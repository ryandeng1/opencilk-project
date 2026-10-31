; RUN: opt -passes=loop-vectorize -force-vector-width=4 -force-vector-interleave=1 -S %s | FileCheck %s --check-prefix=DEFAULT
; RUN: opt -passes=loop-vectorize -force-vector-width=4 -force-vector-interleave=1 -enable-drf-laa -S %s | FileCheck %s --check-prefix=DRF
; RUN: opt -passes=loop-vectorize -force-vector-width=4 -force-vector-interleave=1 -enable-drf-aa -enable-drf-laa -S %s | FileCheck %s --check-prefix=DRF

; RUN: opt -passes=loop-vectorize -force-vector-width=4 -force-vector-interleave=1 -enable-drf-laa -pass-remarks-analysis=loop-vectorize -disable-output %s 2>&1 | FileCheck %s --check-prefix=REMARK
; REMARK: DRF eliminated {{[0-9]+}} grouped runtime pointer check(s)
; REMARK: DRF classified {{[0-9]+}} memory dependence(s) as NoCrossIteration
target datalayout = "e-p:64:64"
target triple = "x86_64-unknown-linux-gnu"

; If %a == %b, the store and load alias in the same iteration and the load must
; observe 7.  DRF rules out only shifted, cross-iteration conflicts.  The DRF
; vector loop therefore keeps the store before the load, but needs neither a
; runtime overlap check nor noalias metadata.
;
; DEFAULT-LABEL: define void @same_iteration_alias(
; DEFAULT: vector.memcheck:
;
; DRF-LABEL: define void @same_iteration_alias(
; DRF-NOT: vector.memcheck:
; DRF: vector.body:
; DRF-NOT: !alias.scope
; DRF: store <4 x i32> splat (i32 7), ptr
; DRF-NOT: !alias.scope
; DRF: %wide.load = load <4 x i32>, ptr
; DRF-NOT: !alias.scope
; DRF: middle.block:
define void @same_iteration_alias(ptr %a, ptr %b, ptr noalias %out) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %pa = getelementptr inbounds i32, ptr %a, i64 %i
  store i32 7, ptr %pa, align 4
  %pb = getelementptr inbounds i32, ptr %b, i64 %i
  %value = load i32, ptr %pb, align 4
  %pout = getelementptr inbounds i32, ptr %out, i64 %i
  store i32 %value, ptr %pout, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; A proven backward dependence (a[i] = a[i-1] + 1) is rejected by ordinary
; LAA.  The input violates the strict DRF contract, so behavior under
; -enable-drf-laa is unconstrained; the contract directly licenses
; cross-iteration reordering and the loop vectorizes.
;
; DEFAULT-LABEL: define void @proven_recurrence(
; DEFAULT-NOT: vector.body:
; DEFAULT: ret void
;
; DRF-LABEL: define void @proven_recurrence(
; DRF: vector.body:
; DRF: %wide.load = load <4 x i32>, ptr
; DRF: store <4 x i32>
; DRF: middle.block:
define void @proven_recurrence(ptr %a) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 1, %entry ], [ %inc, %loop ]
  %im1 = add nsw i64 %i, -1
  %pprev = getelementptr inbounds i32, ptr %a, i64 %im1
  %prev = load i32, ptr %pprev, align 4
  %next = add nsw i32 %prev, 1
  %pcur = getelementptr inbounds i32, ptr %a, i64 %i
  store i32 %next, ptr %pcur, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !3

exit:
  ret void
}

!0 = distinct !{!0, !1, !2}
!1 = !{!"llvm.loop.fromtapirloop"}
!2 = !{!"llvm.loop.vectorize.enable", i1 true}
!3 = distinct !{!3, !1, !2}
