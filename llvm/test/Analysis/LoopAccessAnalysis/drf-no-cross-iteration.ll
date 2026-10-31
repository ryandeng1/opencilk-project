; RUN: opt -passes='print<access-info>' -disable-output < %s 2>&1 | FileCheck %s --check-prefix=DEFAULT
; RUN: opt -passes='print<access-info>' -disable-output -enable-drf-laa < %s 2>&1 | FileCheck %s --check-prefix=DRF
; RUN: opt -passes='print<access-info>' -disable-output -enable-drf-loop-optimizations < %s 2>&1 | FileCheck %s --check-prefix=UMBRELLA
; RUN: opt -passes='print<access-info>' -disable-output -enable-drf-aa -enable-drf-laa < %s 2>&1 | FileCheck %s --check-prefix=BOTH

target datalayout = "e-p:64:64"

@reducer = global i64 0

; DEFAULT-LABEL: function 'tapir_derived_copy':
; DEFAULT: Memory dependences are safe with run-time checks
; DEFAULT: Run-time memory checks:
; DEFAULT: Check 0:
;
; DRF-LABEL: function 'tapir_derived_copy':
; DRF: Memory dependences are safe{{$}}
; DRF: Dependences:
; DRF-NEXT: Run-time memory checks:
; DRF-NEXT: Grouped accesses:
;
; The performance-oriented umbrella keeps ordinary LAA versioning while using
; NoCrossIteration for dependence legality. The explicit -enable-drf-laa flag
; above opts into broad check removal.
; UMBRELLA-LABEL: function 'tapir_derived_copy':
; UMBRELLA: Memory dependences are safe with run-time checks
; UMBRELLA: NoCrossIteration:
; UMBRELLA: Check 0:
;
; DRFAA participates in the cross-iteration alias-set construction before the
; dependence checker.  When it proves this pair independent, no dependence
; candidate remains for the Tapir fallback to classify as NoCrossIteration.
;
; BOTH-LABEL: function 'tapir_derived_copy':
; BOTH: Memory dependences are safe
; BOTH: Dependences:
; BOTH-NEXT: Run-time memory checks:
define void @tapir_derived_copy(ptr %a, ptr %b) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %pa = getelementptr inbounds i32, ptr %a, i64 %i
  %value = load i32, ptr %pa, align 4
  %pb = getelementptr inbounds i32, ptr %b, i64 %i
  store i32 %value, ptr %pb, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; A same-base, statically analyzable pair: ordinary LAA proves a forward
; dependence from %ahead to %current.  This input violates the strict DRF
; contract.  With -enable-drf-laa, the contract is authoritative and the pair
; is classified as having no cross-iteration dependence.
;
; DEFAULT-LABEL: function 'tapir_derived_static_dependence':
; DEFAULT: Memory dependences are safe
; DEFAULT: Dependences:
; DEFAULT: Forward:
;
; DRF-LABEL: function 'tapir_derived_static_dependence':
; DRF: Memory dependences are safe
; DRF: Dependences:
; DRF: NoCrossIteration:
; DRF: Run-time memory checks:
define void @tapir_derived_static_dependence(
    ptr noalias %a, ptr noalias %b, ptr noalias %c) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %ahead.i = add nuw nsw i64 %i, 8
  %pb = getelementptr inbounds i32, ptr %b, i64 %i
  %value = load i32, ptr %pb, align 4
  %plus = add i32 %value, 2
  %ahead = getelementptr inbounds i32, ptr %a, i64 %ahead.i
  store i32 %plus, ptr %ahead, align 4
  %current = getelementptr inbounds i32, ptr %a, i64 %i
  %old = load i32, ptr %current, align 4
  %twice = shl i32 %old, 1
  %pc = getelementptr inbounds i32, ptr %c, i64 %i
  store i32 %twice, ptr %pc, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !4

exit:
  ret void
}

; -enable-drf-laa must not affect an ordinary serial loop.
;
; DRF-LABEL: function 'serial_copy':
; DRF: Memory dependences are safe with run-time checks
; DRF: Dependences:
; DRF-NOT: NoCrossIteration:
; DRF: Run-time memory checks:
; DRF: Check 0:
define void @serial_copy(ptr %a, ptr %b) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %pa = getelementptr inbounds i32, ptr %a, i64 %i
  %value = load i32, ptr %pa, align 4
  %pb = getelementptr inbounds i32, ptr %b, i64 %i
  store i32 %value, ptr %pb, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop

exit:
  ret void
}

; Volatile and atomic accesses are not covered by the new dependence kind.
; In particular, recognizing the loop as Tapir-derived must not make it behave
; like an llvm.loop.parallel_accesses annotation.
;
; DRF-LABEL: function 'tapir_derived_volatile':
; DRF: Report: read with atomic ordering or volatile read
; DRF-NOT: Memory dependences are safe
define void @tapir_derived_volatile(ptr %a, ptr %b) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %pa = getelementptr inbounds i32, ptr %a, i64 %i
  %value = load volatile i32, ptr %pa, align 4
  %pb = getelementptr inbounds i32, ptr %b, i64 %i
  store volatile i32 %value, ptr %pb, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !2

exit:
  ret void
}

; Hyperobject views are runtime-managed reduction state, not ordinary shared
; memory.  Parallel iterations may intentionally update different views, so
; DRF cannot classify accesses through %view as NoCrossIteration.
;
; DRF-LABEL: function 'tapir_derived_hyperobject':
; DRF: Memory dependences are safe with run-time checks
; DRF: Dependences:
; DRF-NOT: NoCrossIteration:
; DRF: Run-time memory checks:
; DRF: Check 0:
; DRF: Non vectorizable stores to invariant address were found in loop.
define void @tapir_derived_hyperobject(ptr %a) {
entry:
  %view = call ptr @llvm.hyper.lookup.2.i64(
      ptr @reducer, i64 8, ptr @identity, ptr @reduce)
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %pa = getelementptr inbounds i64, ptr %a, i64 %i
  %value = load i64, ptr %pa, align 8
  %old = load i64, ptr %view, align 8
  %sum = add i64 %old, %value
  store i64 %sum, ptr %view, align 8
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !3

exit:
  ret void
}

; A proven backward dependence (a[i] = a[i-1] + 1) violates the strict DRF
; contract.  Without the flag, ordinary LAA reports the recurrence.  With the
; flag, the contract is authoritative and directly yields NoCrossIteration.
;
; DEFAULT-LABEL: function 'tapir_derived_recurrence':
; DEFAULT: Report: unsafe dependent memory operations
; DEFAULT: Backward:
;
; DRF-LABEL: function 'tapir_derived_recurrence':
; DRF: Memory dependences are safe
; DRF: Dependences:
; DRF: NoCrossIteration:
; DRF: Run-time memory checks:
define void @tapir_derived_recurrence(ptr %a) {
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
  br i1 %done, label %exit, label %loop, !llvm.loop !5

exit:
  ret void
}

; A read-modify-write through a pointer loaded inside the loop cannot be
; analyzed by SCEV, so ordinary LAA is uncertain (IndirectUnsafe).
; Uncertainty is exactly what the DRF contract may resolve: a cross-iteration
; overlap of the pointees would be a race.
;
; DEFAULT-LABEL: function 'tapir_derived_indirect':
; DEFAULT: Report: unsafe dependent memory operations
; DEFAULT: IndirectUnsafe:
;
; DRF-LABEL: function 'tapir_derived_indirect':
; DRF: Memory dependences are safe
; DRF: Dependences:
; DRF: NoCrossIteration:
define void @tapir_derived_indirect(ptr noalias %ptrs) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %gep = getelementptr inbounds ptr, ptr %ptrs, i64 %i
  %p = load ptr, ptr %gep, align 8
  %v = load i64, ptr %p, align 8
  %v.inc = add i64 %v, 1
  store i64 %v.inc, ptr %p, align 8
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !6

exit:
  ret void
}

declare ptr @llvm.hyper.lookup.2.i64(ptr, i64, ptr, ptr)
declare void @identity(ptr)
declare void @reduce(ptr, ptr)

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
!2 = distinct !{!2, !1}
!3 = distinct !{!3, !1}
!4 = distinct !{!4, !1}
!5 = distinct !{!5, !1}
!6 = distinct !{!6, !1}
