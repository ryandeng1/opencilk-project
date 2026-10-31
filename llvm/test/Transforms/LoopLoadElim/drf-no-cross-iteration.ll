; RUN: opt -passes=loop-load-elim -S %s | FileCheck %s --check-prefix=DEFAULT
; RUN: opt -passes=loop-load-elim -enable-drf-laa -S %s | FileCheck %s --check-prefix=DRF

; The store to a[i+1] and the load of a[i] are a proven forward dependence.
; Ordinary analysis forwards the value after versioning the loop.  This input
; violates the strict DRF contract, which classifies the pair as
; NoCrossIteration.  That result carries no value relationship, so LLE must not
; use it as a forwarding candidate.
;
; DEFAULT-LABEL: define void @proven_forward_is_forwarded(
; DEFAULT: lver.check
; DEFAULT: %load_initial = load i32, ptr %a
; DEFAULT: %store_forwarded = phi i32
; DEFAULT: %twice = shl i32 %store_forwarded, 1
;
; DRF-LABEL: define void @proven_forward_is_forwarded(
; DRF-NOT: lver
; DRF-NOT: load_initial
; DRF: %current = load i32, ptr %a.current
; DRF: %twice = shl i32 %current, 1
; DRF-NOT: lver
define void @proven_forward_is_forwarded(ptr %a, ptr %b, ptr %c) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %next.i = add nuw nsw i64 %i, 1
  %a.next = getelementptr inbounds i32, ptr %a, i64 %next.i
  %pb = getelementptr inbounds i32, ptr %b, i64 %i
  %value = load i32, ptr %pb, align 4
  %plus = add i32 %value, 2
  store i32 %plus, ptr %a.next, align 4

  %a.current = getelementptr inbounds i32, ptr %a, i64 %i
  %current = load i32, ptr %a.current, align 4
  %twice = shl i32 %current, 1
  %pc = getelementptr inbounds i32, ptr %c, i64 %i
  store i32 %twice, ptr %pc, align 4

  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 100
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; A NoCrossIteration result carries no value relationship.  Here the only
; store/load pairs have unknown pointer relations, which DRF classifies as
; NoCrossIteration; that must not create a forwarding candidate, so the load
; of a[i] stays.
;
; DRF-LABEL: define void @unknown_pair_is_not_forwarding(
; DRF-NOT: load_initial
; DRF: %current = load i32, ptr %a.current
; DRF: %twice = shl i32 %current, 1
define void @unknown_pair_is_not_forwarding(ptr %a, ptr %b, ptr %c) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %next.i = add nuw nsw i64 %i, 1
  %b.next = getelementptr inbounds i32, ptr %b, i64 %next.i
  %val = trunc i64 %i to i32
  store i32 %val, ptr %b.next, align 4

  %a.current = getelementptr inbounds i32, ptr %a, i64 %i
  %current = load i32, ptr %a.current, align 4
  %twice = shl i32 %current, 1
  %pc = getelementptr inbounds i32, ptr %c, i64 %i
  store i32 %twice, ptr %pc, align 4

  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 100
  br i1 %done, label %exit, label %loop, !llvm.loop !2

exit:
  ret void
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
!2 = distinct !{!2, !1}
