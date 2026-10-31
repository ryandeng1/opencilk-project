; RUN: opt -passes=gvn -S < %s | FileCheck %s --check-prefix=BASE
; RUN: opt -passes=gvn -enable-drf-memdep -S < %s | FileCheck %s --check-prefix=DRF
; RUN: opt -passes=gvn -enable-drf-memdep -drf-aa-assumed-min-trip-count=1 -S < %s | FileCheck %s --check-prefix=BASE

target datalayout = "e-p:64:64"

; The store may alias %ctx according to ordinary AA, so baseline MemDep cannot
; connect %after to %before. In a logically parallel loop, the invariant load
; executes on every iteration; if the store aliased it, it would conflict with
; the load in another iteration. The loop-scoped DRF MemDep rule lets GVN look
; through the MayAlias store and eliminate the repeated load.
;
; BASE-LABEL: define i32 @unconditional(
; BASE: %after = load i32, ptr %ctx
;
; DRF-LABEL: define i32 @unconditional(
; DRF: %[[BEFORE:before[^ ]*]] = load i32, ptr %ctx
; DRF-NOT: %after = load i32, ptr %ctx
; DRF: %sum = add i32 %[[BEFORE]], %[[BEFORE]]
define i32 @unconditional(ptr dereferenceable(4) %ctx, ptr %out, i64 %n) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %loop ]
  %before = load i32, ptr %ctx, align 4
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  %stored = add i32 %before, 1
  store i32 %stored, ptr %p, align 4
  %after = load i32, ptr %ctx, align 4
  %sum = add i32 %before, %after
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  %result = phi i32 [ %sum, %loop ]
  ret i32 %result
}

; A load in a conditional block does not execute in every logical iteration.
; A conditional store may therefore alias it without supplying the required
; cross-iteration race witness. Query-specific cache handling is important
; here: this load has the same invariant address shape as @unconditional, but
; it must not reuse that proof.
;
; DRF-LABEL: define i32 @conditional(
; DRF: load.block:
; DRF: %before = load i32, ptr %ctx
; DRF: store i32 %stored, ptr %p
; DRF: %after = load i32, ptr %ctx
define i32 @conditional(ptr dereferenceable(4) %ctx, ptr %out, i64 %n,
                        i1 %take) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %latch ]
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  br i1 %take, label %load.block, label %skip

load.block:
  %before = load i32, ptr %ctx, align 4
  %stored = add i32 %before, 1
  store i32 %stored, ptr %p, align 4
  %after = load i32, ptr %ctx, align 4
  %sum = add i32 %before, %after
  br label %latch

skip:
  br label %latch

latch:
  %value = phi i32 [ %sum, %load.block ], [ 0, %skip ]
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !2

exit:
  %result = phi i32 [ %value, %latch ]
  ret i32 %result
}

; A statically single-iteration loop overrides the global minimum-trip-count
; contract, so DRF cannot supply a different-iteration witness.
;
; DRF-LABEL: define i32 @single_iteration(
; DRF: %after = load i32, ptr %ctx
define i32 @single_iteration(ptr dereferenceable(4) %ctx, ptr %out) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %loop ]
  %before = load i32, ptr %ctx, align 4
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  %stored = add i32 %before, 1
  store i32 %stored, ptr %p, align 4
  %after = load i32, ptr %ctx, align 4
  %sum = add i32 %before, %after
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, 1
  br i1 %done, label %exit, label %loop, !llvm.loop !3

exit:
  %result = phi i32 [ %sum, %loop ]
  ret i32 %result
}

; Loop spawning can rebind storage that was private to each source-level Tapir
; iteration to one alloca reused by a serialized chunk loop.  The alloca then
; appears invariant in the derived loop even though its source-level dynamic
; object was not shared between logical iterations.  DRF must not skip the
; variable-offset copy stores when resolving the later invariant load.
;
; This is the reduced shape of Rodinia LUD after its BS=16 copy loop and GEMM
; are vectorized.  Skipping the stores makes GVN replace %value with undef.
;
; BASE-LABEL: define void @derived_task_private_alloca(
; BASE: use:
; BASE-NEXT: %value = load <16 x float>, ptr %tmp
; BASE: store <16 x float> %value, ptr %out
;
; DRF-LABEL: define void @derived_task_private_alloca(
; DRF: use:
; DRF-NEXT: %value = load <16 x float>, ptr %tmp
; DRF: store <16 x float> %value, ptr %out
define void @derived_task_private_alloca(ptr %src, ptr %out, i64 %n) {
entry:
  %tmp = alloca [256 x float], align 64
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %latch ]
  call void @llvm.lifetime.start.p0(i64 1024, ptr nonnull %tmp)
  br label %copy

copy:
  %j = phi i64 [ 0, %loop ], [ %j.next, %copy ]
  %offset = shl nuw nsw i64 %j, 3
  %src.ptr = getelementptr inbounds float, ptr %src, i64 %offset
  %copied = load <8 x float>, ptr %src.ptr, align 4
  %tmp.ptr = getelementptr inbounds [256 x float], ptr %tmp, i64 0,
                                     i64 %offset
  store <8 x float> %copied, ptr %tmp.ptr, align 32
  %j.next = add nuw nsw i64 %j, 1
  %copy.done = icmp eq i64 %j.next, 32
  br i1 %copy.done, label %use, label %copy

use:
  %value = load <16 x float>, ptr %tmp, align 64
  store <16 x float> %value, ptr %out, align 4
  call void @llvm.lifetime.end.p0(i64 1024, ptr nonnull %tmp)
  br label %latch

latch:
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

declare void @llvm.lifetime.start.p0(i64 immarg, ptr captures(none))
declare void @llvm.lifetime.end.p0(i64 immarg, ptr captures(none))

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
!2 = distinct !{!2, !1}
!3 = distinct !{!3, !1}
