; RUN: opt -passes='loop-mssa(licm)' -disable-licm-promotion -S < %s | FileCheck %s --check-prefix=BASE
; RUN: opt -passes='loop-mssa(licm)' -disable-licm-promotion -enable-drf-memoryssa -S < %s | FileCheck %s --check-prefix=DRF
; RUN: opt -passes='loop-mssa(licm)' -disable-licm-promotion -enable-drf-memoryssa -drf-aa-assumed-min-trip-count=1 -S < %s | FileCheck %s --check-prefix=BASE
; RUN: opt -passes='loop-mssa(licm)' -disable-licm-promotion -enable-drf-memoryssa -pass-remarks=licm -disable-output < %s 2>&1 | FileCheck %s --check-prefix=REMARK
; REMARK-COUNT-2: hoisted load after DRF suppressed a loop-local clobber

target datalayout = "e-p:64:64"

; The invariant context load cannot ordinarily be hoisted across a possibly
; aliasing output store.  On a Tapir-derived loop, aliasing would make the
; invariant load race with the output store in another iteration.  DRF
; MemorySSA therefore exposes the load to LICM.
;
; BASE-LABEL: define void @promote(
; BASE: entry:
; BASE-NEXT: br label %loop
; BASE: loop:
; BASE: %factor = load i32, ptr %ctx
;
; DRF-LABEL: define void @promote(
; DRF: entry:
; DRF-NEXT: %factor = load i32, ptr %ctx
; DRF-NEXT: br label %loop
; DRF: loop:
; DRF-NOT: load i32, ptr %ctx
define void @promote(ptr dereferenceable(4) %ctx, ptr %out, i64 %n) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %loop ]
  %factor = load i32, ptr %ctx, align 4
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  store i32 %factor, ptr %p, align 4
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}


; A loop-invariant guard makes the load uniform across logical iterations. If
; %take is true, every iteration executes the load and an aliasing store races
; with another iteration's load. If it is false, the pointer's explicit
; nonnull/dereferenceable facts make speculation into the preheader safe under
; LICM's ordinary trapping rules.
;
; BASE-LABEL: define void @conditional_load(
; BASE: load.block:
; BASE-NEXT: %factor = load i32, ptr %ctx
;
; DRF-LABEL: define void @conditional_load(
; DRF: entry:
; DRF-NEXT: %factor = load i32, ptr %ctx
; DRF: load.block:
; DRF-NOT: load i32, ptr %ctx
define void @conditional_load(
    ptr nonnull align 4 dereferenceable(4) %ctx, ptr %out, i64 %n, i1 %take) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %merge ]
  br i1 %take, label %load.block, label %skip

load.block:
  %factor = load i32, ptr %ctx, align 4
  br label %merge

skip:
  br label %merge

merge:
  %value = phi i32 [ %factor, %load.block ], [ 0, %skip ]
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  store i32 %value, ptr %p, align 4
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; An iteration-varying guard can execute the load in only one logical
; iteration, so it cannot provide a cross-iteration race witness. DRF must
; leave this load in the conditional block.
;
; DRF-LABEL: define void @variant_conditional_load(
; DRF: load.block:
; DRF-NEXT: %factor = load i32, ptr %ctx
define void @variant_conditional_load(ptr dereferenceable(4) %ctx, ptr %out,
                                      i64 %n) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %merge ]
  %take = icmp eq i64 %i, 0
  br i1 %take, label %load.block, label %skip

load.block:
  %factor = load i32, ptr %ctx, align 4
  br label %merge

skip:
  br label %merge

merge:
  %value = phi i32 [ %factor, %load.block ], [ 0, %skip ]
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  store i32 %value, ptr %p, align 4
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; The global minimum-trip-count contract must not contradict a loop that SCEV
; proves executes only once.
;
; DRF-LABEL: define void @single_iteration(
; DRF: loop:
; DRF: %factor = load i32, ptr %ctx
define void @single_iteration(ptr dereferenceable(4) %ctx, ptr %out) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %loop ]
  %factor = load i32, ptr %ctx, align 4
  %p = getelementptr inbounds i32, ptr %out, i64 %i
  store i32 %factor, ptr %p, align 4
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, 1
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; DRF resolves an uncertain clobber, but it does not override an AA proof that
; the store and invariant load access the same location.
;
; DRF-LABEL: define void @proven_alias(
; DRF: loop:
; DRF: %value = load i32, ptr %ptr
define void @proven_alias(ptr dereferenceable(4) %ptr, i64 %n) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %next, %loop ]
  %value = load i32, ptr %ptr, align 4
  %updated = add i32 %value, 1
  store i32 %updated, ptr %ptr, align 4
  %next = add nuw i64 %i, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
