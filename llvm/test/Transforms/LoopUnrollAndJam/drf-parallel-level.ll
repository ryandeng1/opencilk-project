; RUN: opt -passes=loop-unroll-and-jam -allow-unroll-and-jam=true -unroll-and-jam-count=2 -unroll-remainder -S < %s | FileCheck %s --check-prefix=BASE
; RUN: opt -passes=loop-unroll-and-jam -allow-unroll-and-jam=true -unroll-and-jam-count=2 -unroll-remainder -enable-drf-da -S < %s | FileCheck %s --check-prefix=DRF
; RUN: opt -passes='default<O3>' -enable-unroll-and-jam -debug-pass-manager -disable-output < %s 2>&1 | FileCheck %s --check-prefix=PIPE
; RUN: opt -passes='default<O3>' -enable-unroll-and-jam -enable-drf-da -debug-pass-manager -disable-output < %s 2>&1 | FileCheck %s --check-prefix=PIPE

; PIPE: Running pass: LoopUnrollAndJamPass

target datalayout = "e-m:e-p:64:64-i64:64-n32:64-S128"

; Both runs explicitly request the same unroll-and-jam transform and count.
; Without noalias, ordinary DA cannot prove that A[i] and the B[j] loads are
; independent.  The DRF DA summary makes the outer Tapir-derived level EQ.
;
; BASE-LABEL: define void @register_block(
; BASE: for.inner:
; BASE: %j = phi
; BASE-NOT: %j.1 = phi
;
; DRF-LABEL: define void @register_block(
; DRF: for.inner:
; DRF: %j = phi
; DRF: %j.1 = phi
define void @register_block(i32 %I, i32 %J, ptr %A, ptr %B) {
entry:
  %has.i = icmp ne i32 %I, 0
  %has.j = icmp ne i32 %J, 0
  %run = and i1 %has.i, %has.j
  br i1 %run, label %for.outer, label %exit

for.outer:
  %i = phi i32 [ 0, %entry ], [ %inc.i, %for.latch ]
  br label %for.inner

for.inner:
  %j = phi i32 [ 0, %for.outer ], [ %inc.j, %for.inner ]
  %sum = phi i32 [ 0, %for.outer ], [ %next.sum, %for.inner ]
  %pb = getelementptr inbounds i32, ptr %B, i32 %j
  %value = load i32, ptr %pb, align 4
  %next.sum = add i32 %sum, %value
  %inc.j = add nuw i32 %j, 1
  %inner.done = icmp eq i32 %inc.j, %J
  br i1 %inner.done, label %for.latch, label %for.inner

for.latch:
  %result = phi i32 [ %next.sum, %for.inner ]
  %pa = getelementptr inbounds i32, ptr %A, i32 %i
  store i32 %result, ptr %pa, align 4
  %inc.i = add nuw i32 %i, 1
  %outer.done = icmp eq i32 %inc.i, %I
  br i1 %outer.done, label %exit, label %for.outer, !llvm.loop !0

exit:
  ret void
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}

; A serial loop can enclose multiple dynamic instances of the DRF loop.  The
; global direction vector must retain dependences between those instances, but
; UAJ of the DRF loop itself only reschedules iterations within one instance.
;
; BASE-LABEL: define void @nested_register_block(
; BASE: for.inner.nested:
; BASE: %j = phi
; BASE-NOT: %j.1 = phi
;
; DRF-LABEL: define void @nested_register_block(
; DRF: for.inner.nested:
; DRF: %j = phi
; DRF: %j.1 = phi
define void @nested_register_block(i32 %T, i32 %I, i32 %J, ptr %A, ptr %B) {
entry:
  %has.t = icmp ne i32 %T, 0
  %has.i = icmp ne i32 %I, 0
  %has.j = icmp ne i32 %J, 0
  %has.ti = and i1 %has.t, %has.i
  %run = and i1 %has.ti, %has.j
  br i1 %run, label %for.serial, label %exit

for.serial:
  %t = phi i32 [ 0, %entry ], [ %inc.t, %serial.latch ]
  br label %for.outer.nested

for.outer.nested:
  %i = phi i32 [ 0, %for.serial ], [ %inc.i, %for.latch.nested ]
  br label %for.inner.nested

for.inner.nested:
  %j = phi i32 [ 0, %for.outer.nested ], [ %inc.j, %for.inner.nested ]
  %sum = phi i32 [ 0, %for.outer.nested ], [ %next.sum, %for.inner.nested ]
  %pb = getelementptr inbounds i32, ptr %B, i32 %j
  %value = load i32, ptr %pb, align 4
  %next.sum = add i32 %sum, %value
  %inc.j = add nuw i32 %j, 1
  %inner.done = icmp eq i32 %inc.j, %J
  br i1 %inner.done, label %for.latch.nested, label %for.inner.nested

for.latch.nested:
  %result = phi i32 [ %next.sum, %for.inner.nested ]
  %pa = getelementptr inbounds i32, ptr %A, i32 %i
  store i32 %result, ptr %pa, align 4
  %inc.i = add nuw i32 %i, 1
  %outer.done = icmp eq i32 %inc.i, %I
  br i1 %outer.done, label %serial.latch, label %for.outer.nested, !llvm.loop !0

serial.latch:
  %inc.t = add nuw i32 %t, 1
  %serial.done = icmp eq i32 %inc.t, %T
  br i1 %serial.done, label %exit, label %for.serial

exit:
  ret void
}
