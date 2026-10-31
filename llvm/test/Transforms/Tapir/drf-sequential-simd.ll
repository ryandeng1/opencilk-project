; RUN: opt -passes='default<O3>' -S < %s | FileCheck %s --check-prefix=BASE
; RUN: opt -passes='default<O3>' -enable-drf-loop-optimizations -S < %s | FileCheck %s --check-prefix=DRF

target datalayout = "e-p:64:64-i64:64-n32:64-S128"

; The ordinary pipeline retains both levels of nested Tapir scheduling.  DRF
; sequential-SIMD mode serializes only the small inner cilk_for, keeps the
; outer detach, and records provenance on the resulting serial loop.
;
; BASE-LABEL: define void @nested(
; BASE: detach within %outer
; BASE: detach within %inner
;
; DRF-LABEL: define void @nested(
; DRF: detach within %outer
; DRF-NOT: detach within %inner
; DRF: reattach within %outer
; DRF-NOT: detach within
; DRF: !{!"llvm.loop.fromtapirloop"}
define void @nested() {
entry:
  %outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i32 [ 0, %entry ], [ %inc.i, %outer.inc ]
  detach within %outer, label %outer.body, label %outer.inc

outer.body:
  %inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %j = phi i32 [ 0, %outer.body ], [ %inc.j, %inner.inc ]
  detach within %inner, label %inner.body, label %inner.inc

inner.body:
  call void @use(i32 %i, i32 %j)
  reattach within %inner, label %inner.inc

inner.inc:
  %inc.j = add nuw nsw i32 %j, 1
  %inner.done = icmp eq i32 %inc.j, 32
  br i1 %inner.done, label %inner.cleanup, label %inner.header, !llvm.loop !0

inner.cleanup:
  sync within %inner, label %inner.synced

inner.synced:
  call void @llvm.sync.unwind(token %inner)
  reattach within %outer, label %outer.inc

outer.inc:
  %inc.i = add nuw nsw i32 %i, 1
  %outer.done = icmp eq i32 %inc.i, 8
  br i1 %outer.done, label %outer.cleanup, label %outer.header, !llvm.loop !0

outer.cleanup:
  sync within %outer, label %exit

exit:
  call void @llvm.sync.unwind(token %outer)
  ret void
}

declare token @llvm.syncregion.start()
declare void @llvm.sync.unwind(token)
declare void @use(i32, i32)

!0 = distinct !{!0, !1, !2}
!1 = !{!"tapir.loop.spawn.strategy", i32 1}
!2 = !{!"llvm.loop.unroll.disable"}
