; RUN: opt -passes='print<access-info>' -disable-output < %s 2>&1 | FileCheck %s --check-prefix=DEFAULT
; RUN: opt -passes='print<access-info>' -disable-output -enable-drf-laa -stats < %s 2>&1 | FileCheck %s --check-prefix=DRF
; RUN: opt -passes='print<access-info>' -disable-output -enable-drf-loop-optimizations < %s 2>&1 | FileCheck %s --check-prefix=UMBRELLA

target datalayout = "e-p:64:64"

@reducer = global i64 0

; The indirect source address has no loop-wide SCEV bounds. Ordinary LAA
; therefore cannot construct the src-vs-dst runtime overlap check. Explicit
; DRF-LAA may omit %src.ptr because every check edge incident to that access is
; a read/write pair with no cross-iteration dependence.
;
; DEFAULT-LABEL: function 'indirect_gather':
; DEFAULT: Report: cannot identify array bounds
;
; DRF-LABEL: function 'indirect_gather':
; DRF: Memory dependences are safe{{$}}
; DRF-NOT: cannot identify array bounds
; DRF: Run-time memory checks:
;
; The umbrella deliberately retains ordinary runtime-check construction.
; UMBRELLA-LABEL: function 'indirect_gather':
; UMBRELLA: Report: cannot identify array bounds

define void @indirect_gather(ptr %src, ptr %indices, ptr %dst) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %index.ptr = getelementptr inbounds i32, ptr %indices, i64 %i
  %index = load i32, ptr %index.ptr, align 4
  %index.ext = sext i32 %index to i64
  %src.ptr = getelementptr inbounds float, ptr %src, i64 %index.ext
  %value = load float, ptr %src.ptr, align 4
  %dst.ptr = getelementptr inbounds float, ptr %dst, i64 %i
  store float %value, ptr %dst.ptr, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; The same rescue must work when the uncomputable access is the destination.
; In addition to rescuing runtime-check construction, DRF classifies the
; indirect store's otherwise-unsafe loop-carried dependences explicitly as
; NoCrossIteration.
;
; DEFAULT-LABEL: function 'indirect_scatter':
; DEFAULT: Report: cannot identify array bounds
;
; DRF-LABEL: function 'indirect_scatter':
; DRF: Memory dependences are safe{{$}}
; DRF: Dependences:
; DRF: NoCrossIteration:
; DRF-NOT: cannot identify array bounds
; DRF: Run-time memory checks:

define void @indirect_scatter(ptr %src, ptr %indices, ptr %dst) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %src.ptr = getelementptr inbounds float, ptr %src, i64 %i
  %value = load float, ptr %src.ptr, align 4
  %index.ptr = getelementptr inbounds i32, ptr %indices, i64 %i
  %index = load i32, ptr %index.ptr, align 4
  %index.ext = sext i32 %index to i64
  %dst.ptr = getelementptr inbounds float, ptr %dst, i64 %index.ext
  %old = load float, ptr %dst.ptr, align 4
  %updated = fadd float %old, %value
  store float %updated, ptr %dst.ptr, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; A single uncovered incident edge must prevent the rescue. The hyperobject
; view is runtime-managed reduction state, so the store through %view.ptr is
; not an ordinary shared-memory access covered by NoCrossIteration.
;
; DRF-LABEL: function 'mixed_uncovered_partner':
; DRF: Report: cannot identify array bounds

define void @mixed_uncovered_partner(ptr %src, ptr %indices, ptr %dst) {
entry:
  %view = call ptr @llvm.hyper.lookup.2.i64(
      ptr @reducer, i64 8, ptr @identity, ptr @reduce)
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %index.ptr = getelementptr inbounds i32, ptr %indices, i64 %i
  %index = load i32, ptr %index.ptr, align 4
  %index.ext = sext i32 %index to i64
  %src.ptr = getelementptr inbounds float, ptr %src, i64 %index.ext
  %value = load float, ptr %src.ptr, align 4
  %dst.ptr = getelementptr inbounds float, ptr %dst, i64 %i
  store float %value, ptr %dst.ptr, align 4
  %view.ptr = getelementptr inbounds float, ptr %view, i64 %i
  store float %value, ptr %view.ptr, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !2

exit:
  ret void
}

; Without Tapir provenance, the same ordinary instruction pair is not covered
; by the DRF loop contract.
;
; DRF-LABEL: function 'serial_indirect_gather':
; DRF: Report: cannot identify array bounds

define void @serial_indirect_gather(ptr %src, ptr %indices, ptr %dst) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %index.ptr = getelementptr inbounds i32, ptr %indices, i64 %i
  %index = load i32, ptr %index.ptr, align 4
  %index.ext = sext i32 %index to i64
  %src.ptr = getelementptr inbounds float, ptr %src, i64 %index.ext
  %value = load float, ptr %src.ptr, align 4
  %dst.ptr = getelementptr inbounds float, ptr %dst, i64 %i
  store float %value, ptr %dst.ptr, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop

exit:
  ret void
}

; Only @indirect_gather and @indirect_scatter reach the DRF rescue.
; DRF-DAG: 2 loop-accesses - Number of LAA alias-set bounds failures rescued by DRF
; DRF-DAG: 2 loop-accesses - Number of uncomputable LAA accesses discharged by DRF

declare ptr @llvm.hyper.lookup.2.i64(ptr, i64, ptr, ptr)
declare void @identity(ptr)
declare void @reduce(ptr, ptr)

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
!2 = distinct !{!2, !1}
