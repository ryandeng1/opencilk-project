; RUN: opt -passes=loop-vectorize -force-vector-width=8 -force-vector-interleave=1 -S %s | FileCheck %s --check-prefix=DEFAULT
; RUN: opt -passes=loop-vectorize -force-vector-width=8 -force-vector-interleave=1 -enable-drf-laa -S %s | FileCheck %s --check-prefix=DRF
; RUN: opt -passes=loop-vectorize -enable-drf-laa -S %s | FileCheck %s --check-prefix=COST
; RUN: opt -passes=loop-vectorize -force-vector-width=8 -force-vector-interleave=1 -enable-drf-laa -pass-remarks-analysis=loop-vectorize -pass-remarks=loop-vectorize -disable-output %s 2>&1 | FileCheck %s --check-prefix=REMARK
; RUN: opt -passes=loop-vectorize -force-vector-width=8 -force-vector-interleave=1 -enable-drf-laa -pass-remarks-output=%t.yaml -disable-output %s
; RUN: FileCheck %s --check-prefix=YAML < %t.yaml
; REMARK: DRF rescued vectorization legality by discharging all runtime-check edges for an access with uncomputable bounds
; REMARK: vectorized loop after DRF changed memory legality
; YAML-COUNT-2: Name:            DRFBoundsRescued
; YAML: Function:        indirect_scatter

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Bounds for the indirect source cannot be represented by the runtime pointer
; checker, so ordinary LAA prevents vectorization. DRF-LAA discharges every
; check edge involving that source and allows the remap-shaped loop to be
; vectorized without a runtime overlap check.
; AVX-512 makes the newly legal indirect read visible as a masked gather.
;
; DEFAULT-LABEL: define void @indirect_gather(
; DEFAULT-NOT: vector.body:
; DEFAULT: ret void
;
; DRF-LABEL: define void @indirect_gather(
; DRF-NOT: vector.memcheck:
; DRF: vector.body:
; DRF: call <8 x float> @llvm.masked.gather
; DRF: store <8 x float>
; DRF: middle.block:

define void @indirect_gather(ptr %src, ptr %indices, ptr %dst) #0 {
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

; An indirect destination has the symmetric bounds-construction failure.
; Baseline refuses the loop, while DRF makes it legal without inventing a
; target cost. The forced-width check exposes the scatter shape, and COST uses
; the target model without a forced VF to independently select vectorization.
;
; DEFAULT-LABEL: define void @indirect_scatter(
; DEFAULT-NOT: vector.body:
; DEFAULT: ret void
;
; DRF-LABEL: define void @indirect_scatter(
; DRF-NOT: vector.memcheck:
; DRF: vector.body:
; DRF: call void @llvm.masked.scatter
; DRF: middle.block:
;
; COST-LABEL: define void @indirect_scatter(
; COST: vector.body:
; COST: call void @llvm.masked.scatter
; COST: middle.block:

define void @indirect_scatter(ptr %src, ptr %indices, ptr %dst) #0 {
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


attributes #0 = { "target-features"="+avx,+avx2,+avx512f,+avx512vl" }
!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
