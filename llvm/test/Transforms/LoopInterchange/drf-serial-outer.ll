; RUN: opt -passes=loop-interchange -pass-remarks-missed=loop-interchange -pass-remarks=loop-interchange -S < %s 2>&1 | FileCheck %s --check-prefix=BASE
; RUN: opt -passes=loop-interchange -pass-remarks-missed=loop-interchange -pass-remarks=loop-interchange -enable-drf-da -S < %s 2>&1 | FileCheck %s --check-prefix=DRF
; RUN: opt -passes=loop-interchange -pass-remarks-missed=loop-interchange -pass-remarks=loop-interchange -enable-drf-da -drf-da-require-eq-prefix=false -S < %s 2>&1 | FileCheck %s --check-prefix=UNGUARDED

target datalayout = "e-m:e-p:64:64-i64:64-n32:64-S128"

; A serial t loop encloses a Tapir-derived j loop.  Every j iteration writes
; A[j][t+1] and reads A[j+1][t], so the j loop is race-free, but the store at
; (t, j) feeds the load at (t+1, j-1): direction (<, >), which interchange
; would turn into the negative (>, <).  The DRF NoCrossIteration fact for j
; covers only pairs within one dynamic instance of the j loop; with the
; -drf-da-require-eq-prefix guard (default on) DependenceAnalysis keeps the
; real vector and interchange refuses.  The unguarded rewrite to (<, =) is
; unsound and interchanges the nest; it is checked only to document what the
; option switches off.
;
; BASE: Cannot interchange loops due to dependences.
; BASE-NOT: Loop interchanged
;
; DRF: Cannot interchange loops due to dependences.
; DRF-NOT: Loop interchanged
;
; UNGUARDED: Loop interchanged with enclosing loop.
define void @serial_outer_carries(ptr noalias %A) {
entry:
  br label %t.header

t.header:
  %t = phi i64 [ 0, %entry ], [ %t.inc, %t.latch ]
  %t1 = add nuw nsw i64 %t, 1
  br label %j.header

j.header:
  %j = phi i64 [ 0, %t.header ], [ %j.inc, %j.header ]
  %j1 = add nuw nsw i64 %j, 1
  %ld.p = getelementptr inbounds [64 x [64 x i32]], ptr %A, i64 0, i64 %j1, i64 %t
  %v = load i32, ptr %ld.p, align 4
  %v1 = add i32 %v, 1
  %st.p = getelementptr inbounds [64 x [64 x i32]], ptr %A, i64 0, i64 %j, i64 %t1
  store i32 %v1, ptr %st.p, align 4
  %j.inc = add nuw nsw i64 %j, 1
  %j.done = icmp eq i64 %j.inc, 32
  br i1 %j.done, label %t.latch, label %j.header, !llvm.loop !0

t.latch:
  %t.inc = add nuw nsw i64 %t, 1
  %t.done = icmp eq i64 %t.inc, 32
  br i1 %t.done, label %exit, label %t.header

exit:
  ret void
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
