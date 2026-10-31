; RUN: opt -passes='print<da>' -disable-output < %s 2>&1 | FileCheck %s --check-prefix=BASE
; RUN: opt -passes='print<da>' -disable-output -enable-drf-da < %s 2>&1 | FileCheck %s --check-prefix=DRF
; RUN: opt -passes='print<da>' -disable-output -enable-drf-loop-optimizations < %s 2>&1 | FileCheck %s --check-prefix=DRF

target datalayout = "e-p:64:64"

; DRF refines only the direction at a Tapir-derived loop level.  A confused
; ordinary result becomes EQ-or-loop-independent instead of losing all
; same-iteration ordering information.
;
; BASE-LABEL: function 'tapir_derived_copy':
; BASE: Src:  %value = load i32, ptr %pa, align 4 --> Dst:  store i32 %value, ptr %pb, align 4
; BASE-NEXT: da analyze - confused!
; DRF-LABEL: function 'tapir_derived_copy':
; DRF: Src:  %value = load i32, ptr %pa, align 4 --> Dst:  store i32 %value, ptr %pb, align 4
; DRF-NEXT: da analyze - anti [0|<]!
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

; A direction that ordinary DA can calculate is overwritten only at the
; parallel level.  Under the user-selected DRF contract, the nonzero distance
; is a contradiction and cannot be carried by this loop.
;
; BASE-LABEL: function 'tapir_derived_static_dependence':
; BASE: da analyze - consistent flow [8]!
; DRF-LABEL: function 'tapir_derived_static_dependence':
; DRF: da analyze - flow [0|<]!
define void @tapir_derived_static_dependence(ptr noalias %a) {
entry:
  br label %loop

loop:
  %i = phi i64 [ 0, %entry ], [ %inc, %loop ]
  %ahead.i = add nuw nsw i64 %i, 8
  %ahead = getelementptr inbounds i32, ptr %a, i64 %ahead.i
  store i32 1, ptr %ahead, align 4
  %current = getelementptr inbounds i32, ptr %a, i64 %i
  %old = load i32, ptr %current, align 4
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, 1024
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

; DRF-LABEL: function 'serial_copy':
; DRF: Src:  %value = load i32, ptr %pa, align 4 --> Dst:  store i32 %value, ptr %pb, align 4
; DRF-NEXT: da analyze - confused!
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

; Atomics and volatile accesses remain outside the DRF classifier.
;
; DRF-LABEL: function 'tapir_derived_volatile':
; DRF: Src:  %value = load volatile i32, ptr %pa, align 4 --> Dst:  store volatile i32 %value, ptr %pb, align 4
; DRF-NEXT: da analyze - confused!
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
  br i1 %done, label %exit, label %loop, !llvm.loop !0

exit:
  ret void
}

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}

; A serial loop enclosing the Tapir-derived loop.  Each j iteration writes
; A[j][t+1] and reads A[j+1][t], so the j loop is race-free, but the store at
; (t, j) feeds the load at (t+1, j-1): a real dependence carried by the serial
; t level whose j direction is not EQ.  The NoCrossIteration fact only covers
; pairs in the same dynamic instance of the j loop, so with the guard
; (-drf-da-require-eq-prefix, default on) the vector is left alone.  The
; unguarded rewrite to distance 0 at j is unsound; it is checked here only to
; document what the option switches off.
;
; RUN: opt -passes='print<da>' -disable-output -enable-drf-da -drf-da-require-eq-prefix=false < %s 2>&1 | FileCheck %s --check-prefix=UNGUARDED
;
; BASE-LABEL: function 'serial_outer_carries':
; BASE: Src:  %v = load i32, ptr %ld.p, align 4 --> Dst:  store i32 %v1, ptr %st.p, align 4
; BASE-NEXT: da analyze - consistent anti [-1 1]!
; DRF-LABEL: function 'serial_outer_carries':
; DRF: Src:  %v = load i32, ptr %ld.p, align 4 --> Dst:  store i32 %v1, ptr %st.p, align 4
; DRF-NEXT: da analyze - consistent anti [-1 1]!
; UNGUARDED-LABEL: function 'serial_outer_carries':
; UNGUARDED: Src:  %v = load i32, ptr %ld.p, align 4 --> Dst:  store i32 %v1, ptr %st.p, align 4
; UNGUARDED-NEXT: da analyze - anti [-1 0|<]!
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

; The same nest with row-wise accesses: DA proves the serial t level EQ, so
; every dependent pair lives in one instance of the j loop and the guard still
; lets the Tapir level be refined.
;
; BASE-LABEL: function 'serial_outer_eq':
; BASE: Src:  %v = load i32, ptr %ld.p, align 4 --> Dst:  store i32 %v1, ptr %st.p, align 4
; BASE-NEXT: da analyze - consistent anti [0 1]!
; DRF-LABEL: function 'serial_outer_eq':
; DRF: Src:  %v = load i32, ptr %ld.p, align 4 --> Dst:  store i32 %v1, ptr %st.p, align 4
; DRF-NEXT: da analyze - anti [0 0|<]!
define void @serial_outer_eq(ptr noalias %A) {
entry:
  br label %t.header

t.header:
  %t = phi i64 [ 0, %entry ], [ %t.inc, %t.latch ]
  br label %j.header

j.header:
  %j = phi i64 [ 0, %t.header ], [ %j.inc, %j.header ]
  %j1 = add nuw nsw i64 %j, 1
  %ld.p = getelementptr inbounds [64 x [64 x i32]], ptr %A, i64 0, i64 %t, i64 %j1
  %v = load i32, ptr %ld.p, align 4
  %v1 = add i32 %v, 1
  %st.p = getelementptr inbounds [64 x [64 x i32]], ptr %A, i64 0, i64 %t, i64 %j
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
