; REQUIRES: asserts
; RUN: opt -disable-output < %S/drf-aa-delta-set-serial-outer.ll -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-delta-set-proof -enable-drf-aa-presburger-delta-set-proof -drf-aa-presburger-delta-set-max-loop-vars=3 -print-all-alias-modref-info -debug-only=drf-aa-result 2>&1 | FileCheck %s

; Companion to drf-aa-delta-set-serial-outer.ll: the check prefixes there only
; enable a backend, they do not show which backend produced an answer.  This
; file reads the DRF-AA debug trace to attribute each result.
;
; The debug strings are distinct per backend:
;   "via affine interval delta-set inclusion proof"   constant-domain interval cover
;   "via affine delta-set inclusion proof"            exact Presburger subtraction
;   "via symbolic affine delta-set inclusion proof"   constant-shift witnesses
;   "via delta-set inclusion proof"                   exhaustive enumeration

; No backend may manufacture a witness for the two negative cases: every
; candidate pair for the same-instance delta -7k lives in different k
; iterations, which the sync at the end of each cilk_for orders.

; CHECK-LABEL: Function: serial_outer_const
; CHECK-NOT:   alias-implies-race via
; CHECK:       MayAlias: {{.*}}%pa, {{.*}}%pb

; CHECK-LABEL: Function: serial_outer_sym
; CHECK-NOT:   alias-implies-race via
; CHECK:       MayAlias: {{.*}}%pa.sym, {{.*}}%pb.sym

; The constant-bound positive control is settled by the cheap interval cover
; before the Presburger backend is consulted.

; CHECK-LABEL: Function: serial_outer_same_instance_witness
; CHECK:       alias-implies-race via affine interval delta-set inclusion proof
; CHECK:       NoAlias: {{.*}}%pmat, {{.*}}%ptmp

; The symbolic-bound positive control can only be settled by the Presburger
; backend, whose cross-task set must keep the serial k coordinate equal and
; still find the same-k witness tmp[i+1+k] / mat[i+k][j+1].

; CHECK-LABEL: Function: serial_outer_same_instance_witness_sym
; CHECK:       alias-implies-race via affine delta-set inclusion proof
; CHECK:       NoAlias: {{.*}}%pmat.sym, {{.*}}%ptmp.sym
