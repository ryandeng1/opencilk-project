; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=BASE
; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-delta-set-proof -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=DELTA
; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-delta-set-proof -enable-drf-aa-presburger-delta-set-proof -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=PRESBURGER
; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-delta-set-proof -enable-drf-aa-presburger-delta-set-proof -drf-aa-presburger-delta-set-max-loop-vars=3 -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=PRESBURGER3
; See drf-aa-delta-set-serial-outer-attribution.ll for checks of which backend
; supplied each answer (requires an asserts build).

; A serial loop k enclosing a parallel loop i, with k appearing in both
; addresses:
;
;   for (k = 0; k < 8; ++k)            // serial
;     cilk_for (i = 0; i < 4; ++i) {   // parallel
;       v = b[8*k + i];                // load  B(k,i)
;       a[k + i] = v + 1;              // store A(k,i)
;     }
;
; With a == b + 7 this program is race-free: two accesses can only race in
; the same cilk_for instance (same k, different i), and a[k+x] == b[8k+y]
; with x != y would need |y - x| = 7|1 - k| >= 7 > 3.  Yet at k == 1,
; a[1+i] == b[8+i] for every i: the load and the store touch the same
; address in the same strand, which is legal.  The correct answer is
; therefore MayAlias.
;
; The same-instance delta -7k is only reproduced by pairs that live in
; *different* k iterations, e.g. A(k-1, i+1) vs B(k, i).  Those are ordered
; by the sync that ends each cilk_for and never race, so they must not be
; accepted as race witnesses.  Two iteration points are logically parallel
; only when the outermost coordinate in which they differ belongs to a
; parallel loop.

; BASE:           MayAlias: {{.*}}%pa, {{.*}}%pb
; DELTA:          MayAlias: {{.*}}%pa, {{.*}}%pb
; DELTA-NOT:      NoAlias: {{.*}}%pa, {{.*}}%pb
; PRESBURGER:     MayAlias: {{.*}}%pa, {{.*}}%pb
; PRESBURGER-NOT: NoAlias: {{.*}}%pa, {{.*}}%pb
; PRESBURGER3:     MayAlias: {{.*}}%pa, {{.*}}%pb
; PRESBURGER3-NOT: NoAlias: {{.*}}%pa, {{.*}}%pb

define void @serial_outer_const(ptr %a, ptr %b) {
entry:
  br label %k.cond

k.cond:
  %k = phi i64 [ 0, %entry ], [ %k.next, %k.inc ]
  %sr = call token @llvm.syncregion.start()
  br label %pfor.cond

pfor.cond:
  %i = phi i64 [ 0, %k.cond ], [ %i.next, %pfor.inc ]
  detach within %sr, label %pfor.body, label %pfor.inc

pfor.body:
  %brow = mul nuw nsw i64 %k, 8
  %bidx = add nuw nsw i64 %brow, %i
  %pb = getelementptr inbounds double, ptr %b, i64 %bidx
  %v = load double, ptr %pb, align 8
  %aidx = add nuw nsw i64 %k, %i
  %pa = getelementptr inbounds double, ptr %a, i64 %aidx
  %w = fadd double %v, 1.0
  store double %w, ptr %pa, align 8
  reattach within %sr, label %pfor.inc

pfor.inc:
  %i.next = add nuw nsw i64 %i, 1
  %i.done = icmp eq i64 %i.next, 4
  br i1 %i.done, label %pfor.end, label %pfor.cond

pfor.end:
  sync within %sr, label %k.inc

k.inc:
  %k.next = add nuw nsw i64 %k, 1
  %k.done = icmp eq i64 %k.next, 8
  br i1 %k.done, label %exit, label %k.cond

exit:
  ret void
}

; The same shape with symbolic trip counts exercises the Presburger and
; symbolic-witness paths instead of the constant-domain solvers.

; BASE:           MayAlias: {{.*}}%pa.sym, {{.*}}%pb.sym
; DELTA:          MayAlias: {{.*}}%pa.sym, {{.*}}%pb.sym
; DELTA-NOT:      NoAlias: {{.*}}%pa.sym, {{.*}}%pb.sym
; PRESBURGER:     MayAlias: {{.*}}%pa.sym, {{.*}}%pb.sym
; PRESBURGER-NOT: NoAlias: {{.*}}%pa.sym, {{.*}}%pb.sym
; PRESBURGER3:     MayAlias: {{.*}}%pa.sym, {{.*}}%pb.sym
; PRESBURGER3-NOT: NoAlias: {{.*}}%pa.sym, {{.*}}%pb.sym

define void @serial_outer_sym(ptr %a, ptr %b, i64 %K, i64 %N) {
entry:
  br label %k.cond

k.cond:
  %k = phi i64 [ 0, %entry ], [ %k.next, %k.inc ]
  %sr = call token @llvm.syncregion.start()
  br label %pfor.cond

pfor.cond:
  %i = phi i64 [ 0, %k.cond ], [ %i.next, %pfor.inc ]
  detach within %sr, label %pfor.body, label %pfor.inc

pfor.body:
  %brow = mul nuw nsw i64 %k, 8
  %bidx = add nuw nsw i64 %brow, %i
  %pb.sym = getelementptr inbounds double, ptr %b, i64 %bidx
  %v = load double, ptr %pb.sym, align 8
  %aidx = add nuw nsw i64 %k, %i
  %pa.sym = getelementptr inbounds double, ptr %a, i64 %aidx
  %w = fadd double %v, 1.0
  store double %w, ptr %pa.sym, align 8
  reattach within %sr, label %pfor.inc

pfor.inc:
  %i.next = add nuw nsw i64 %i, 1
  %i.done = icmp eq i64 %i.next, %N
  br i1 %i.done, label %pfor.end, label %pfor.cond

pfor.end:
  sync within %sr, label %k.inc

k.inc:
  %k.next = add nuw nsw i64 %k, 1
  %k.done = icmp eq i64 %k.next, %K
  br i1 %k.done, label %exit, label %k.cond

exit:
  ret void
}

; Positive control: an enclosing serial loop in the addresses must not
; disable the proof when the race witness lives in the same k instance.
;
;   for (k = 0; k < 8; ++k)                       // serial
;     cilk_for (i = 0; i < 4; ++i)                // parallel
;       for (j = 0; j < 4; ++j)                   // serial
;         tmp[i + k] += mat[(i + k) * 4 + j];
;
; If tmp[i+k] and mat[i+k][j] coincide in iteration (k, i, j), then
; tmp[i+1+k] (written by task i+1) coincides with mat[i+k][j+1] (read by
; task i) in the same k instance, which is a race.  The witness agrees with
; the original point on k, so it is a genuine cross-task pair.

; DELTA:          NoAlias: {{.*}}%pmat, {{.*}}%ptmp
; PRESBURGER:     NoAlias: {{.*}}%pmat, {{.*}}%ptmp
; PRESBURGER3:    NoAlias: {{.*}}%pmat, {{.*}}%ptmp

define void @serial_outer_same_instance_witness(ptr %tmp, ptr %mat) {
entry:
  br label %k.cond

k.cond:
  %k = phi i64 [ 0, %entry ], [ %k.next, %k.inc ]
  %sr = call token @llvm.syncregion.start()
  br label %pfor.cond

pfor.cond:
  %i = phi i64 [ 0, %k.cond ], [ %i.next, %pfor.inc ]
  detach within %sr, label %pfor.body, label %pfor.inc

pfor.body:
  br label %for.cond

for.cond:
  %j = phi i64 [ 0, %pfor.body ], [ %j.next, %for.inc ]
  %ik = add nuw nsw i64 %i, %k
  %ptmp = getelementptr inbounds double, ptr %tmp, i64 %ik
  %old = load double, ptr %ptmp, align 8
  %row = mul nuw nsw i64 %ik, 4
  %idx = add nuw nsw i64 %row, %j
  %pmat = getelementptr inbounds double, ptr %mat, i64 %idx
  %v = load double, ptr %pmat, align 8
  %sum = fadd double %old, %v
  store double %sum, ptr %ptmp, align 8
  br label %for.inc

for.inc:
  %j.next = add nuw nsw i64 %j, 1
  %j.done = icmp eq i64 %j.next, 4
  br i1 %j.done, label %pfor.body.exit, label %for.cond

pfor.body.exit:
  reattach within %sr, label %pfor.inc

pfor.inc:
  %i.next = add nuw nsw i64 %i, 1
  %i.done = icmp eq i64 %i.next, 4
  br i1 %i.done, label %pfor.end, label %pfor.cond

pfor.end:
  sync within %sr, label %k.inc

k.inc:
  %k.next = add nuw nsw i64 %k, 1
  %k.done = icmp eq i64 %k.next, 8
  br i1 %k.done, label %exit, label %k.cond

exit:
  ret void
}

; The same positive control with symbolic trip counts.  The interval solver
; needs constant rectangular bounds and the symbolic/exhaustive fallbacks are
; capped at two instance loops, so only the exact Presburger backend can
; supply this answer -- and only when its loop-variable cap admits the
; three-dimensional (k, i, j) instance domain.  Note that the cap counts the
; serial k as well: under the default cap of two this query stays MayAlias,
; which is a compile-time cost limit, not a correctness requirement.

; PRESBURGER3:    NoAlias: {{.*}}%pmat.sym, {{.*}}%ptmp.sym

define void @serial_outer_same_instance_witness_sym(ptr %tmp, ptr %mat, i64 %K, i64 %N) {
entry:
  br label %k.cond

k.cond:
  %k = phi i64 [ 0, %entry ], [ %k.next, %k.inc ]
  %sr = call token @llvm.syncregion.start()
  br label %pfor.cond

pfor.cond:
  %i = phi i64 [ 0, %k.cond ], [ %i.next, %pfor.inc ]
  detach within %sr, label %pfor.body, label %pfor.inc

pfor.body:
  br label %for.cond

for.cond:
  %j = phi i64 [ 0, %pfor.body ], [ %j.next, %for.inc ]
  %ik = add nuw nsw i64 %i, %k
  %ptmp.sym = getelementptr inbounds double, ptr %tmp, i64 %ik
  %old = load double, ptr %ptmp.sym, align 8
  %row = mul nuw nsw i64 %ik, 4
  %idx = add nuw nsw i64 %row, %j
  %pmat.sym = getelementptr inbounds double, ptr %mat, i64 %idx
  %v = load double, ptr %pmat.sym, align 8
  %sum = fadd double %old, %v
  store double %sum, ptr %ptmp.sym, align 8
  br label %for.inc

for.inc:
  %j.next = add nuw nsw i64 %j, 1
  %j.done = icmp eq i64 %j.next, 4
  br i1 %j.done, label %pfor.body.exit, label %for.cond

pfor.body.exit:
  reattach within %sr, label %pfor.inc

pfor.inc:
  %i.next = add nuw nsw i64 %i, 1
  %i.done = icmp eq i64 %i.next, %N
  br i1 %i.done, label %pfor.end, label %pfor.cond

pfor.end:
  sync within %sr, label %k.inc

k.inc:
  %k.next = add nuw nsw i64 %k, 1
  %k.done = icmp eq i64 %k.next, %K
  br i1 %k.done, label %exit, label %k.cond

exit:
  ret void
}

declare token @llvm.syncregion.start()
