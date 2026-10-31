; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=BASE
; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-delta-set-proof -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=DELTA
; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-delta-set-proof -enable-drf-aa-presburger-delta-set-proof -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=PRESBURGER

; The ordinary same-body query %ptmp vs %pmat is not covered by the older
; one-varying-axis or replicated-fiber witnesses: both addresses vary with the
; parallel i loop, and neither single address is replicated across i tasks.
;
; With the delta-set proof enabled, every same-instance delta
;   tmp[i] - mat[i][j]
; is also produced by some cross-i pair of dynamic accesses in the loop nest.
; Therefore any aliasing between the two logical objects would imply a
; cross-task read/write race.

; BASE-NOT: NoAlias: {{.*}}%pmat, {{.*}}%ptmp
; DELTA: NoAlias: {{.*}}%pmat, {{.*}}%ptmp
; PRESBURGER: NoAlias: {{.*}}%pmat, {{.*}}%ptmp

define void @delta_1d_2d(ptr %tmp, ptr %mat) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %pfor.cond

pfor.cond:
  %i = phi i64 [ 0, %entry ], [ %i.next, %pfor.inc ]
  detach within %sr, label %pfor.body, label %pfor.inc

pfor.body:
  br label %for.cond

for.cond:
  %j = phi i64 [ 0, %pfor.body ], [ %j.next, %for.inc ]
  %ptmp = getelementptr inbounds double, ptr %tmp, i64 %i
  %old = load double, ptr %ptmp, align 8
  %row = mul nuw nsw i64 %i, 4
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
  br i1 %i.done, label %pfor.cond.cleanup, label %pfor.cond

pfor.cond.cleanup:
  sync within %sr, label %sync.continue

sync.continue:
  ret void
}

declare token @llvm.syncregion.start()


; The transposed shape is different.  In a j-parallel loop, s[j] and
; mat[i][j] can overlap in the same dynamic j task (for example s[j] ==
; mat[0][j]) without forcing any sibling-task access to the same address.
; The delta-set proof must therefore leave this as MayAlias.
;
; DELTA: MayAlias: {{.*}}%pmat.col, {{.*}}%ps
; DELTA-NOT: NoAlias: {{.*}}%pmat.col, {{.*}}%ps
; PRESBURGER: MayAlias: {{.*}}%pmat.col, {{.*}}%ps
; PRESBURGER-NOT: NoAlias: {{.*}}%pmat.col, {{.*}}%ps

define void @delta_2d_1d_column_wall(ptr %mat, ptr %s) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %pfor.cond

pfor.cond:
  %j = phi i64 [ 0, %entry ], [ %j.next, %pfor.inc ]
  detach within %sr, label %pfor.body, label %pfor.inc

pfor.body:
  br label %for.cond

for.cond:
  %i = phi i64 [ 0, %pfor.body ], [ %i.next, %for.inc ]
  %ps = getelementptr inbounds double, ptr %s, i64 %j
  %old = load double, ptr %ps, align 8
  %row = mul nuw nsw i64 %i, 4
  %idx = add nuw nsw i64 %row, %j
  %pmat.col = getelementptr inbounds double, ptr %mat, i64 %idx
  %v = load double, ptr %pmat.col, align 8
  %sum = fadd double %old, %v
  store double %sum, ptr %ps, align 8
  br label %for.inc

for.inc:
  %i.next = add nuw nsw i64 %i, 1
  %i.done = icmp eq i64 %i.next, 4
  br i1 %i.done, label %pfor.body.exit, label %for.cond

pfor.body.exit:
  reattach within %sr, label %pfor.inc

pfor.inc:
  %j.next = add nuw nsw i64 %j, 1
  %j.done = icmp eq i64 %j.next, 4
  br i1 %j.done, label %pfor.cond.cleanup, label %pfor.cond

pfor.cond.cleanup:
  sync within %sr, label %sync.continue

sync.continue:
  ret void
}

; Strip-mining can produce a logically parallel outer loop with one dynamic
; iteration even when the source Tapir loop has a large trip count.  Its i1
; backedge-taken count is false, and its exact trip count is one.  The assumed
; source-loop minimum must not turn this generated loop's domain into an empty
; Presburger set: %pa and %pb can legally alias within the sole outer task.
;
; PRESBURGER: MayAlias: {{.*}}%pa, {{.*}}%pb
; PRESBURGER-NOT: NoAlias: {{.*}}%pa, {{.*}}%pb

define void @delta_single_parallel_strip_same_index(ptr %a, ptr %b) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %strip.cond

strip.cond:
  %strip = phi i1 [ false, %entry ], [ %strip.next, %strip.inc ]
  detach within %sr, label %strip.body, label %strip.inc

strip.body:
  %strip.ext = zext i1 %strip to i64
  %strip.base = shl nuw nsw i64 %strip.ext, 7
  br label %inner.cond

inner.cond:
  %inner = phi i64 [ 0, %strip.body ], [ %inner.next, %inner.inc ]
  %idx = add nuw nsw i64 %strip.base, %inner
  %pa = getelementptr inbounds double, ptr %a, i64 %idx
  %old = load double, ptr %pa, align 8
  %pb = getelementptr inbounds double, ptr %b, i64 %idx
  %value = load double, ptr %pb, align 8
  %sum = fadd double %old, %value
  store double %sum, ptr %pa, align 8
  br label %inner.inc

inner.inc:
  %inner.next = add nuw nsw i64 %inner, 1
  %inner.done = icmp eq i64 %inner.next, 128
  br i1 %inner.done, label %strip.body.exit, label %inner.cond

strip.body.exit:
  reattach within %sr, label %strip.inc

strip.inc:
  %strip.next = xor i1 %strip, true
  %strip.done = icmp eq i1 %strip.next, true
  br i1 %strip.done, label %strip.cleanup, label %strip.cond

strip.cleanup:
  sync within %sr, label %exit

exit:
  ret void
}
