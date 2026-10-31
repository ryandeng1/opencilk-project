; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false -S %s | \
; RUN:   FileCheck %s --check-prefix=PAIR
; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false \
; RUN:   -drf-aa-proven-pair-max-accesses-per-task=1 \
; RUN:   -drf-aa-proven-pair-max-checks-per-task=1 -S %s | \
; RUN:   FileCheck %s --check-prefix=BUDGET
; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false \
; RUN:   -drf-aa-proven-pair-max-checks-per-parallel-loop=1 -S %s | \
; RUN:   FileCheck %s --check-prefix=LOOP-LIMIT
; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false -stats -disable-output %s \
; RUN:   2>&1 | FileCheck %s --check-prefix=STATS
; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false -S %s -o %t.once
; RUN: opt -passes='drf-scoped-noalias,drf-scoped-noalias' -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false -S %s -o %t.twice
; RUN: diff %t.once %t.twice

; A varying write and two invariant reads give two full NoAlias proofs.  The
; compact representation creates one scope per access; the store's noalias
; list contains both read scopes.  The limit-1 run also proves both edges,
; because limits apply to individual access/bucket pairs rather than skipping
; this entire task after seeing three accesses.
;
; PAIR-LABEL: define void @pair_graph(
; PAIR-SAME: !drfaa.generated.alias.scope.domains
; PAIR: store double 1.000000e+00, ptr %pvar{{.*}}!alias.scope [[STORE_AS:![0-9]+]], !noalias [[STORE_NA:![0-9]+]]
; PAIR: load double, ptr %pinv1{{.*}}!alias.scope [[LOAD1_AS:![0-9]+]], !noalias [[STORE_AS]]
; PAIR: load double, ptr %pinv2{{.*}}!alias.scope [[LOAD2_AS:![0-9]+]], !noalias [[STORE_AS]]
;
; BUDGET-LABEL: define void @pair_graph(
; BUDGET-SAME: !drfaa.generated.alias.scope.domains
; BUDGET: store double 1.000000e+00, ptr %pvar{{.*}}!alias.scope {{![0-9]+}}, !noalias [[BUDGET_STORE_NA:![0-9]+]]
; BUDGET: [[BUDGET_STORE_NA]] = !{!{{[0-9]+}}, !{{[0-9]+}}}
;
; The independent total cap bounds the number of candidates visited in one
; parallel loop without preventing later loop contexts from being analyzed.
;
; LOOP-LIMIT-LABEL: define void @pair_graph(
; LOOP-LIMIT: store double 1.000000e+00, ptr %pvar{{.*}}!alias.scope {{![0-9]+}}, !noalias [[LIMIT_STORE_NA:![0-9]+]]
; LOOP-LIMIT: load double, ptr %pinv1{{.*}}!alias.scope
; LOOP-LIMIT: load double, ptr %pinv2, align 8{{$}}
; LOOP-LIMIT: [[LIMIT_STORE_NA]] = !{!{{[0-9]+}}}
;
; STATS: 3 drf-scoped-noalias - Number of DRF NoAlias pair proofs materialized
; STATS: 1 drf-scoped-noalias - Number of DRF pairs classified only NoCrossIteration
; STATS: 5 drf-scoped-noalias - Number of compact DRF per-access alias scopes materialized
define void @pair_graph(ptr %row, ptr %scalar1, ptr %scalar2) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %header

header:
  %j = phi i64 [ 0, %entry ], [ %j.next, %latch ]
  detach within %sr, label %body, label %latch

body:
  %pvar = getelementptr inbounds double, ptr %row, i64 %j
  store double 1.000000e+00, ptr %pvar
  %pinv1 = getelementptr inbounds double, ptr %scalar1, i64 0
  %v1 = load double, ptr %pinv1
  %pinv2 = getelementptr inbounds double, ptr %scalar2, i64 0
  %v2 = load double, ptr %pinv2
  reattach within %sr, label %latch

latch:
  %j.next = add nuw nsw i64 %j, 1
  %cmp = icmp slt i64 %j.next, 4
  br i1 %cmp, label %header, label %exit

exit:
  sync within %sr, label %cont

cont:
  ret void
}

; These accesses can alias in the same iteration, so DRF establishes only
; NoCrossIteration.  That fact must not be materialized as scoped noalias.
;
; PAIR-LABEL: define void @same_iteration(
; PAIR-NOT: !drfaa.generated.alias.scope.domains
; PAIR: store double 1.000000e+00, ptr %pa, align 8
; PAIR: store double 2.000000e+00, ptr %pb, align 8
; PAIR-NOT: !alias.scope
define void @same_iteration(ptr %a, ptr %b) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %latch ]
  detach within %sr, label %body, label %latch

body:
  %pa = getelementptr inbounds double, ptr %a, i64 %i
  %pb = getelementptr inbounds double, ptr %b, i64 %i
  store double 1.000000e+00, ptr %pa
  store double 2.000000e+00, ptr %pb
  reattach within %sr, label %latch

latch:
  %i.next = add nuw nsw i64 %i, 1
  %cmp = icmp slt i64 %i.next, 4
  br i1 %cmp, label %header, label %exit

exit:
  sync within %sr, label %cont

cont:
  ret void
}

; Pair proofs are also rebuilt after Tapir has serialized a loop, using its
; fromtapirloop provenance rather than requiring live detach instructions.
;
; PAIR-LABEL: define void @serialized_pair(
; PAIR-SAME: !drfaa.generated.alias.scope.domains
; PAIR: store double 1.000000e+00, ptr %pvar.serial{{.*}}!alias.scope
; PAIR: load double, ptr %pinv.serial{{.*}}!alias.scope
; PAIR-DAG: [[STORE_AS]] = !{!{{[0-9]+}}}
; PAIR-DAG: [[LOAD1_AS]] = !{!{{[0-9]+}}}
; PAIR-DAG: [[LOAD2_AS]] = !{!{{[0-9]+}}}
; PAIR-DAG: [[STORE_NA]] = !{!{{[0-9]+}}, !{{[0-9]+}}}
define void @serialized_pair(ptr %row, ptr %scalar) {
entry:
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %latch ]
  br label %body

body:
  %pvar.serial = getelementptr inbounds double, ptr %row, i64 %i
  store double 1.000000e+00, ptr %pvar.serial
  %pinv.serial = getelementptr inbounds double, ptr %scalar, i64 0
  %v = load double, ptr %pinv.serial
  br label %latch

latch:
  %i.next = add nuw nsw i64 %i, 1
  %cmp = icmp slt i64 %i.next, 4
  br i1 %cmp, label %header, label %exit, !llvm.loop !0

exit:
  ret void
}

declare token @llvm.syncregion.start()

!0 = distinct !{!0, !1}
!1 = !{!"llvm.loop.fromtapirloop"}
