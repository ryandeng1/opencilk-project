; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s

; If %pvar and %pinv alias, then the guaranteed store to %row[j] in one
; Tapir-loop iteration races with the guaranteed invariant load from
; %scalar[0] in a sibling iteration.  Under the data-race-free assumption,
; DRFAA can therefore answer NoAlias for this ordinary same-body query even
; though loop-carried parallelism alone is not enough.

define void @nested(ptr %row, ptr %scalar) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %header

header:
  %j = phi i64 [ 0, %entry ], [ %j.next, %latch ]
  detach within %sr, label %body, label %latch

body:
  %pvar = getelementptr inbounds double, ptr %row, i64 %j
  store double 1.000000e+00, ptr %pvar
  %pinv = getelementptr inbounds double, ptr %scalar, i64 0
  %v = load double, ptr %pinv
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

declare token @llvm.syncregion.start()

; CHECK: NoAlias: {{.*}}%pinv, {{.*}}%pvar
