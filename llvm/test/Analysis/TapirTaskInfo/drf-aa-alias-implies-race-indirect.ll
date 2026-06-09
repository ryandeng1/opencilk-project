; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s

; %pvar is affine in the Tapir-loop iteration, but %pind is an indirect access
; through %idx[j].  The indirect address is not loop-invariant; it is opaque
; SCEVUnknown-dependent state defined in the loop body.  DRFAA must not treat
; the absence of an addrec in %pind as proof that %pind repeats in every sibling
; iteration.

define void @indirect(ptr %a, ptr %b, ptr %idx) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %header

header:
  %j = phi i64 [ 0, %entry ], [ %j.next, %latch ]
  detach within %sr, label %body, label %latch

body:
  %pvar = getelementptr inbounds double, ptr %a, i64 %j
  store double 1.000000e+00, ptr %pvar
  %idxp = getelementptr inbounds i64, ptr %idx, i64 %j
  %idxv = load i64, ptr %idxp
  %pind = getelementptr inbounds double, ptr %b, i64 %idxv
  %v = load double, ptr %pind
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

; CHECK: MayAlias: {{.*}}%pind, {{.*}}%pvar
; CHECK-NOT: NoAlias:
