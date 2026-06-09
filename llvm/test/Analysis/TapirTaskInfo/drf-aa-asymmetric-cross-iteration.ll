; RUN: opt -disable-output < %s -passes='print<access-info>' -aa-pipeline=drf-aa -enable-drf-aa 2>&1 | FileCheck %s --check-prefix=DRFAA
; RUN: opt -disable-output < %s -passes='print<access-info>' 2>&1 | FileCheck %s --check-prefix=STOCK

; In the Tapir loop  cilk_for (j) { a[j] = c[0]; }  the store address a[j] varies
; with the iteration while the load address c[0] is loop-invariant, and %a and %c
; are distinct allocations.  If the two could ever overlap, the invariant load in
; one sibling iteration would race with the varying store in another -- forbidden
; under the data-race-free assumption -- so DRFAA answers NoAlias.  This is the
; cross-iteration counterpart of drf-aa-alias-implies-race.ll (which exercises the
; same reasoning on an ordinary same-body query): LoopAccessAnalysis queries alias
; analysis in cross-iteration mode, so DRFAA must apply the "alias would imply a
; parallel race" argument there too, eliminating the runtime memory check.

; DRFAA: Memory dependences are safe
; DRFAA-NOT: Comparing group
; DRFAA-NOT: run-time checks

; Stock LLVM cannot prove %a and %c disjoint, so it needs a runtime check.
; STOCK: Memory dependences are safe with run-time checks
; STOCK: Comparing group

define void @k(ptr %a, ptr %c, i64 %n) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %header

header:
  %j = phi i64 [ 0, %entry ], [ %j.next, %latch ]
  detach within %sr, label %body, label %latch

body:
  %pa = getelementptr inbounds double, ptr %a, i64 %j
  %pc = getelementptr inbounds double, ptr %c, i64 0
  %vc = load double, ptr %pc
  store double %vc, ptr %pa
  reattach within %sr, label %latch

latch:
  %j.next = add nuw nsw i64 %j, 1
  %cmp = icmp slt i64 %j.next, %n
  br i1 %cmp, label %header, label %exit

exit:
  sync within %sr, label %cont

cont:
  ret void
}

declare token @llvm.syncregion.start()
