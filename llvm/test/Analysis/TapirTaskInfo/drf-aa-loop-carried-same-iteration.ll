; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s

; Soundness regression test.  %pa and %pb are two accesses in the *same* Tapir
; loop body (same task).  They are logically parallel only across *distinct*
; iterations; within one iteration they execute in a single serial strand, so
; if %a and %b name the same allocation at run time the program is still
; race-free and they genuinely alias.  DRFAA must therefore NOT report NoAlias
; here -- loop-carried parallelism is not a license for an unconditional
; (different-underlying-object) no-alias answer on an ordinary, non
; cross-iteration query.
;
; Before the fix, DRFAA returned NoAlias for this pair, which miscompiled
;   cilk_for (i) { a[i]=1; b[i]=2; a[i]=a[i]+b[i]; }
; (called with a==b) by folding a[i]+b[i] to the constant 3.0 instead of 4.0.

define void @f(ptr %a, ptr %b, i64 %n) {
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
  %i.next = add nsw i64 %i, 1
  %cmp = icmp slt i64 %i.next, %n
  br i1 %cmp, label %header, label %exit

exit:
  sync within %sr, label %cont

cont:
  ret void
}

declare token @llvm.syncregion.start()

; CHECK: MayAlias: {{.*}}%pa, {{.*}}%pb
; CHECK-NOT: NoAlias:
