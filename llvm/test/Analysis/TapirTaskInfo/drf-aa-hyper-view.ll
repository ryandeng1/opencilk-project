; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-hyper-view -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=BOTH,HYPER
; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=BOTH,DEFAULT

; A hyperobject view access is runtime-mediated.  Under the serial-projection
; race model every lookup of @gsum denotes @gsum's leftmost storage, so if the
; view could overlap an ordinary parallel-varying access, the leftmost storage
; would be involved in a cross-strand race that the DRF assumption forbids.
; With -enable-drf-aa-hyper-view, DRFAA substitutes the hyperobject handle for
; the view and the existing asymmetric loop-carried proof answers NoAlias for
; view-vs-array queries.  Without the flag, the view is an opaque loop-defined
; pointer and every proof must bail.

@gsum = global i64 0

define void @reducer_loop(ptr %a, ptr %out) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %header

header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %latch ]
  detach within %sr, label %body, label %latch

body:
  %view = call ptr @llvm.hyper.lookup.2.i64(ptr @gsum, i64 8, ptr @zero, ptr @plus)
  %pa = getelementptr inbounds i64, ptr %a, i64 %i
  %va = load i64, ptr %pa
  %acc = load i64, ptr %view
  %sum = add i64 %acc, %va
  store i64 %sum, ptr %view
  %pout = getelementptr inbounds i64, ptr %out, i64 %i
  %dbl = shl i64 %va, 1
  store i64 %dbl, ptr %pout
  reattach within %sr, label %latch

latch:
  %i.next = add nuw nsw i64 %i, 1
  %cmp = icmp slt i64 %i.next, 1024
  br i1 %cmp, label %header, label %exit

exit:
  sync within %sr, label %cont

cont:
  ret void
}

; HYPER-DAG: NoAlias:{{.*}}%pa, {{.*}}%view
; HYPER-DAG: NoAlias:{{.*}}%pout, {{.*}}%view
; DEFAULT-DAG: MayAlias:{{.*}}%pa, {{.*}}%view
; DEFAULT-DAG: MayAlias:{{.*}}%pout, {{.*}}%view

; Two views of the same hyperobject in definitely-parallel tasks may legally
; alias (in the serial projection both lookups return the leftmost storage),
; so DRFAA must not conclude NoAlias from the DRF assumption, even though the
; two lookup calls are distinct underlying objects.

define void @two_tasks(ptr %x) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %task1, label %cont1

task1:
  %view1 = call ptr @llvm.hyper.lookup.2.i64(ptr @gsum, i64 8, ptr @zero, ptr @plus)
  %v1 = load i64, ptr %view1
  %s1 = add i64 %v1, 1
  store i64 %s1, ptr %view1
  reattach within %sr, label %cont1

cont1:
  detach within %sr, label %task2, label %cont2

task2:
  %view2 = call ptr @llvm.hyper.lookup.2.i64(ptr @gsum, i64 8, ptr @zero, ptr @plus)
  %v2 = load i64, ptr %view2
  %s2 = add i64 %v2, 2
  store i64 %s2, ptr %view2
  reattach within %sr, label %cont2

cont2:
  sync within %sr, label %done

done:
  ret void
}

; With the flag, DRFAA abstains on view-vs-view; nothing else in the drf-aa
; pipeline proves the pair, so it stays MayAlias.  (Without the flag DRFAA's
; definite-parallel distinct-objects conclusion fires; that unsound answer is
; documented here so a future default-on change does not regress silently.)
; HYPER-DAG: MayAlias:{{.*}}%view1, {{.*}}%view2
; DEFAULT-DAG: NoAlias:{{.*}}%view1, {{.*}}%view2

; BOTH: Alias Analysis Evaluator Report

declare token @llvm.syncregion.start()
declare ptr @llvm.hyper.lookup.2.i64(ptr, i64, ptr, ptr)
declare void @zero(ptr)
declare void @plus(ptr, ptr)
