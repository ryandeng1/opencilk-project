; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s

; %pa is accessed in a spawned task and %pb in its continuation, so the two
; accesses are *definitely* logically parallel: they run in distinct parallel
; tasks for every dynamic instance.  Under the data-race-free assumption,
; aliasing would be a race, so DRFAA may soundly report NoAlias for distinct
; underlying objects.  This guards that the soundness fix for loop-carried
; parallelism did not over-restrict genuine (different-task) parallelism.

define void @g(ptr %a, ptr %b) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %task, label %cont

task:
  %pa = getelementptr inbounds double, ptr %a, i64 0
  store double 1.000000e+00, ptr %pa
  reattach within %sr, label %cont

cont:
  %pb = getelementptr inbounds double, ptr %b, i64 0
  store double 2.000000e+00, ptr %pb
  sync within %sr, label %after

after:
  ret void
}

declare token @llvm.syncregion.start()

; CHECK: NoAlias: {{.*}}%pa, {{.*}}%pb
