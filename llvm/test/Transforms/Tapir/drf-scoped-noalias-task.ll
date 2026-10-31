; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-proven-pair-metadata=false -S %s | \
; RUN:   FileCheck %s --check-prefix=TASK
; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false \
; RUN:   -enable-drf-aa-proven-pair-metadata=false -S %s | \
; RUN:   FileCheck %s --check-prefix=OFF

@reducer = global i64 0

; Each task has an all-access scope and a write-only scope.  A parallel read
; excludes the write scope; a parallel write excludes the all-access scope.
; This proves both write/read orientations and write/write separation without
; incorrectly separating legal parallel reads.
;
; Calls, atomics, volatile accesses, and hyperobject views have semantics not
; modeled by this structural proof and must receive no task metadata.
;
; TASK-LABEL: define void @access_kinds(
; TASK-SAME: !drfaa.generated.alias.scope.domains
; TASK: %task.read = load i32, ptr %taskp, align 4, !alias.scope [[ALL_LIST:![0-9]+]]
; TASK: store i32 1, ptr %task.writep, align 4, !alias.scope [[ALL_WRITE_LIST:![0-9]+]]
; TASK: %task.atomic = load atomic i32, ptr %taskp monotonic, align 4{{$}}
; TASK: store volatile i32 2, ptr %task.writep, align 4{{$}}
; TASK: %task.rmw = atomicrmw add ptr %taskp, i32 1 monotonic, align 4{{$}}
; TASK: call void @opaque(ptr %taskp){{$}}
; TASK: %view = call ptr @llvm.hyper.lookup.2.i64(
; TASK: store i64 1, ptr %view, align 8{{$}}
; TASK: %cont.read = load i32, ptr %contp, align 4, !noalias [[WRITE_LIST:![0-9]+]]
; TASK: store i32 3, ptr %cont.writep, align 4, !noalias [[ALL_LIST]]
; TASK: [[ALL_LIST]] = !{[[ALL_SCOPE:![0-9]+]]}
; TASK: [[ALL_WRITE_LIST]] = !{[[ALL_SCOPE]], [[WRITE_SCOPE:![0-9]+]]}
; TASK: [[WRITE_LIST]] = !{[[WRITE_SCOPE]]}
define void @access_kinds(ptr %taskp, ptr %contp) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %task, label %cont

task:
  %task.read = load i32, ptr %taskp
  %task.writep = getelementptr inbounds i32, ptr %taskp, i64 1
  store i32 1, ptr %task.writep
  %task.atomic = load atomic i32, ptr %taskp monotonic, align 4
  store volatile i32 2, ptr %task.writep
  %task.rmw = atomicrmw add ptr %taskp, i32 1 monotonic
  call void @opaque(ptr %taskp)
  %view = call ptr @llvm.hyper.lookup.2.i64(ptr @reducer, i64 8, ptr null, ptr null)
  store i64 1, ptr %view, align 8
  reattach within %sr, label %cont

cont:
  %cont.read = load i32, ptr %contp
  %cont.writep = getelementptr inbounds i32, ptr %contp, i64 1
  store i32 3, ptr %cont.writep
  sync within %sr, label %exit

exit:
  ret void
}

; The mechanisms have independent gates.  With both disabled, the pass owns
; no metadata and leaves every access untouched.
;
; OFF-NOT: drfaa.generated.alias.scope.domains
; OFF-NOT: !alias.scope
; OFF-NOT: !noalias

declare token @llvm.syncregion.start()
declare void @opaque(ptr)
declare ptr @llvm.hyper.lookup.2.i64(ptr, i64, ptr, ptr)
