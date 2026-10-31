; RUN: opt < %s -passes=dse -S | FileCheck %s

; Reducer registration and lookup retain or invoke state held in ordinary
; memory.  They must expose those reads before Tapir lowering, or DSE can
; remove reducer-object and callback initialization needed by stolen views.

%callbacks = type { ptr, ptr }

define void @register_reads_object_state() {
; CHECK-LABEL: define void @register_reads_object_state(
; CHECK: store ptr @identity, ptr %object
; CHECK: store ptr @reduce, ptr %reduce.slot
; CHECK: call void @llvm.reducer.register(i32 0, ptr %object, ptr poison)
entry:
  %object = alloca %callbacks, align 8
  %reduce.slot = getelementptr inbounds %callbacks, ptr %object, i32 0, i32 1
  store ptr @identity, ptr %object, align 8
  store ptr @reduce, ptr %reduce.slot, align 8
  call void @llvm.reducer.register(i32 0, ptr %object, ptr poison)
  ret void
}

define void @register_reads_callbacks(ptr %key) {
; CHECK-LABEL: define void @register_reads_callbacks(
; CHECK: store ptr @identity, ptr %callbacks
; CHECK: store ptr @reduce, ptr %reduce.slot
; CHECK: call void @llvm.reducer.register(i32 1, ptr %key, ptr %callbacks)
entry:
  %callbacks = alloca %callbacks, align 8
  %reduce.slot = getelementptr inbounds %callbacks, ptr %callbacks, i32 0, i32 1
  store ptr @identity, ptr %callbacks, align 8
  store ptr @reduce, ptr %reduce.slot, align 8
  call void @llvm.reducer.register(i32 1, ptr %key, ptr %callbacks)
  ret void
}

define ptr @lookup_0_reads_object_state() {
; CHECK-LABEL: define ptr @lookup_0_reads_object_state(
; CHECK: store ptr @identity, ptr %object
; CHECK: store ptr @reduce, ptr %reduce.slot
; CHECK: %view = call ptr @llvm.hyper.lookup.0(ptr %object)
entry:
  %object = alloca %callbacks, align 8
  %reduce.slot = getelementptr inbounds %callbacks, ptr %object, i32 0, i32 1
  store ptr @identity, ptr %object, align 8
  store ptr @reduce, ptr %reduce.slot, align 8
  %view = call ptr @llvm.hyper.lookup.0(ptr %object)
  ret ptr %view
}

define ptr @lookup_1_reads_callbacks(ptr %key) {
; CHECK-LABEL: define ptr @lookup_1_reads_callbacks(
; CHECK: store ptr @identity, ptr %callbacks
; CHECK: store ptr @reduce, ptr %reduce.slot
; CHECK: %view = call ptr @llvm.hyper.lookup.1(ptr %key, ptr %callbacks)
entry:
  %callbacks = alloca %callbacks, align 8
  %reduce.slot = getelementptr inbounds %callbacks, ptr %callbacks, i32 0, i32 1
  store ptr @identity, ptr %callbacks, align 8
  store ptr @reduce, ptr %reduce.slot, align 8
  %view = call ptr @llvm.hyper.lookup.1(ptr %key, ptr %callbacks)
  ret ptr %view
}

define ptr @lookup_2_uses_raw_callbacks(ptr %key) {
; CHECK-LABEL: define ptr @lookup_2_uses_raw_callbacks(
; CHECK: %view = call ptr @llvm.hyper.lookup.2.i64(
entry:
  %view = call ptr @llvm.hyper.lookup.2.i64(
      ptr %key, i64 8, ptr @identity, ptr @reduce)
  ret ptr %view
}

declare void @identity(ptr)
declare void @reduce(ptr, ptr)
declare void @llvm.reducer.register(i32, ptr, ptr)
declare ptr @llvm.hyper.lookup.0(ptr)
declare ptr @llvm.hyper.lookup.1(ptr, ptr)
declare ptr @llvm.hyper.lookup.2.i64(ptr, i64, ptr, ptr)
