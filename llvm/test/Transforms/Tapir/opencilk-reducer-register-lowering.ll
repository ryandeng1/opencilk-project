; RUN: opt < %s -passes=tapir2target -tapir-target=opencilk \
; RUN:   -use-opencilk-runtime-bc=false -debug-abi-calls -S | FileCheck %s

; Reducer registration has a different signature from its runtime call, so it
; must be replaced rather than retargeted in place.  In particular, do not
; leave the intrinsic behind for a later Tapir-lowering invocation to process.

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define void @lower_register_variants(ptr %key, ptr %callback) {
; CHECK-LABEL: define void @lower_register_variants(
; CHECK: entry:
; CHECK-NEXT: call void @__cilkrts_reducer_register_0(ptr %key)
; CHECK-NEXT: call void @__cilkrts_reducer_register_1(ptr %key, ptr %callback)
; CHECK-NEXT: call void @__cilkrts_reducer_register_2(ptr %key, ptr %callback)
; CHECK-NEXT: ret void
entry:
  call void @llvm.reducer.register(i32 0, ptr %key, ptr poison)
  call void @llvm.reducer.register(i32 1, ptr %key, ptr %callback)
  call void @llvm.reducer.register(i32 2, ptr %key, ptr %callback)
  ret void
}

declare void @llvm.reducer.register(i32, ptr, ptr)
