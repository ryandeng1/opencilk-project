; RUN: opt < %s -aa-pipeline=basic-aa -passes='loop-mssa(licm)' -S | FileCheck %s

; A hyperobject lookup is invariant only within one registration lifetime.
; LICM may not reuse its result across a register/unregister pair for the same
; key, as happens when a Tapir loop is strip-mined into a serial chunk loop.

define void @same_key(ptr %out, i64 %n) {
; CHECK-LABEL: define void @same_key(
; CHECK: entry:
; CHECK-NOT: llvm.hyper.lookup
; CHECK: loop:
; CHECK: call void @llvm.reducer.register(i32 2, ptr %key, ptr @reduce)
; CHECK-NEXT: %view = call ptr @llvm.hyper.lookup.2.i64(ptr %key
; CHECK: call void @llvm.reducer.unregister(ptr %key)
entry:
  %key = alloca double, align 8
  br label %loop

loop:
  %iv = phi i64 [ 0, %entry ], [ %next, %loop ]
  store double 0.000000e+00, ptr %key, align 8
  call void @llvm.reducer.register(i32 2, ptr %key, ptr @reduce)
  %view = call ptr @llvm.hyper.lookup.2.i64(
      ptr %key, i64 8, ptr @identity, ptr @reduce)
  %old = load double, ptr %view, align 8
  %inc = fadd double %old, 1.000000e+00
  store double %inc, ptr %view, align 8
  store double %inc, ptr %out, align 8
  call void @llvm.reducer.unregister(ptr %key)
  %next = add nuw i64 %iv, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop

exit:
  ret void
}

; A lifetime operation on a provably different key is not a barrier.  Keep
; allowing LICM to hoist this lookup within key.b's registration lifetime.

define void @different_keys(ptr %out, i64 %n) {
; CHECK-LABEL: define void @different_keys(
; CHECK: entry:
; CHECK: call void @llvm.reducer.register(i32 2, ptr %key.b, ptr @reduce)
; CHECK: %view = call ptr @llvm.hyper.lookup.2.i64(ptr %key.b
; CHECK: loop:
; CHECK-NOT: llvm.hyper.lookup
; CHECK: call void @llvm.reducer.unregister(ptr %key.b)
entry:
  %key.a = alloca double, align 8
  %key.b = alloca double, align 8
  store double 0.000000e+00, ptr %key.b, align 8
  call void @llvm.reducer.register(i32 2, ptr %key.b, ptr @reduce)
  br label %loop

loop:
  %iv = phi i64 [ 0, %entry ], [ %next, %loop ]
  store double 0.000000e+00, ptr %key.a, align 8
  call void @llvm.reducer.register(i32 2, ptr %key.a, ptr @reduce)
  %view = call ptr @llvm.hyper.lookup.2.i64(
      ptr %key.b, i64 8, ptr @identity, ptr @reduce)
  %value = load double, ptr %view, align 8
  store double %value, ptr %out, align 8
  call void @llvm.reducer.unregister(ptr %key.a)
  %next = add nuw i64 %iv, 1
  %done = icmp eq i64 %next, %n
  br i1 %done, label %exit, label %loop

exit:
  call void @llvm.reducer.unregister(ptr %key.b)
  ret void
}

define internal void @identity(ptr %view) {
  store double 0.000000e+00, ptr %view, align 8
  ret void
}

define internal void @reduce(ptr %left, ptr %right) {
  %rhs = load double, ptr %right, align 8
  %lhs = load double, ptr %left, align 8
  %sum = fadd double %lhs, %rhs
  store double %sum, ptr %left, align 8
  ret void
}

declare ptr @llvm.hyper.lookup.2.i64(ptr, i64, ptr, ptr)
declare void @llvm.reducer.register(i32, ptr, ptr)
declare void @llvm.reducer.unregister(ptr)
