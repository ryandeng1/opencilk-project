; RUN: opt -disable-output -passes='early-cse<memssa>' \
; RUN:   -enable-drf-aa -enable-drf-loop-optimizations %s

; DRF MemorySSA must remain inert in a serial function.  In particular, the
; argmem location below is ConstantData and has no LLVM use-list.
define void @serial_constant_data(ptr %p) #0 {
entry:
  store i8 0, ptr %p
  call void @read_location(ptr null)
  ret void
}

; Keep the ConstantData guard independent of the serial-function fast path by
; posing the same query in a function whose task forest is non-serial.
define void @tapir_constant_data(ptr %p) #0 {
entry:
  %syncreg = call token @llvm.syncregion.start()
  detach within %syncreg, label %detached, label %continue

detached:
  call void @use()
  reattach within %syncreg, label %continue

continue:
  store i8 0, ptr %p
  call void @read_location(ptr null)
  ret void
}

declare void @read_location(ptr) #1
declare void @use()
declare token @llvm.syncregion.start() #2

attributes #0 = { "null-pointer-is-valid"="true" }
attributes #1 = {
  memory(argmem: read)
  "null-pointer-is-valid"="true"
}
attributes #2 = { nounwind memory(none) }
