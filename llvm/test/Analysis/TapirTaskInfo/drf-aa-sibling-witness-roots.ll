; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=OFF,COMMON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=ON,COMMON

; An access addressed by its root itself (the argument, or a pointer computed
; before the phase) has no in-leaf pointer instruction. The fact is still
; answered as long as the other side is defined inside the leaf; a pair of two
; roots is never answered, because those addresses may coincide on a path that
; skips the phase.

; COMMON-LABEL: Function: argument_root:
; OFF: MayAlias: {{.*}}%input, {{.*}}%local.out{{$}}
; ON: NoAlias: {{.*}}%input, {{.*}}%local.out{{$}}
; COMMON: MayAlias: {{.*}}%input, {{.*}}%output{{$}}
define void @argument_root(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %w = load i32, ptr %input
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  store i32 1, ptr %local.out
  store i32 2, ptr %output
  %v = load i32, ptr %input
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: prephase_root:
; OFF: MayAlias: {{.*}}%in.off, {{.*}}%local.out{{$}}
; ON: NoAlias: {{.*}}%in.off, {{.*}}%local.out{{$}}
define void @prephase_root(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  %in.off = getelementptr i32, ptr %input, i64 16
  detach within %sr, label %witness, label %work
witness:
  %w = load i32, ptr %in.off
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  store i32 1, ptr %local.out
  %v = load i32, ptr %in.off
  sync within %sr, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
