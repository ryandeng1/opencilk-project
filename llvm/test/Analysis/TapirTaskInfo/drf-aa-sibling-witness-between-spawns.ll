; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=OFF,COMMON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=ON,COMMON

; Ordinary loads and stores between two spawns belong to no leaf and cannot
; stop the later spawns from executing, so the phase is still a proof. A call
; between the spawns might not return, so it still ends the phase.

; COMMON-LABEL: Function: accesses_between_spawns:
; OFF: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; ON: NoAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @accesses_between_spawns(ptr %output, ptr %input, ptr %other) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %between
witness:
  %sibling.in = getelementptr i32, ptr %input, i64 0
  %w = load i32, ptr %sibling.in
  reattach within %sr, label %between
between:
  %o = load i32, ptr %other
  %o1 = add i32 %o, 1
  store i32 %o1, ptr %other
  detach within %sr, label %second, label %work
second:
  %s = load i32, ptr %other
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  store i32 1, ptr %local.out
  %local.in = getelementptr i32, ptr %input, i64 0
  %v = load i32, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: call_between_spawns:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @call_between_spawns(ptr %output, ptr %input, ptr %other) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %between
witness:
  %sibling.in = getelementptr i32, ptr %input, i64 0
  %w = load i32, ptr %sibling.in
  reattach within %sr, label %between
between:
  call void @ext()
  detach within %sr, label %second, label %work
second:
  %s = load i32, ptr %other
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  store i32 1, ptr %local.out
  %local.in = getelementptr i32, ptr %input, i64 0
  %v = load i32, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

declare void @ext()
declare token @llvm.syncregion.start()
