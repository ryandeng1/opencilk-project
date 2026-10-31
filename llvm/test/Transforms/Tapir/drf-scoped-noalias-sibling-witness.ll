; RUN: opt -S %s -passes=drf-scoped-noalias -enable-drf-aa -enable-drf-aa-sibling-witness -enable-drf-aa-task-scope-metadata=false -enable-drf-aa-proven-pair-metadata=false | FileCheck %s --check-prefixes=MD
; RUN: opt -S %s -passes=drf-scoped-noalias,drf-scoped-noalias -enable-drf-aa -enable-drf-aa-sibling-witness -enable-drf-aa-task-scope-metadata=false -enable-drf-aa-proven-pair-metadata=false | FileCheck %s --check-prefixes=MD,TWICE
; RUN: opt -disable-output %s -passes=drf-scoped-noalias,aa-eval -aa-pipeline=scoped-noalias-aa -enable-drf-aa -enable-drf-aa-sibling-witness -evaluate-aa-metadata -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=AA
; RUN: opt -disable-output %s -passes=drf-scoped-noalias,aa-eval -aa-pipeline=scoped-noalias-aa -enable-drf-aa -enable-drf-aa-sibling-witness -enable-drf-aa-sibling-witness-metadata=false -evaluate-aa-metadata -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=NOMD

; The sibling-witness pairs become scoped-noalias metadata on the two leaf
; accesses, including an input read through the bare argument. The relation
; then lives on the instructions: ScopedNoAliasAA alone answers NoAlias, and a
; second run of the pass adds no duplicate scopes.

; MD-LABEL: define void @argument_root(
; MD: store i32 1, ptr %local.out, align 4, !alias.scope ![[OUTSCOPE:[0-9]+]]
; MD: load i32, ptr %input, align 4, !noalias ![[OUTSCOPE]]
; MD-DAG: ![[OUTSCOPE]] = !{![[SCOPE:[0-9]+]]}
; MD-DAG: ![[SCOPE]] = distinct !{![[SCOPE]], ![[DOM:[0-9]+]], !"drfaa_sibling_0"}
; MD-DAG: ![[DOM]] = distinct !{![[DOM]], !"drfaa_siblingdom_argument_root"}
; TWICE-NOT: !"drfaa_sibling_1"

; AA: Function: argument_root:
; AA: NoAlias: %v = load i32, ptr %input{{.*}} <-> store i32 1, ptr %local.out
; NOMD: Function: argument_root:
; NOMD: MayAlias: %v = load i32, ptr %input{{.*}} <-> store i32 1, ptr %local.out
define void @argument_root(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %w = load i32, ptr %input, align 4
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  store i32 1, ptr %local.out, align 4
  %v = load i32, ptr %input, align 4
  sync within %sr, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
