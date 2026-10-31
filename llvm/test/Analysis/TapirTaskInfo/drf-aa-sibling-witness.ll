; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=OFF,COMMON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=ON,COMMON

; All target pairs use distinct pointer arguments. BasicAA alone cannot prove
; their disjointness. The target accesses are in the same serial strand; only
; the third access in a guaranteed parallel sibling supplies the race witness.
;
; Separate zero-offset GEPs give each tested load/store its own representative
; access, including the output load whose disjointness is inherited from a
; guaranteed write to the same location.

; COMMON-LABEL: Function: scalar_witness:
; OFF: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; ON: NoAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @scalar_witness(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: covered_output_load:
; OFF-DAG: MayAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
; OFF-DAG: MayAlias: {{.*}}%local.in, {{.*}}%local.out.write{{$}}
; ON-DAG: NoAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
; ON-DAG: NoAlias: {{.*}}%local.in, {{.*}}%local.out.write{{$}}
define void @covered_output_load(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out.read = getelementptr double, ptr %output, i64 0
  %old = load double, ptr %local.out.read
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  %sum = fadd double %old, %v
  %local.out.write = getelementptr double, ptr %output, i64 0
  store double %sum, ptr %local.out.write
  sync within %sr, label %exit
exit:
  ret void
}

; A read-only output has no forbidden write/read overlap to transfer.
; COMMON-LABEL: Function: no_output_write:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @no_output_write(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  %old = load double, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; The output write does not cover this output load's bytes.
; COMMON-LABEL: Function: uncovered_output_load:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
define void @uncovered_output_load(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out.write = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out.write
  %local.out.read = getelementptr double, ptr %output, i64 1
  %old = load double, ptr %local.out.read
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; The sibling exists but its read is conditional.
; COMMON-LABEL: Function: conditional_witness_read:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @conditional_witness_read(ptr %output, ptr %input, i1 %cond) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  br i1 %cond, label %read, label %witness.exit
read:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  br label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; The target accesses also execute on the path that never spawns the sibling.
; COMMON-LABEL: Function: conditional_spawn:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @conditional_spawn(ptr %output, ptr %input, i1 %cond) {
entry:
  %sr = call token @llvm.syncregion.start()
  br i1 %cond, label %spawn, label %work
spawn:
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; A write that might not happen cannot justify a read/read noalias fact.
; COMMON-LABEL: Function: conditional_output_write:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
define void @conditional_output_write(ptr %output, ptr %input, i1 %cond) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out.read = getelementptr double, ptr %output, i64 0
  %old = load double, ptr %local.out.read
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  br i1 %cond, label %write, label %done
write:
  %local.out.write = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out.write
  br label %done
done:
  sync within %sr, label %exit
exit:
  ret void
}

; The sibling's read uses a different, possibly unrelated input base.
; COMMON-LABEL: Function: different_input_base:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @different_input_base(ptr %output, ptr %input, ptr %other) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %other, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; A witness before the sync cannot prove disjointness in the next serial phase.
; COMMON-LABEL: Function: after_sync:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @after_sync(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %join
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %join
join:
  sync within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  ret void
}

; COMMON-LABEL: Function: no_sibling:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @no_sibling(ptr %output, ptr %input) {
entry:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  ret void
}

; Non-ordinary accesses must not be used as witness or local write evidence.
; COMMON-LABEL: Function: volatile_witness:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @volatile_witness(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load volatile double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: atomic_witness:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @atomic_witness(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr i64, ptr %input, i64 0
  %w = load atomic i64, ptr %sibling.in monotonic, align 8
  reattach within %sr, label %work
work:
  %local.out = getelementptr i64, ptr %output, i64 0
  store i64 1, ptr %local.out
  %local.in = getelementptr i64, ptr %input, i64 0
  %v = load i64, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: atomic_output_write:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @atomic_output_write(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr i64, ptr %input, i64 0
  %w = load i64, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr i64, ptr %output, i64 0
  store atomic i64 1, ptr %local.out monotonic, align 8
  %local.in = getelementptr i64, ptr %input, i64 0
  %v = load i64, ptr %local.in
  sync within %sr, label %exit
exit:
  ret void
}

; The peeled path supplies a witness, but the generic serial branch does not.
; Separate access instructions are essential: the function arguments themselves
; never acquire unconditional noalias attributes.
; COMMON-LABEL: Function: generic_serial_branch:
; COMMON: MayAlias: {{.*}}%serial.in, {{.*}}%serial.out{{$}}
define void @generic_serial_branch(ptr %output, ptr %input, i1 %peeled) {
entry:
  %sr = call token @llvm.syncregion.start()
  br i1 %peeled, label %spawn, label %serial
spawn:
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %peeled.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %peeled.out
  %peeled.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %peeled.in
  sync within %sr, label %exit
serial:
  %serial.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %serial.out
  %serial.in = getelementptr double, ptr %input, i64 0
  %sv = load double, ptr %serial.in
  br label %exit
exit:
  ret void
}

; The target leaf can be the detached child rather than the continuation.
; COMMON-LABEL: Function: detached_leaf_witness:
; OFF: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; ON: NoAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @detached_leaf_witness(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %work, label %witness
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 0
  %v = load double, ptr %local.in
  reattach within %sr, label %witness
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  sync within %sr, label %exit
exit:
  ret void
}

; Both read-only inputs can legally alias each other. The output exclusion
; does not turn three pointer arguments into mutually disjoint allocations.
; COMMON-LABEL: Function: readonly_inputs_may_alias:
; OFF-DAG: MayAlias: {{.*}}%local.a, {{.*}}%local.out{{$}}
; OFF-DAG: MayAlias: {{.*}}%local.b, {{.*}}%local.out{{$}}
; ON-DAG: NoAlias: {{.*}}%local.a, {{.*}}%local.out{{$}}
; ON-DAG: NoAlias: {{.*}}%local.b, {{.*}}%local.out{{$}}
; COMMON: MayAlias: {{.*}}%local.a, {{.*}}%local.b{{$}}
define void @readonly_inputs_may_alias(ptr %output, ptr %a, ptr %b) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness, label %work
witness:
  %sibling.a = getelementptr double, ptr %a, i64 0
  %wa = load double, ptr %sibling.a
  %sibling.b = getelementptr double, ptr %b, i64 0
  %wb = load double, ptr %sibling.b
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.a = getelementptr double, ptr %a, i64 0
  %va = load double, ptr %local.a
  %local.b = getelementptr double, ptr %b, i64 0
  %vb = load double, ptr %local.b
  sync within %sr, label %exit
exit:
  ret void
}

; A context-free query on arguments also used by a serial path must not acquire
; the stronger property of access instructions in the peeled path.
; COMMON-LABEL: Function: arguments_used_by_serial_branch:
; COMMON: MayAlias: {{.*}}%input, {{.*}}%output{{$}}
define void @arguments_used_by_serial_branch(ptr %output, ptr %input, i1 %peeled) {
entry:
  %sr = call token @llvm.syncregion.start()
  br i1 %peeled, label %spawn, label %serial
spawn:
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %input, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  store double 1.0, ptr %output
  %v = load double, ptr %input
  sync within %sr, label %exit
serial:
  store double 1.0, ptr %output
  %sv = load double, ptr %input
  br label %exit
exit:
  ret void
}

; This initial proof deliberately rejects a phase repeated in an enclosing
; serial loop: one iteration's separation must not become a context-free
; noalias assertion spanning different dynamic phase instances.
; COMMON-LABEL: Function: repeated_serial_phase:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @repeated_serial_phase(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  br label %outer
outer:
  %i = phi i64 [ 0, %entry ], [ %next, %latch ]
  %out.base = getelementptr double, ptr %output, i64 %i
  %in.base = getelementptr double, ptr %input, i64 %i
  detach within %sr, label %witness, label %work
witness:
  %sibling.in = getelementptr double, ptr %in.base, i64 0
  %w = load double, ptr %sibling.in
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %out.base, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %in.base, i64 0
  %v = load double, ptr %local.in
  sync within %sr, label %latch
latch:
  %next = add nuw nsw i64 %i, 1
  %more = icmp ult i64 %next, 4
  br i1 %more, label %outer, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
