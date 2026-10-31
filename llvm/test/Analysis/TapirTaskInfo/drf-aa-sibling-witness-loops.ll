; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=OFF,COMMON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=ON,COMMON

; Both loops are serial. Their independent induction variables describe the
; same input footprint only in the positive case. A same-base or bounding-box
; match must not overlook holes, byte widths, guards, or unknown trip counts.
; Output and input are independent arguments without noalias attributes.

; Distinct IVs both sweep all four doubles.
; COMMON-LABEL: Function: separate_iv_full_coverage:
; OFF-DAG: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; ON-DAG: NoAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; OFF-DAG: MayAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
; ON-DAG: NoAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
define void @separate_iv_full_coverage(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out.read = getelementptr double, ptr %output, i64 %i
  %old = load double, ptr %local.out.read
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; The sibling reads only half of the queried input footprint.
; COMMON-LABEL: Function: partial_coverage:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @partial_coverage(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 2
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; The sibling bounding interval contains the local input footprint but has
; holes. The single-double output may legally equal input+1: all sibling
; reads then miss the output, although the local input loop reads it.
; COMMON-LABEL: Function: strided_holes:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @strided_holes(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %scaled = mul nuw nsw i64 %j, 2
  %sibling.in = getelementptr double, ptr %input, i64 %scaled
  %w = load double, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 0
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; An equal-size footprint at a different offset is not coverage.
; COMMON-LABEL: Function: shifted_coverage:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @shifted_coverage(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %offset = add nuw nsw i64 %j, 4
  %sibling.in = getelementptr double, ptr %input, i64 %offset
  %w = load double, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; An unknown count may be zero or smaller than the local footprint.
; COMMON-LABEL: Function: unknown_witness_count:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @unknown_witness_count(ptr %output, ptr %input, i64 %n) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  %nonempty = icmp ugt i64 %n, 0
  br i1 %nonempty, label %witness.loop, label %witness.exit
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, %n
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; A syntactic witness loop that executes zero times is not evidence.
; COMMON-LABEL: Function: zero_witness_count:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @zero_witness_count(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br i1 false, label %witness.loop, label %witness.exit
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; A fixed positive loop count does not make a guarded load mandatory.
; COMMON-LABEL: Function: conditional_read_in_loop:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @conditional_read_in_loop(ptr %output, ptr %input, i1 %cond) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.latch ]
  br i1 %cond, label %witness.read, label %witness.latch
witness.read:
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  br label %witness.latch
witness.latch:
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; Four one-byte reads cannot cover four eight-byte input loads.
; COMMON-LABEL: Function: insufficient_byte_coverage:
; COMMON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
define void @insufficient_byte_coverage(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %sibling.in = getelementptr i8, ptr %input, i64 %j
  %w = load i8, ptr %sibling.in
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %local.out = getelementptr double, ptr %output, i64 %i
  store double 1.0, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; A small LU-like tile uses independent nested IVs in the two task bodies.
; COMMON-LABEL: Function: nested_rectangular_coverage:
; OFF-DAG: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; OFF-DAG: MayAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
; ON-DAG: NoAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; ON-DAG: NoAlias: {{.*}}%local.in, {{.*}}%local.out.read{{$}}
define void @nested_rectangular_coverage(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.outer
witness.outer:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.outer.latch ]
  br label %witness.inner
witness.inner:
  %k = phi i64 [ 0, %witness.outer ], [ %k.next, %witness.inner ]
  %sibling.in = getelementptr [4 x double], ptr %input, i64 %j, i64 %k
  %w = load double, ptr %sibling.in
  %k.next = add nuw nsw i64 %k, 1
  %witness.inner.more = icmp ult i64 %k.next, 4
  br i1 %witness.inner.more, label %witness.inner, label %witness.outer.latch
witness.outer.latch:
  %j.next = add nuw nsw i64 %j, 1
  %witness.outer.more = icmp ult i64 %j.next, 2
  br i1 %witness.outer.more, label %witness.outer, label %witness.exit
witness.exit:
  reattach within %sr, label %work
work:
  br label %local.outer
local.outer:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.outer.latch ]
  br label %local.inner
local.inner:
  %l = phi i64 [ 0, %local.outer ], [ %l.next, %local.inner ]
  %local.out.read = getelementptr [4 x double], ptr %output, i64 %i, i64 %l
  %old = load double, ptr %local.out.read
  %local.out = getelementptr [4 x double], ptr %output, i64 %i, i64 %l
  store double 1.0, ptr %local.out
  %local.in = getelementptr [4 x double], ptr %input, i64 %i, i64 %l
  %v = load double, ptr %local.in
  %l.next = add nuw nsw i64 %l, 1
  %local.inner.more = icmp ult i64 %l.next, 4
  br i1 %local.inner.more, label %local.inner, label %local.outer.latch
local.outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %local.outer.more = icmp ult i64 %i.next, 2
  br i1 %local.outer.more, label %local.outer, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
