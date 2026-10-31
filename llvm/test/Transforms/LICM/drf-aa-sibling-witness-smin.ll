; RUN: opt -S %s -aa-pipeline=basic-aa,drf-aa -passes='loop-mssa(licm),verify' -enable-drf-aa | FileCheck %s --check-prefix=OFF
; RUN: opt -S %s -aa-pipeline=basic-aa,drf-aa -passes='loop-mssa(licm),verify' -enable-drf-aa -enable-drf-aa-sibling-witness | FileCheck %s --check-prefix=ON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=AAOFF
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefix=AAON

; Floyd-Warshall's unconditional min update becomes llvm.smin. The pure
; arithmetic intrinsic must not hide a guaranteed sibling read. With complete
; parallel coverage, both the output load and output store are disjoint from
; the input, and LICM can postpone the repeated output stores until loop exit.
; No source noalias attributes, scopes, or conditional write assumptions occur.

; AAOFF-LABEL: Function: min_with_sibling:
; AAOFF: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; AAON-LABEL: Function: min_with_sibling:
; AAON: NoAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; OFF-LABEL: define void @min_with_sibling(
; OFF: local.loop:
; OFF: store i32 %minimum, ptr %local.out
; OFF: br i1 %local.more, label %local.loop, label %join
; ON-LABEL: define void @min_with_sibling(
; ON: work:
; ON: load i32, ptr %local.out
; ON: local.loop:
; ON-NOT: load i32, ptr %local.out
; ON: call i32 @llvm.smin.i32
; ON-NOT: store i32 {{.*}}, ptr %local.out
; ON: br i1 %local.more, label %local.loop, label %join
; ON: join:
; ON: store i32 {{.*}}, ptr %local.out
; ON: sync within %sr, label %exit
define void @min_with_sibling(ptr %output, ptr %input, ptr %witness.result) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %acc = phi i32 [ 2147483647, %witness.preheader ], [ %acc.next, %witness.loop ]
  %sibling.in = getelementptr i32, ptr %input, i64 %j
  %w = load i32, ptr %sibling.in
  %acc.next = call i32 @llvm.smin.i32(i32 %acc, i32 %w)
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  store i32 %acc.next, ptr %witness.result
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %old = load i32, ptr %local.out
  %local.in = getelementptr i32, ptr %input, i64 %i
  %v = load i32, ptr %local.in
  %candidate = add i32 %v, 7
  %minimum = call i32 @llvm.smin.i32(i32 %old, i32 %candidate)
  store i32 %minimum, ptr %local.out
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; Accepting smin does not relax coverage: the sibling misses two input cells.
; The output can overlap one of those cells without creating a sibling race.
; AAOFF-LABEL: Function: min_partial_coverage:
; AAOFF: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; AAON-LABEL: Function: min_partial_coverage:
; AAON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; OFF-LABEL: define void @min_partial_coverage(
; OFF: local.loop:
; OFF: store i32 %minimum, ptr %local.out
; ON-LABEL: define void @min_partial_coverage(
; ON: local.loop:
; ON: store i32 %minimum, ptr %local.out
define void @min_partial_coverage(ptr %output, ptr %input, ptr %witness.result) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %acc = phi i32 [ 2147483647, %witness.preheader ], [ %acc.next, %witness.loop ]
  %sibling.in = getelementptr i32, ptr %input, i64 %j
  %w = load i32, ptr %sibling.in
  %acc.next = call i32 @llvm.smin.i32(i32 %acc, i32 %w)
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 2
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  store i32 %acc.next, ptr %witness.result
  reattach within %sr, label %work
work:
  %local.out = getelementptr i32, ptr %output, i64 0
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %old = load i32, ptr %local.out
  %local.in = getelementptr i32, ptr %input, i64 %i
  %v = load i32, ptr %local.in
  %candidate = add i32 %v, 7
  %minimum = call i32 @llvm.smin.i32(i32 %old, i32 %candidate)
  store i32 %minimum, ptr %local.out
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

; A min reduction alone cannot establish disjointness in a serial function.
; AAOFF-LABEL: Function: min_without_sibling:
; AAOFF: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; AAON-LABEL: Function: min_without_sibling:
; AAON: MayAlias: {{.*}}%local.in, {{.*}}%local.out{{$}}
; OFF-LABEL: define void @min_without_sibling(
; OFF: local.loop:
; OFF: store i32 %minimum, ptr %local.out
; ON-LABEL: define void @min_without_sibling(
; ON: local.loop:
; ON: store i32 %minimum, ptr %local.out
define void @min_without_sibling(ptr %output, ptr %input) {
entry:
  %local.out = getelementptr i32, ptr %output, i64 0
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %entry ], [ %i.next, %local.loop ]
  %old = load i32, ptr %local.out
  %local.in = getelementptr i32, ptr %input, i64 %i
  %v = load i32, ptr %local.in
  %candidate = add i32 %v, 7
  %minimum = call i32 @llvm.smin.i32(i32 %old, i32 %candidate)
  store i32 %minimum, ptr %local.out
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
declare i32 @llvm.smin.i32(i32, i32)
