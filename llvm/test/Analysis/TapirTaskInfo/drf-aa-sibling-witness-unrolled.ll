; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=OFF,COMMON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=ON,COMMON

; A runtime-unrolled counted loop steps its phi through a chain of literal
; adds and tests a later value of the chain in the latch. The matcher must
; recover the real trip count: 8 trips of step 2 below cover input[0..16), the
; same bytes the sibling reads, so the pairs are NoAlias. With the bound at 32
; the leaf reads input[0..32), more than the sibling covers, so no fact.

; COMMON-LABEL: Function: unrolled_by_two:
; OFF-DAG: MayAlias: {{.*}}%in.a, {{.*}}%out.a{{$}}
; OFF-DAG: MayAlias: {{.*}}%in.b, {{.*}}%out.b{{$}}
; ON-DAG: NoAlias: {{.*}}%in.a, {{.*}}%out.a{{$}}
; ON-DAG: NoAlias: {{.*}}%in.a, {{.*}}%out.b{{$}}
; ON-DAG: NoAlias: {{.*}}%in.b, {{.*}}%out.a{{$}}
; ON-DAG: NoAlias: {{.*}}%in.b, {{.*}}%out.b{{$}}
define void @unrolled_by_two(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.ph, label %work.ph
witness.ph:
  br label %witness
witness:
  %j = phi i64 [ 0, %witness.ph ], [ %j.next, %witness ]
  %sibling.in = getelementptr i32, ptr %input, i64 %j
  %w = load i32, ptr %sibling.in
  %j.next = add i64 %j, 1
  %wc = icmp ne i64 %j.next, 16
  br i1 %wc, label %witness, label %witness.exit
witness.exit:
  reattach within %sr, label %work.ph
work.ph:
  br label %work
work:
  %i = phi i64 [ 0, %work.ph ], [ %i.next.1, %work ]
  %i.next = add i64 %i, 1
  %in.a = getelementptr i32, ptr %input, i64 %i
  %va = load i32, ptr %in.a
  %out.a = getelementptr i32, ptr %output, i64 %i
  store i32 %va, ptr %out.a
  %in.b = getelementptr i32, ptr %input, i64 %i.next
  %vb = load i32, ptr %in.b
  %out.b = getelementptr i32, ptr %output, i64 %i.next
  store i32 %vb, ptr %out.b
  %i.next.1 = add i64 %i.next, 1
  %c = icmp ne i64 %i.next.1, 16
  br i1 %c, label %work, label %work.exit
work.exit:
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: unrolled_reads_past_witness:
; COMMON-DAG: MayAlias: {{.*}}%in.a, {{.*}}%out.a{{$}}
; COMMON-DAG: MayAlias: {{.*}}%in.b, {{.*}}%out.b{{$}}
define void @unrolled_reads_past_witness(ptr %output, ptr %input) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.ph, label %work.ph
witness.ph:
  br label %witness
witness:
  %j = phi i64 [ 0, %witness.ph ], [ %j.next, %witness ]
  %sibling.in = getelementptr i32, ptr %input, i64 %j
  %w = load i32, ptr %sibling.in
  %j.next = add i64 %j, 1
  %wc = icmp ne i64 %j.next, 16
  br i1 %wc, label %witness, label %witness.exit
witness.exit:
  reattach within %sr, label %work.ph
work.ph:
  br label %work
work:
  %i = phi i64 [ 0, %work.ph ], [ %i.next.1, %work ]
  %i.next = add i64 %i, 1
  %in.a = getelementptr i32, ptr %input, i64 %i
  %va = load i32, ptr %in.a
  %out.a = getelementptr i32, ptr %output, i64 %i
  store i32 %va, ptr %out.a
  %in.b = getelementptr i32, ptr %input, i64 %i.next
  %vb = load i32, ptr %in.b
  %out.b = getelementptr i32, ptr %output, i64 %i.next
  store i32 %vb, ptr %out.b
  %i.next.1 = add i64 %i.next, 1
  %c = icmp ne i64 %i.next.1, 32
  br i1 %c, label %work, label %work.exit
work.exit:
  sync within %sr, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
