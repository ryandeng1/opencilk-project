; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=OFF,COMMON
; RUN: opt -disable-output %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -enable-drf-aa-sibling-witness -print-all-alias-modref-info 2>&1 | FileCheck %s --check-prefixes=ON,COMMON

; An index clamped with a min intrinsic is evaluated exactly per instance.
; The leaf reads input[min(k, 3)] for k = 0..7, i.e. input[0..4); the sibling
; reads input[0..4) in full, so the pair is NoAlias. In the second function
; the sibling reads only input[0..3) and the clamp lets the leaf reach
; input[3], so no fact.

; COMMON-LABEL: Function: clamp_covered:
; OFF: MayAlias: {{.*}}%in.k, {{.*}}%out.k{{$}}
; ON: NoAlias: {{.*}}%in.k, {{.*}}%out.k{{$}}
define void @clamp_covered(ptr %output, ptr %input) {
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
  %wc = icmp ne i64 %j.next, 4
  br i1 %wc, label %witness, label %witness.exit
witness.exit:
  reattach within %sr, label %work.ph
work.ph:
  br label %work
work:
  %k = phi i64 [ 0, %work.ph ], [ %k.next, %work ]
  %c = call i64 @llvm.smin.i64(i64 %k, i64 3)
  %in.k = getelementptr i32, ptr %input, i64 %c
  %v = load i32, ptr %in.k
  %out.k = getelementptr i32, ptr %output, i64 %k
  store i32 %v, ptr %out.k
  %k.next = add i64 %k, 1
  %kc = icmp ne i64 %k.next, 8
  br i1 %kc, label %work, label %work.exit
work.exit:
  sync within %sr, label %exit
exit:
  ret void
}

; COMMON-LABEL: Function: clamp_uncovered:
; COMMON: MayAlias: {{.*}}%in.k, {{.*}}%out.k{{$}}
define void @clamp_uncovered(ptr %output, ptr %input) {
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
  %wc = icmp ne i64 %j.next, 3
  br i1 %wc, label %witness, label %witness.exit
witness.exit:
  reattach within %sr, label %work.ph
work.ph:
  br label %work
work:
  %k = phi i64 [ 0, %work.ph ], [ %k.next, %work ]
  %c = call i64 @llvm.smin.i64(i64 %k, i64 3)
  %in.k = getelementptr i32, ptr %input, i64 %c
  %v = load i32, ptr %in.k
  %out.k = getelementptr i32, ptr %output, i64 %k
  store i32 %v, ptr %out.k
  %k.next = add i64 %k, 1
  %kc = icmp ne i64 %k.next, 8
  br i1 %kc, label %work, label %work.exit
work.exit:
  sync within %sr, label %exit
exit:
  ret void
}

declare i64 @llvm.smin.i64(i64, i64)
declare token @llvm.syncregion.start()
