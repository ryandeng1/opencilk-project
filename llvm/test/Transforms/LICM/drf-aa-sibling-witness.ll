; RUN: opt -S %s -aa-pipeline=basic-aa,drf-aa -passes='loop-mssa(licm),verify' -enable-drf-aa | FileCheck %s --check-prefix=OFF
; RUN: opt -S %s -aa-pipeline=basic-aa,drf-aa -passes='loop-mssa(licm),verify' -enable-drf-aa -enable-drf-aa-sibling-witness | FileCheck %s --check-prefix=ON

; The serial accumulation loop cannot sink its output stores past an input
; load unless output/input overlap is excluded. A parallel sibling reads the
; complete input footprint under an independent IV. Its read is observable
; through the reduction result, so LICM cannot delete the witness as dead code.
; There is no scoped-noalias metadata or source-level noalias parameter here.
; Both the output load and store participate in the promotion candidate.

; OFF-LABEL: define void @promote_with_sibling_witness(
; OFF: work:
; OFF: load double, ptr %local.out
; OFF: local.loop:
; OFF: store double %sum, ptr %local.out
; OFF: br i1 %local.more, label %local.loop, label %join
;
; ON-LABEL: define void @promote_with_sibling_witness(
; ON: work:
; ON: load double, ptr %local.out
; ON: local.loop:
; ON-NOT: load double, ptr %local.out
; ON: phi double
; ON-NOT: store double {{.*}}, ptr %local.out
; ON: br i1 %local.more, label %local.loop, label %join
; ON: join:
; ON: store double {{.*}}, ptr %local.out
; ON: sync within %sr, label %exit
define void @promote_with_sibling_witness(ptr %output, ptr %input, ptr %witness.result) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.loop ]
  %acc = phi double [ 0.0, %witness.preheader ], [ %acc.next, %witness.loop ]
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  %acc.next = fadd double %acc, %w
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  store double %acc.next, ptr %witness.result
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 0
  br label %local.loop
local.loop:
  %i = phi i64 [ 0, %work ], [ %i.next, %local.loop ]
  %old = load double, ptr %local.out
  %local.in = getelementptr double, ptr %input, i64 %i
  %v = load double, ptr %local.in
  %sum = fadd double %old, %v
  store double %sum, ptr %local.out
  %i.next = add nuw nsw i64 %i, 1
  %local.more = icmp ult i64 %i.next, 4
  br i1 %local.more, label %local.loop, label %join
join:
  sync within %sr, label %exit
exit:
  ret void
}

declare token @llvm.syncregion.start()
