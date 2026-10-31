; RUN: opt -disable-output %s -aa-pipeline=basic-aa,drf-aa -passes='aa-eval,gvn,verify' -enable-drf-aa -enable-drf-aa-sibling-witness
;
; First AA-eval queries the sibling witness while witness.latch is the loop's
; exiting block. GVN then merges that block into witness.loop and queries AA
; again while optimizing the continuation loads. The witness matcher must use
; the current IR, not a cached ScalarEvolution backedge count referencing the
; deleted exiting block. This used to assert on a poisoned BasicBlock handle
; in ScalarEvolution::BackedgeTakenInfo::getExact.
;
; Keep the output GEP nonzero: folding it to the function argument would make
; the context-free witness query abstain, accidentally hiding the crash.

define void @gvn_deletes_exiting_block(ptr %output, ptr %input, ptr %witness.result) {
entry:
  %sr = call token @llvm.syncregion.start()
  detach within %sr, label %witness.preheader, label %work
witness.preheader:
  br label %witness.loop
witness.loop:
  %j = phi i64 [ 0, %witness.preheader ], [ %j.next, %witness.latch ]
  %acc = phi double [ 0.0, %witness.preheader ], [ %acc.next, %witness.latch ]
  %sibling.in = getelementptr double, ptr %input, i64 %j
  %w = load double, ptr %sibling.in
  %acc.next = fadd double %acc, %w
  br label %witness.latch
witness.latch:
  %j.next = add nuw nsw i64 %j, 1
  %witness.more = icmp ult i64 %j.next, 4
  br i1 %witness.more, label %witness.loop, label %witness.exit
witness.exit:
  store double %acc.next, ptr %witness.result
  reattach within %sr, label %work
work:
  %local.out = getelementptr double, ptr %output, i64 1
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
