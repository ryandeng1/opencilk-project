; RUN: opt -S -passes='loop-simplify,loop-rotate,loop-versioning' -aa-pipeline=basic-aa -enable-drf-equality-versioning %s | FileCheck %s

; A Tapir-derived loop with lockstep read-modify-write access to a[i] and read
; access to b[i].  If a == b, each iteration aliases only its own lane, which is
; race-free and must take the original clone.  Any shifted overlap would create a
; cross-iteration race, so under DRF the non-equal case is a noalias clone.

target datalayout = "e-p:64:64"

; CHECK-LABEL: define void @accumulate(
; CHECK: for.body.lver.check:
; CHECK: %[[DIFF:.*]] = sub i64
; CHECK-NEXT: %drf.eq.check = icmp eq i64 %[[DIFF]], 0
; CHECK-NEXT: br i1 %drf.eq.check, label %for.body.ph.lver.orig, label %for.body.ph
; CHECK-NOT: memcheck.conflict
; CHECK-NOT: bound0
; CHECK: %old = load double, ptr %pa, align 8, !alias.scope ![[A_SCOPE:[0-9]+]], !noalias ![[B_SCOPE:[0-9]+]]
; CHECK: %x = load double, ptr %pb, align 8, !alias.scope ![[B_SCOPE]]
; CHECK: store double %sum, ptr %pa, align 8, !alias.scope ![[A_SCOPE]], !noalias ![[B_SCOPE]]
define void @accumulate(ptr %a, ptr %b, i64 %n) {
entry:
  %cmp0 = icmp sgt i64 %n, 0
  br i1 %cmp0, label %for.body, label %exit

for.body:
  %i = phi i64 [ 0, %entry ], [ %inc, %for.body ]
  %pa = getelementptr inbounds double, ptr %a, i64 %i
  %old = load double, ptr %pa, align 8
  %pb = getelementptr inbounds double, ptr %b, i64 %i
  %x = load double, ptr %pb, align 8
  %sum = fadd double %old, %x
  store double %sum, ptr %pa, align 8
  %inc = add nuw nsw i64 %i, 1
  %done = icmp eq i64 %inc, %n
  br i1 %done, label %exit, label %for.body, !llvm.loop !0

exit:
  ret void
}

!0 = distinct !{!0, !1, !2}
!1 = !{!"llvm.loop.fromtapirloop"}
!2 = !{!"llvm.loop.mustprogress"}
