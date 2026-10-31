; RUN: opt -passes=drf-scoped-noalias -enable-drf-aa \
; RUN:   -enable-drf-aa-task-scope-metadata=false \
; RUN:   -enable-drf-aa-proven-pair-metadata=false -S %s | \
; RUN:   FileCheck %s

; The function attachment identifies exactly the alias-scope domains owned by
; this pass.  A later invocation removes operands from those domains and the
; legacy done marker, while preserving unrelated scoped-noalias metadata.
;
; CHECK-NOT: drfaa.generated.alias.scope.domains
; CHECK-NOT: drfaa.proven.pair.noalias.done
; CHECK-LABEL: define void @stale(
; CHECK-NOT: !drfaa
; CHECK: %v = load i32, ptr %p, align 4, !alias.scope [[USER_LIST:![0-9]+]], !noalias [[USER_LIST]]
; CHECK: [[USER_LIST]] = !{[[USER_SCOPE:![0-9]+]]}
; CHECK: [[USER_SCOPE]] = distinct !{[[USER_SCOPE]], [[USER_DOMAIN:![0-9]+]], !"user_scope"}
; CHECK: [[USER_DOMAIN]] = distinct !{[[USER_DOMAIN]], !"user_domain"}
; CHECK-NOT: stale_generated
define void @stale(ptr %p) !drfaa.generated.alias.scope.domains !0 !drfaa.proven.pair.noalias.done !6 {
entry:
  %v = load i32, ptr %p, !alias.scope !5, !noalias !5
  ret void
}

!0 = !{!1}
!1 = distinct !{!1, !"stale_generated_domain"}
!2 = distinct !{!2, !1, !"stale_generated_scope"}
!3 = distinct !{!3, !"user_domain"}
!4 = distinct !{!4, !3, !"user_scope"}
!5 = !{!2, !4}
!6 = !{}
