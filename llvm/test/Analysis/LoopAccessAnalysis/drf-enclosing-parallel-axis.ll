; RUN: opt -passes='print<access-info>' -disable-output < %s 2>&1 | FileCheck %s --check-prefix=BASE
; RUN: opt -passes='print<access-info>' -disable-output -aa-pipeline=drf-aa -enable-drf-aa -enable-drf-laa-check-elision -stats < %s 2>&1 | FileCheck %s --check-prefix=DRF
;
; A varying inner-loop trip domain does not guarantee that the same coordinate
; exists in a sibling Tapir iteration. Keep the ordinary runtime check.
; BASE-LABEL: function 'nested_tri':
; BASE: Memory dependences are safe with run-time checks
; BASE: Check 0:
; DRF-LABEL: function 'nested_tri':
; DRF: Memory dependences are safe with run-time checks
; DRF: Check 0:
;
; A conditionally executed invariant-side access is not a replicated witness.
; BASE-LABEL: function 'nested_cond':
; BASE: Memory dependences are safe with run-time checks
; BASE: Check 0:
; DRF-LABEL: function 'nested_cond':
; DRF: Memory dependences are safe with run-time checks
; DRF: Check 0:
;
; SCEV cannot recover the outer recurrence through the opaque Rows[i] load.
; The scoped LAA query may still recognize that pointer as varying across the
; enclosing Tapir loop, while c[j] has a replicated inner-loop schedule.
; BASE-LABEL: function 'pointer_table':
; BASE: Memory dependences are safe with run-time checks
; BASE: Check 0:
; DRF-LABEL: function 'pointer_table':
; DRF: Memory dependences are safe{{$}}
; DRF-NOT: Check 0:
;
; The same proof must run before an indirect store poisons CanDoRT. Every
; runtime-check edge incident to the uncomputable store is discharged here.
; BASE-LABEL: function 'pointer_table_indirect':
; BASE: Report: cannot identify array bounds
; DRF-LABEL: function 'pointer_table_indirect':
; DRF: Memory dependences are safe{{$}}
; DRF-NOT: cannot identify array bounds
;
; DRF: {{[1-9][0-9]*}} drf-aa-result - Number of loop-scoped DRF-AA proofs using an enclosing parallel axis
; DRF: {{[1-9][0-9]*}} loop-accesses - Number of LAA alias-set bounds failures rescued by DRF
; DRF: {{[1-9][0-9]*}} loop-accesses - Number of uncomputable LAA accesses discharged by DRF

source_filename = "drf-enclosing-parallel-axis.ll"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local void @nested_tri(ptr noundef %a, ptr noundef %c, i64 noundef %n) #0 {
entry:
  %syncreg = call token @llvm.syncregion.start()
  %cmp = icmp slt i64 0, %n
  br i1 %cmp, label %pfor.ph, label %pfor.end

pfor.ph:                                          ; preds = %entry
  %sub = sub nsw i64 %n, 0
  br label %pfor.cond

pfor.cond:                                        ; preds = %pfor.inc, %pfor.ph
  %__begin.0 = phi i64 [ 0, %pfor.ph ], [ %inc5, %pfor.inc ]
  %add = add nsw i64 0, %__begin.0
  detach within %syncreg, label %pfor.body, label %pfor.inc

pfor.body:                                        ; preds = %pfor.cond
  br label %for.cond

for.cond:                                         ; preds = %for.body, %pfor.body
  %j.0 = phi i64 [ 0, %pfor.body ], [ %inc, %for.body ]
  %add1 = add nsw i64 %add, 2
  %cmp2 = icmp slt i64 %j.0, %add1
  br i1 %cmp2, label %for.body, label %pfor.preattach

for.body:                                         ; preds = %for.cond
  %arrayidx = getelementptr inbounds double, ptr %c, i64 %j.0
  %0 = load double, ptr %arrayidx, align 8
  %mul = mul nsw i64 %add, %n
  %add3 = add nsw i64 %mul, %j.0
  %arrayidx4 = getelementptr inbounds double, ptr %a, i64 %add3
  store double %0, ptr %arrayidx4, align 8
  %inc = add nsw i64 %j.0, 1
  br label %for.cond, !llvm.loop !6

pfor.preattach:                                   ; preds = %for.cond
  reattach within %syncreg, label %pfor.inc

pfor.inc:                                         ; preds = %pfor.preattach, %pfor.cond
  %inc5 = add nsw i64 %__begin.0, 1
  %cmp6 = icmp slt i64 %inc5, %sub
  br i1 %cmp6, label %pfor.cond, label %pfor.cond.cleanup, !llvm.loop !8

pfor.cond.cleanup:                                ; preds = %pfor.inc
  sync within %syncreg, label %pfor.end

pfor.end:                                         ; preds = %pfor.cond.cleanup, %entry
  ret void
}

; Function Attrs: nounwind willreturn memory(argmem: readwrite)
declare token @llvm.syncregion.start() #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @nested_cond(ptr noundef %a, ptr noundef %c, i64 noundef %n, i64 noundef %m) #0 {
entry:
  %syncreg = call token @llvm.syncregion.start()
  %cmp = icmp slt i64 0, %n
  br i1 %cmp, label %pfor.ph, label %pfor.end

pfor.ph:                                          ; preds = %entry
  %sub = sub nsw i64 %n, 0
  br label %pfor.cond

pfor.cond:                                        ; preds = %pfor.inc, %pfor.ph
  %__begin.0 = phi i64 [ 0, %pfor.ph ], [ %inc4, %pfor.inc ]
  %add = add nsw i64 0, %__begin.0
  detach within %syncreg, label %pfor.body, label %pfor.inc

pfor.body:                                        ; preds = %pfor.cond
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %pfor.body
  %j.0 = phi i64 [ 0, %pfor.body ], [ %inc, %for.inc ]
  %cmp1 = icmp slt i64 %j.0, %m
  br i1 %cmp1, label %for.body, label %pfor.preattach

for.body:                                         ; preds = %for.cond
  %and = and i64 %j.0, 1
  %tobool = icmp ne i64 %and, 0
  br i1 %tobool, label %if.then, label %for.inc

if.then:                                          ; preds = %for.body
  %arrayidx = getelementptr inbounds double, ptr %c, i64 %j.0
  %0 = load double, ptr %arrayidx, align 8
  %mul = mul nsw i64 %add, %m
  %add2 = add nsw i64 %mul, %j.0
  %arrayidx3 = getelementptr inbounds double, ptr %a, i64 %add2
  store double %0, ptr %arrayidx3, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body, %if.then
  %inc = add nsw i64 %j.0, 1
  br label %for.cond, !llvm.loop !10

pfor.preattach:                                   ; preds = %for.cond
  reattach within %syncreg, label %pfor.inc

pfor.inc:                                         ; preds = %pfor.preattach, %pfor.cond
  %inc4 = add nsw i64 %__begin.0, 1
  %cmp5 = icmp slt i64 %inc4, %sub
  br i1 %cmp5, label %pfor.cond, label %pfor.cond.cleanup, !llvm.loop !11

pfor.cond.cleanup:                                ; preds = %pfor.inc
  sync within %syncreg, label %pfor.end

pfor.end:                                         ; preds = %pfor.cond.cleanup, %entry
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @pointer_table(ptr noundef %rows, ptr noundef %c, i64 noundef %n, i64 noundef %m) #0 {
entry:
  %syncreg = call token @llvm.syncregion.start()
  %cmp = icmp slt i64 0, %n
  br i1 %cmp, label %pfor.ph, label %pfor.end

pfor.ph:                                          ; preds = %entry
  %sub = sub nsw i64 %n, 0
  br label %pfor.cond

pfor.cond:                                        ; preds = %pfor.inc, %pfor.ph
  %__begin.0 = phi i64 [ 0, %pfor.ph ], [ %inc4, %pfor.inc ]
  %add = add nsw i64 0, %__begin.0
  detach within %syncreg, label %pfor.body, label %pfor.inc

pfor.body:                                        ; preds = %pfor.cond
  %arrayidx = getelementptr inbounds ptr, ptr %rows, i64 %add
  %0 = load ptr, ptr %arrayidx, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.body, %pfor.body
  %j.0 = phi i64 [ 0, %pfor.body ], [ %inc, %for.body ]
  %cmp1 = icmp slt i64 %j.0, %m
  br i1 %cmp1, label %for.body, label %pfor.preattach

for.body:                                         ; preds = %for.cond
  %arrayidx2 = getelementptr inbounds double, ptr %c, i64 %j.0
  %1 = load double, ptr %arrayidx2, align 8
  %arrayidx3 = getelementptr inbounds double, ptr %0, i64 %j.0
  store double %1, ptr %arrayidx3, align 8
  %inc = add nsw i64 %j.0, 1
  br label %for.cond, !llvm.loop !12

pfor.preattach:                                   ; preds = %for.cond
  reattach within %syncreg, label %pfor.inc

pfor.inc:                                         ; preds = %pfor.preattach, %pfor.cond
  %inc4 = add nsw i64 %__begin.0, 1
  %cmp5 = icmp slt i64 %inc4, %sub
  br i1 %cmp5, label %pfor.cond, label %pfor.cond.cleanup, !llvm.loop !13

pfor.cond.cleanup:                                ; preds = %pfor.inc
  sync within %syncreg, label %pfor.end

pfor.end:                                         ; preds = %pfor.cond.cleanup, %entry
  ret void
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @pointer_table_indirect(ptr noundef %rows, ptr noundef %indices, ptr noundef %c, i64 noundef %n, i64 noundef %m) #0 {
entry:
  %syncreg = call token @llvm.syncregion.start()
  %cmp = icmp slt i64 0, %n
  br i1 %cmp, label %pfor.ph, label %pfor.end

pfor.ph:                                          ; preds = %entry
  %sub = sub nsw i64 %n, 0
  br label %pfor.cond

pfor.cond:                                        ; preds = %pfor.inc, %pfor.ph
  %__begin.0 = phi i64 [ 0, %pfor.ph ], [ %inc5, %pfor.inc ]
  %add = add nsw i64 0, %__begin.0
  detach within %syncreg, label %pfor.body, label %pfor.inc

pfor.body:                                        ; preds = %pfor.cond
  %arrayidx = getelementptr inbounds ptr, ptr %rows, i64 %add
  %0 = load ptr, ptr %arrayidx, align 8
  br label %for.cond

for.cond:                                         ; preds = %for.body, %pfor.body
  %j.0 = phi i64 [ 0, %pfor.body ], [ %inc, %for.body ]
  %cmp1 = icmp slt i64 %j.0, %m
  br i1 %cmp1, label %for.body, label %pfor.preattach

for.body:                                         ; preds = %for.cond
  %arrayidx2 = getelementptr inbounds double, ptr %c, i64 %j.0
  %1 = load double, ptr %arrayidx2, align 8
  %arrayidx3 = getelementptr inbounds i64, ptr %indices, i64 %j.0
  %2 = load i64, ptr %arrayidx3, align 8
  %arrayidx4 = getelementptr inbounds double, ptr %0, i64 %2
  store double %1, ptr %arrayidx4, align 8
  %inc = add nsw i64 %j.0, 1
  br label %for.cond, !llvm.loop !14

pfor.preattach:                                   ; preds = %for.cond
  reattach within %syncreg, label %pfor.inc

pfor.inc:                                         ; preds = %pfor.preattach, %pfor.cond
  %inc5 = add nsw i64 %__begin.0, 1
  %cmp6 = icmp slt i64 %inc5, %sub
  br i1 %cmp6, label %pfor.cond, label %pfor.cond.cleanup, !llvm.loop !15

pfor.cond.cleanup:                                ; preds = %pfor.inc
  sync within %syncreg, label %pfor.end

pfor.end:                                         ; preds = %pfor.cond.cleanup, %entry
  ret void
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nounwind willreturn memory(argmem: readwrite) }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 21.1.3 (https://github.com/ryandeng1/opencilk-project.git a3bd4800f3229216899ec84e4d9eec986f5b4d43)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7, !9}
!9 = !{!"tapir.loop.spawn.strategy", i32 1}
!10 = distinct !{!10, !7}
!11 = distinct !{!11, !7, !9}
!12 = distinct !{!12, !7}
!13 = distinct !{!13, !7, !9}
!14 = distinct !{!14, !7}
!15 = distinct !{!15, !7, !9}
