; RUN: opt -disable-output < %s -aa-pipeline=drf-aa -passes=aa-eval -enable-drf-aa -print-all-alias-modref-info 2>&1 | FileCheck %s

define void @covariance_style(ptr %data, ptr %cov) {
entry:
  %sr.outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %j = phi i64 [ %i, %outer.body ], [ %j.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %pcov = getelementptr [16 x double], ptr %cov, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pcov
  %pdata.i = getelementptr [16 x double], ptr %data, i64 0, i64 %i
  %vi = load double, ptr %pdata.i
  %pdata.j = getelementptr [16 x double], ptr %data, i64 0, i64 %j
  %vj = load double, ptr %pdata.j
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %j.next = add nuw nsw i64 %j, 1
  %inner.cmp = icmp slt i64 %j.next, 4
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, 4
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}


define void @rectangular_diagonal_with_lower_companion(ptr %data, ptr %cov) {
entry:
  %sr.outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %jl = phi i64 [ 0, %outer.body ], [ %jl.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %j = add nuw nsw i64 %i, %jl
  %pcov.rect = getelementptr [16 x double], ptr %cov, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pcov.rect
  %pdata.i.rect = getelementptr [16 x double], ptr %data, i64 0, i64 %i
  %vi.rect = load double, ptr %pdata.i.rect
  %pdata.j.rect = getelementptr [16 x double], ptr %data, i64 0, i64 %j
  %vj.rect = load double, ptr %pdata.j.rect
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %jl.next = add nuw nsw i64 %jl, 1
  %inner.cmp = icmp slt i64 %jl.next, 4
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, 4
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}


define void @rectangular_diagonal_with_two_companions(ptr %data, ptr %cov) {
entry:
  %sr.outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %jl = phi i64 [ 0, %outer.body ], [ %jl.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %j = add nuw nsw i64 %i, %jl
  %pcov.rect.both = getelementptr [16 x double], ptr %cov, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pcov.rect.both
  %pdata.low.rect.both = getelementptr [16 x double], ptr %data, i64 0, i64 %i
  %vlow.rect.both = load double, ptr %pdata.low.rect.both
  %i.plus.3 = add nuw nsw i64 %i, 3
  %pdata.high.rect.both = getelementptr [16 x double], ptr %data, i64 0, i64 %i.plus.3
  %vhigh.rect.both = load double, ptr %pdata.high.rect.both
  %pdata.j.rect.both = getelementptr [16 x double], ptr %data, i64 0, i64 %j
  %vj.rect.both = load double, ptr %pdata.j.rect.both
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %jl.next = add nuw nsw i64 %jl, 1
  %inner.cmp = icmp slt i64 %jl.next, 4
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, 4
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}


define void @diagonal_without_boundary_witness(ptr %data, ptr %cov) {
entry:
  %sr.outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %jl = phi i64 [ 0, %outer.body ], [ %jl.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %j = add nuw nsw i64 %i, %jl
  %pcov.no.boundary = getelementptr [16 x double], ptr %cov, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pcov.no.boundary
  %pdata.j.no.boundary = getelementptr [16 x double], ptr %data, i64 0, i64 %j
  %vj = load double, ptr %pdata.j.no.boundary
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %jl.next = add nuw nsw i64 %jl, 1
  %inner.cmp = icmp slt i64 %jl.next, 4
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, 4
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}

define void @lockstep_2d_wall(ptr %a, ptr %b) {
entry:
  %sr.outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %j = phi i64 [ 0, %outer.body ], [ %j.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %pa = getelementptr [16 x double], ptr %a, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pa
  %pb = getelementptr [16 x double], ptr %b, i64 %i, i64 %j
  %v = load double, ptr %pb
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %j.next = add nuw nsw i64 %j, 1
  %inner.cmp = icmp slt i64 %j.next, 4
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, 4
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}

define void @correlation_style_shifted_boundary(ptr %data, ptr %corr) {
entry:
  %sr.outer = call token @llvm.syncregion.start()
  br label %outer.header

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %ip1 = add nuw nsw i64 %i, 1
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %j = phi i64 [ %ip1, %outer.body ], [ %j.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %pcorr.shifted = getelementptr [16 x double], ptr %corr, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pcorr.shifted
  %pdata.i.shifted = getelementptr [16 x double], ptr %data, i64 0, i64 %i
  %vi.shifted = load double, ptr %pdata.i.shifted
  %pdata.j.shifted = getelementptr [16 x double], ptr %data, i64 0, i64 %j
  %vj.shifted = load double, ptr %pdata.j.shifted
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %j.next = add nuw nsw i64 %j, 1
  %inner.cmp = icmp slt i64 %j.next, 4
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, 3
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}

define void @multi_coordinate_shifted_boundary(ptr %data, ptr %out) {
entry:
  %sr.u = call token @llvm.syncregion.start()
  br label %u.header

u.header:
  %u = phi i64 [ 0, %entry ], [ %u.next, %u.latch ]
  detach within %sr.u, label %u.body, label %u.latch

u.body:
  %sr.v = call token @llvm.syncregion.start()
  br label %v.header

v.header:
  %v = phi i64 [ 0, %u.body ], [ %v.next, %v.latch ]
  detach within %sr.v, label %v.body, label %v.latch

v.body:
  %sr.jl = call token @llvm.syncregion.start()
  br label %jl.header

jl.header:
  %jl = phi i64 [ 0, %v.body ], [ %jl.next, %jl.latch ]
  detach within %sr.jl, label %jl.body, label %jl.latch

jl.body:
  %u2 = shl nuw nsw i64 %u, 1
  %v3 = mul nuw nsw i64 %v, 3
  %uv = add nuw nsw i64 %u2, %v3
  %jl5 = mul nuw nsw i64 %jl, 5
  %target.base = add nuw nsw i64 %uv, %jl5
  %target.idx = add nuw nsw i64 %target.base, 5
  %pout.multi = getelementptr [128 x double], ptr %out, i64 0, i64 %target.idx
  store double 1.000000e+00, ptr %pout.multi
  %pdata.companion.multi = getelementptr [128 x double], ptr %data, i64 0, i64 %uv
  %vc.multi = load double, ptr %pdata.companion.multi
  %pdata.target.multi = getelementptr [128 x double], ptr %data, i64 0, i64 %target.idx
  %vt.multi = load double, ptr %pdata.target.multi
  reattach within %sr.jl, label %jl.latch

jl.latch:
  %jl.next = add nuw nsw i64 %jl, 1
  %jl.cmp = icmp slt i64 %jl.next, 4
  br i1 %jl.cmp, label %jl.header, label %jl.exit

jl.exit:
  sync within %sr.jl, label %v.reattach

v.reattach:
  reattach within %sr.v, label %v.latch

v.latch:
  %v.next = add nuw nsw i64 %v, 1
  %v.cmp = icmp slt i64 %v.next, 4
  br i1 %v.cmp, label %v.header, label %v.exit

v.exit:
  sync within %sr.v, label %u.reattach

u.reattach:
  reattach within %sr.u, label %u.latch

u.latch:
  %u.next = add nuw nsw i64 %u, 1
  %u.cmp = icmp slt i64 %u.next, 4
  br i1 %u.cmp, label %u.header, label %u.exit

u.exit:
  sync within %sr.u, label %cont

cont:
  ret void
}


define void @dynamic_covariance_style(ptr %data, ptr %cov, i64 %n) {
entry:
  %has.iter = icmp sgt i64 %n, 0
  br i1 %has.iter, label %outer.header, label %cont

outer.header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %outer.latch ]
  %sr.outer = call token @llvm.syncregion.start()
  detach within %sr.outer, label %outer.body, label %outer.latch

outer.body:
  %sr.inner = call token @llvm.syncregion.start()
  br label %inner.header

inner.header:
  %j = phi i64 [ %i, %outer.body ], [ %j.next, %inner.latch ]
  detach within %sr.inner, label %inner.body, label %inner.latch

inner.body:
  %pcov.dynamic = getelementptr [1024 x double], ptr %cov, i64 %i, i64 %j
  store double 1.000000e+00, ptr %pcov.dynamic
  %pdata.i.dynamic = getelementptr [1024 x double], ptr %data, i64 0, i64 %i
  %vi.dynamic = load double, ptr %pdata.i.dynamic
  %pdata.j.dynamic = getelementptr [1024 x double], ptr %data, i64 0, i64 %j
  %vj.dynamic = load double, ptr %pdata.j.dynamic
  reattach within %sr.inner, label %inner.latch

inner.latch:
  %j.next = add nuw nsw i64 %j, 1
  %inner.cmp = icmp slt i64 %j.next, %n
  br i1 %inner.cmp, label %inner.header, label %inner.exit

inner.exit:
  sync within %sr.inner, label %outer.reattach

outer.reattach:
  reattach within %sr.outer, label %outer.latch

outer.latch:
  %i.next = add nuw nsw i64 %i, 1
  %outer.cmp = icmp slt i64 %i.next, %n
  br i1 %outer.cmp, label %outer.header, label %outer.exit

outer.exit:
  sync within %sr.outer, label %cont

cont:
  ret void
}

declare token @llvm.syncregion.start()

; CHECK-LABEL: Function: covariance_style:
; CHECK-DAG: NoAlias: {{.*}}%pcov, {{.*}}%pdata.i
; CHECK-DAG: NoAlias: {{.*}}%pcov, {{.*}}%pdata.j
; CHECK-LABEL: Function: rectangular_diagonal_with_lower_companion:
; CHECK: MayAlias: {{.*}}%pcov.rect, {{.*}}%pdata.j.rect
; CHECK-NOT: NoAlias: {{.*}}%pcov.rect, {{.*}}%pdata.j.rect
; CHECK-LABEL: Function: rectangular_diagonal_with_two_companions:
; CHECK: NoAlias: {{.*}}%pcov.rect.both, {{.*}}%pdata.j.rect.both
; CHECK-LABEL: Function: diagonal_without_boundary_witness:
; CHECK: MayAlias: {{.*}}%pcov.no.boundary, {{.*}}%pdata.j.no.boundary
; CHECK-NOT: NoAlias: {{.*}}%pcov.no.boundary, {{.*}}%pdata.j.no.boundary
; CHECK-LABEL: Function: lockstep_2d_wall:
; CHECK: MayAlias: {{.*}}%pa, {{.*}}%pb
; CHECK-NOT: NoAlias: {{.*}}%pa, {{.*}}%pb
; CHECK-LABEL: Function: correlation_style_shifted_boundary:
; CHECK-DAG: NoAlias: {{.*}}%pcorr.shifted, {{.*}}%pdata.i.shifted
; CHECK-DAG: NoAlias: {{.*}}%pcorr.shifted, {{.*}}%pdata.j.shifted
; CHECK-LABEL: Function: multi_coordinate_shifted_boundary:
; CHECK: MayAlias: {{.*}}%pdata.target.multi, {{.*}}%pout.multi
; CHECK-NOT: NoAlias: {{.*}}%pdata.target.multi, {{.*}}%pout.multi
; CHECK-LABEL: Function: dynamic_covariance_style:
; CHECK-DAG: NoAlias: {{.*}}%pcov.dynamic, {{.*}}%pdata.i.dynamic
; CHECK-DAG: NoAlias: {{.*}}%pcov.dynamic, {{.*}}%pdata.j.dynamic
