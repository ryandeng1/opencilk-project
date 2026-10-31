// RUN: %clang_cc1 %s -x c -fopencilk -fhyperobject-associative-math -emit-llvm -disable-llvm-passes -o - | FileCheck %s --check-prefixes=CHECK,REASSOC
// RUN: %clang_cc1 %s -x c -fopencilk -emit-llvm -disable-llvm-passes -o - | FileCheck %s --check-prefixes=CHECK,STRICT
// RUN: %clang_cc1 %s -x c++ -fopencilk -fhyperobject-associative-math -emit-llvm -disable-llvm-passes -o - | FileCheck %s --check-prefixes=CHECK,REASSOC
// RUN: %clang_cc1 %s -x c++ -fopencilk -emit-llvm -disable-llvm-passes -o - | FileCheck %s --check-prefixes=CHECK,STRICT

#ifdef __cplusplus
extern "C" {
#endif
void identity(void *), reduce(void *, void *);
extern double _Hyperobject(identity, reduce) sum;
extern double plain;

// -fhyperobject-associative-math licenses reassociation only for updates of
// reducer views; everything else keeps strict FP semantics.

double view_add(double v)
{
  // CHECK-LABEL: view_add
  // CHECK: call ptr @llvm.hyper.lookup.2.i64(ptr @sum
  // REASSOC: fadd reassoc nsz double
  // STRICT: fadd double %
  // CHECK: store double
  sum += v;
  return 0.0;
}

double view_mul(double v)
{
  // CHECK-LABEL: view_mul
  // CHECK: call ptr @llvm.hyper.lookup.2.i64(ptr @sum
  // REASSOC: fmul reassoc nsz double
  // STRICT: fmul double %
  // CHECK: store double
  sum *= v;
  return 0.0;
}

double plain_add(double v)
{
  // CHECK-LABEL: plain_add
  // CHECK: fadd double %
  // CHECK: store double
  plain += v;
  return 0.0;
}

#ifdef __cplusplus
}
#endif
