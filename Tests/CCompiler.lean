import NumLean.Experimental.Meta.CCompiler

set_option backward.do.legacy false

open NumLean

namespace Tests.CCompiler

def copySlice' (n : USize)
    (src : FloatArray) (srcOff srcInc : USize)
    (dst : FloatArray) (dstOff dstInc : USize) : FloatArray := Id.run do
  let mut dst := dst
  let mut dstIdx := dstOff
  let mut srcIdx := srcOff
  for_all i in 0...n do
    dst := dst.set! dstIdx.toNat src[srcIdx.toNat]!
    srcIdx := srcOff + srcInc
    dstIdx := dstOff + dstInc
  return dst

/--
info: void Tests_CCompiler_copySlice_(size_t n,
    const double * restrict src,
    size_t src_size,
    size_t srcOff,
    size_t srcInc,
    double * restrict dst,
    size_t dst_size,
    size_t dstOff,
    size_t dstInc) {
  size_t dstIdx = dstOff;
  size_t srcIdx = srcOff;
  for (size_t i = 0; i < n; ++i) {
    dst[dstIdx] = src[srcIdx];
    srcIdx = (srcOff + srcInc);
    dstIdx = (dstOff + dstInc);
  }
}
-/
#guard_msgs in
#compile_c copySlice'

def copySlice'' (n : USize)
    (src : FloatArray) (srcOff srcInc : USize)
    (dst1 : FloatArray) (dst1Off dst1Inc : USize)
    (dst2 : FloatArray) (dst2Off dst2Inc' : USize) : FloatArray × FloatArray := Id.run do
  let mut dst1 := dst1
  let mut dst2 := dst2
  let mut dst1Idx := dst1Off
  let mut dst2Idx := dst2Off
  let mut srcIdx := srcOff
  for_all i in 0...n do
    dst1 := dst1.set! dst1Idx.toNat src[srcIdx.toNat]!
    dst2 := dst2.set! dst2Idx.toNat src[srcIdx.toNat]!
    srcIdx := srcOff + srcInc
    dst1Idx := dst1Off + dst1Inc
    dst2Idx := dst2Off + dst2Inc'
  return (dst1, dst2)

/--
info: void Tests_CCompiler_copySlice__(size_t n,
    const double * restrict src,
    size_t src_size,
    size_t srcOff,
    size_t srcInc,
    double * restrict dst1,
    size_t dst1_size,
    size_t dst1Off,
    size_t dst1Inc,
    double * restrict dst2,
    size_t dst2_size,
    size_t dst2Off,
    size_t dst2Inc_) {
  size_t dst1Idx = dst1Off;
  size_t dst2Idx = dst2Off;
  size_t srcIdx = srcOff;
  for (size_t i = 0; i < n; ++i) {
    dst1[dst1Idx] = src[srcIdx];
    dst2[dst2Idx] = src[srcIdx];
    srcIdx = (srcOff + srcInc);
    dst1Idx = (dst1Off + dst1Inc);
    dst2Idx = (dst2Off + dst2Inc_);
  }
}
-/
#guard_msgs in
#compile_c copySlice''

def addUSizeArray (xs : USizeArray) (i j : USize) : USize :=
  xs[i]! + j

/--
info: size_t Tests_CCompiler_addUSizeArray(const size_t * restrict xs,
    size_t xs_size,
    size_t i,
    size_t j) {
  return (xs[i] + j);
}
-/
#guard_msgs in
#compile_c addUSizeArray

def fill32 (n : USize) (dst : Float32Array) (x : Float32) : Float32Array := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    dst := dst.set! i.toNat x
  return dst

/--
info: void Tests_CCompiler_fill32(size_t n,
    float * restrict dst,
    size_t dst_size,
    float x) {
  for (size_t i = 0; i < n; ++i) {
    dst[i] = x;
  }
}
-/
#guard_msgs in
#compile_c fill32

def copyByIndex (n : USize) (src : FloatArray) (idxs : USizeArray) (dst : FloatArray) : FloatArray := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    let srcIdx := idxs[i]!
    dst := dst.set! i.toNat src[srcIdx.toNat]!
  return dst

/--
info: void Tests_CCompiler_copyByIndex(size_t n,
    const double * restrict src,
    size_t src_size,
    const size_t * restrict idxs,
    size_t idxs_size,
    double * restrict dst,
    size_t dst_size) {
  for (size_t i = 0; i < n; ++i) {
    size_t srcIdx = idxs[i];
    dst[i] = src[srcIdx];
  }
}
-/
#guard_msgs in
#compile_c copyByIndex

def copyInt32 (n : USize) (src : Int32Array) (dst : Int32Array) : Int32Array := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    dst := dst.set! i.toNat src[i]!
  return dst

/--
info: void Tests_CCompiler_copyInt32(size_t n,
    const int32_t * restrict src,
    size_t src_size,
    int32_t * restrict dst,
    size_t dst_size) {
  for (size_t i = 0; i < n; ++i) {
    dst[i] = src[i];
  }
}
-/
#guard_msgs in
#compile_c copyInt32

def copyInt64 (n : USize) (src : Int64Array) (dst : Int64Array) : Int64Array := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    dst := dst.set! i.toNat src[i]!
  return dst

/--
info: void Tests_CCompiler_copyInt64(size_t n,
    const int64_t * restrict src,
    size_t src_size,
    int64_t * restrict dst,
    size_t dst_size) {
  for (size_t i = 0; i < n; ++i) {
    dst[i] = src[i];
  }
}
-/
#guard_msgs in
#compile_c copyInt64

def copyUSize (n : USize) (src : USizeArray) (dst : USizeArray) : USizeArray := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    dst := dst.set! i.toNat src[i]!
  return dst

/--
info: void Tests_CCompiler_copyUSize(size_t n,
    const size_t * restrict src,
    size_t src_size,
    size_t * restrict dst,
    size_t dst_size) {
  for (size_t i = 0; i < n; ++i) {
    dst[i] = src[i];
  }
}
-/
#guard_msgs in
#compile_c copyUSize

def fillMatrix (rows cols : USize) (dst : FloatArray) (x : Float) : FloatArray := Id.run do
  let mut dst := dst
  for_all i in 0...rows do
    for_all j in 0...cols do
      let idx := i * cols + j
      dst := dst.set! idx.toNat x
  return dst

/--
info: void Tests_CCompiler_fillMatrix(size_t rows,
    size_t cols,
    double * restrict dst,
    size_t dst_size,
    double x) {
  for (size_t i = 0; i < rows; ++i) {
    for (size_t j = 0; j < cols; ++j) {
      size_t idx = ((i * cols) + j);
      dst[idx] = x;
    }
  }
}
-/
#guard_msgs in
#compile_c fillMatrix

def dot2 (xs ys : FloatArray) : Float := Id.run do
  let mut r : Float := 0
  for_all i in 0...xs.size do
    r := r + xs[i]! * ys[i]!
  return r

/--
info: double Tests_CCompiler_dot2(const double * restrict xs,
    size_t xs_size,
    const double * restrict ys,
    size_t ys_size) {
  double r = 0;
  for (size_t i = 0; i < xs_size; ++i) {
    r = (r + (xs[i] * ys[i]));
  }
  return r;
}
-/
#guard_msgs in
#compile_c dot2

def castToFloat (n u : USize) (i32 : Int32) (i64 : Int64) (f32 : Float32) : Float :=
  n.toFloat + u.toFloat + i32.toFloat + i64.toFloat + f32.toFloat + (1.25 : Float)

/--
info: double Tests_CCompiler_castToFloat(size_t n,
    size_t u,
    int32_t i32,
    int64_t i64,
    float f32) {
  return ((((((double)(n) + (double)(u)) + (double)(i32)) + (double)(i64)) + (double)(f32)) + 125e-2);
}
-/
#guard_msgs in
#compile_c castToFloat

def castToFloat32 (n u : USize) (i32 : Int32) (i64 : Int64) (x : Float) : Float32 :=
  n.toFloat32 + u.toFloat32 + i32.toFloat32 + i64.toFloat32 + x.toFloat32 + (1.25 : Float32)

/--
info: float Tests_CCompiler_castToFloat32(size_t n,
    size_t u,
    int32_t i32,
    int64_t i64,
    double x) {
  return ((((((float)(n) + (float)(u)) + (float)(i32)) + (float)(i64)) + (float)(x)) + 125e-2f);
}
-/
#guard_msgs in
#compile_c castToFloat32

def castToInt32 (n : USize) (i64 : Int64) : Int32 :=
  n.toNat.toInt32 + i64.toInt32 + (7 : Int32)

/--
info: int32_t Tests_CCompiler_castToInt32(size_t n,
    int64_t i64) {
  return (((int32_t)(n) + (int32_t)(i64)) + 7);
}
-/
#guard_msgs in
#compile_c castToInt32

def castToInt64 (n : USize) (i32 : Int32) : Int64 :=
  n.toNat.toInt64 + i32.toInt64 + (7 : Int64)

/--
info: int64_t Tests_CCompiler_castToInt64(size_t n,
    int32_t i32) {
  return (((int64_t)(n) + (int64_t)(i32)) + 7);
}
-/
#guard_msgs in
#compile_c castToInt64

def castToUSize (n u : USize) : USize :=
  n + USize.ofNat 3 + (7 : USize) + u

/--
info: size_t Tests_CCompiler_castToUSize(size_t n,
    size_t u) {
  return (((n + 3) + 7) + u);
}
-/
#guard_msgs in
#compile_c castToUSize

def scientificFloat : Float :=
  (1.25 : Float) + Float.ofScientific 3 false 2

/--
info: double Tests_CCompiler_scientificFloat() {
  return (125e-2 + 3e2);
}
-/
#guard_msgs in
#compile_c scientificFloat

def scientificFloat32 : Float32 :=
  (1.25 : Float32) + Float32.ofScientific 3 true 1

/--
info: float Tests_CCompiler_scientificFloat32() {
  return (125e-2f + 3e-1f);
}
-/
#guard_msgs in
#compile_c scientificFloat32

/-- In-place no-pivot Gaussian elimination on row-major `A` with separate RHS vector `b`. -/
def gaussianElimNoPivot (n : USize) (a : FloatArray) (b : FloatArray) : FloatArray × FloatArray := Id.run do
  let mut a := a
  let mut b := b
  for_all k in 0...n do
    let pivot := a[(k * n + k).toNat]!
    for_all i in (k + 1)...n do
      let factor := a[(i * n + k).toNat]! / pivot
      for_all j in k...n do
        let ij := i * n + j
        let kj := k * n + j
        a := a.set! ij.toNat (a[ij.toNat]! - factor * a[kj.toNat]!)
      b := b.set! i.toNat (b[i.toNat]! - factor * b[k.toNat]!)
  return (a, b)

/--
info: void Tests_CCompiler_gaussianElimNoPivot(size_t n,
    double * restrict a,
    size_t a_size,
    double * restrict b,
    size_t b_size) {
  for (size_t k = 0; k < n; ++k) {
    double pivot = a[((k * n) + k)];
    for (size_t i = (k + 1); i < n; ++i) {
      double factor = (a[((i * n) + k)] / pivot);
      for (size_t j = k; j < n; ++j) {
        size_t ij = ((i * n) + j);
        size_t kj = ((k * n) + j);
        a[ij] = (a[ij] - (factor * a[kj]));
      }
      b[i] = (b[i] - (factor * b[k]));
    }
  }
}
-/
#guard_msgs in
#compile_c gaussianElimNoPivot

/-- In-place Gaussian elimination with partial pivoting on row-major `A` and RHS vector `b`. -/
def gaussianElimPartialPivot (n : USize) (a : FloatArray) (b : FloatArray) : FloatArray × FloatArray := Id.run do
  let mut a := a
  let mut b := b
  for_all k in 0...n do
    let mut pivot := k
    let mut maxVal := Float.abs a[(k * n + k).toNat]!
    for_all i in (k + 1)...n do
      let v := Float.abs a[(i * n + k).toNat]!
      if maxVal < v then
        pivot := i
        maxVal := v
    for_all j in k...n do
      let kj := k * n + j
      let pj := pivot * n + j
      let tmp := a[kj.toNat]!
      a := a.set! kj.toNat a[pj.toNat]!
      a := a.set! pj.toNat tmp
    let tmpB := b[k.toNat]!
    b := b.set! k.toNat b[pivot.toNat]!
    b := b.set! pivot.toNat tmpB
    let pivotVal := a[(k * n + k).toNat]!
    for_all i in (k + 1)...n do
      let factor := a[(i * n + k).toNat]! / pivotVal
      for_all j in k...n do
        let ij := i * n + j
        let kj := k * n + j
        a := a.set! ij.toNat (a[ij.toNat]! - factor * a[kj.toNat]!)
      b := b.set! i.toNat (b[i.toNat]! - factor * b[k.toNat]!)
  return (a, b)

/--
info: void Tests_CCompiler_gaussianElimPartialPivot(size_t n,
    double * restrict a,
    size_t a_size,
    double * restrict b,
    size_t b_size) {
  for (size_t k = 0; k < n; ++k) {
    size_t pivot = k;
    double maxVal = fabs(a[((k * n) + k)]);
    for (size_t i = (k + 1); i < n; ++i) {
      double v = fabs(a[((i * n) + k)]);
      if ((maxVal < v)) {
        pivot = i;
        maxVal = v;
      }
    }
    for (size_t j = k; j < n; ++j) {
      size_t kj = ((k * n) + j);
      size_t pj = ((pivot * n) + j);
      double tmp = a[kj];
      a[kj] = a[pj];
      a[pj] = tmp;
    }
    double tmpB = b[k];
    b[k] = b[pivot];
    b[pivot] = tmpB;
    double pivotVal = a[((k * n) + k)];
    for (size_t i = (k + 1); i < n; ++i) {
      double factor = (a[((i * n) + k)] / pivotVal);
      for (size_t j = k; j < n; ++j) {
        size_t ij = ((i * n) + j);
        size_t kj = ((k * n) + j);
        a[ij] = (a[ij] - (factor * a[kj]));
      }
      b[i] = (b[i] - (factor * b[k]));
    }
  }
}
-/
#guard_msgs in
#compile_c gaussianElimPartialPivot

/-- In-place lower-triangular Cholesky decomposition of a row-major SPD matrix. -/
def choleskyLower (n : USize) (a : FloatArray) : FloatArray := Id.run do
  let mut a := a
  for_all i in 0...n do
    for_all j in 0...i do
      let mut sum := a[(i * n + j).toNat]!
      for_all k in 0...j do
        sum := sum - a[(i * n + k).toNat]! * a[(j * n + k).toNat]!
      a := a.set! (i * n + j).toNat (sum / a[(j * n + j).toNat]!)
    let mut diag := a[(i * n + i).toNat]!
    for_all k in 0...i do
      diag := diag - a[(i * n + k).toNat]! * a[(i * n + k).toNat]!
    a := a.set! (i * n + i).toNat (Float.sqrt diag)
  return a

/--
info: void Tests_CCompiler_choleskyLower(size_t n,
    double * restrict a,
    size_t a_size) {
  for (size_t i = 0; i < n; ++i) {
    for (size_t j = 0; j < i; ++j) {
      double sum = a[((i * n) + j)];
      for (size_t k = 0; k < j; ++k) {
        sum = (sum - (a[((i * n) + k)] * a[((j * n) + k)]));
      }
      a[((i * n) + j)] = (sum / a[((j * n) + j)]);
    }
    double diag = a[((i * n) + i)];
    for (size_t k = 0; k < i; ++k) {
      diag = (diag - (a[((i * n) + k)] * a[((i * n) + k)]));
    }
    a[((i * n) + i)] = sqrt(diag);
  }
}
-/
#guard_msgs in
#compile_c choleskyLower

def badArrayAlias (xs : FloatArray) (i : USize) : Float := Id.run do
  let ys := xs
  return ys[i.toNat]!

/--
error: C compiler error: unsupported operation: array alias `let ys := xs` is not supported; mutable arrays must use the standard `let mut xs := xs; xs := xs.set! ...` handoff pattern
-/
#guard_msgs in
#compile_c badArrayAlias

end Tests.CCompiler
