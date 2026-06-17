import NumLean.Data.HTuple.RangeIterator
import NumLean.Data.HList.RangeIterator
import NumLean.Data.Vector.RangeIterator

open NumLean TensorIndex HList

namespace Tests.FloatArrayTensorBenchmark

def matrixSize : Nat := 192
def rank3Dim0 : Nat := 96
def rank3Dim1 : Nat := 64
def rank3Dim2 : Nat := 32

def makeFloatArray (n salt : Nat) : FloatArray :=
  FloatArray.mk <| Array.ofFn fun i : Fin n =>
    Float.ofNat ((i.1 * 17 + salt * 31 + 13) % 1024) / 1024.0

theorem makeFloatArray_size (n salt : Nat) : (makeFloatArray n salt).size = n := by
  change (Array.ofFn (fun i : Fin n =>
    Float.ofNat ((i.1 * 17 + salt * 31 + 13) % 1024) / 1024.0)).size = n
  rw [Array.size_ofFn]

def checksum (xs : FloatArray) : Float := Id.run do
  let stride := max 1 (xs.size / 4096)
  let mut acc := 0.0
  let mut i := 0
  while i < xs.size do
    if h : i < xs.size then
      acc := acc + xs.get i h
    i := i + stride
  return acc

def timeRun (name : String) (runs : Nat) (body : Nat → IO Float) : IO Unit := do
  let warmToken ← IO.monoMsNow
  let warm ← body warmToken
  let start ← IO.monoMsNow
  let mut guard := warm
  for run in [0:runs] do
    let token ← IO.monoMsNow
    guard ← body (token + run)
  let stop ← IO.monoMsNow
  let elapsed := stop - start
  let perRun := if runs == 0 then 0.0 else Float.ofNat elapsed / Float.ofNat runs
  IO.println s!"{name}\t{elapsed}ms\t{perRun}ms/run\t{guard}"

@[inline] def fset (xs : FloatArray) (i : Nat) (x : Float) : FloatArray :=
  if h : i < xs.size then xs.set i x h else xs

theorem flat3_lt {d0 d1 d2 i j k : Nat}
    (hi : i < d0) (hj : j < d1) (hk : k < d2) :
    (i * d1 + j) * d2 + k < d0 * d1 * d2 := by
  have hprefix : i * d1 + j < d0 * d1 := by
    have hiSucc : i + 1 ≤ d0 := Nat.succ_le_of_lt hi
    calc
      i * d1 + j < i * d1 + d1 := Nat.add_lt_add_left hj _
      _ = (i + 1) * d1 := by rw [Nat.succ_mul]
      _ ≤ d0 * d1 := Nat.mul_le_mul_right d1 hiSucc
  have hprefixSucc : i * d1 + j + 1 ≤ d0 * d1 := Nat.succ_le_of_lt hprefix
  calc
    (i * d1 + j) * d2 + k < (i * d1 + j) * d2 + d2 := Nat.add_lt_add_left hk _
    _ = (i * d1 + j + 1) * d2 := by rw [Nat.succ_mul]
    _ ≤ (d0 * d1) * d2 := Nat.mul_le_mul_right d2 hprefixSucc
    _ = d0 * d1 * d2 := by rw [Nat.mul_assoc]

def matmulDirect (n token : Nat) (a b : FloatArray)
    (ha : a.size = n * n) (hb : b.size = n * n) : FloatArray := Id.run do
  let mut c := FloatArray.mk (Array.replicate (n * n) 0.0)
  let bias := Float.ofNat (token % 7) * 0.000001
  for hi : i in 0...n do
    have hiLt : i < n := by
      simp only [Membership.mem] at hi
      omega
    for hj : j in 0...n do
      have hjLt : j < n := by
        simp only [Membership.mem] at hj
        omega
      let mut acc := bias
      for hk : k in 0...n do
        have hkLt : k < n := by
          simp only [Membership.mem] at hk
          omega
        have haIdx : i * n + k < a.size := by
          rw [ha]
          nlinarith
        have hbIdx : k * n + j < b.size := by
          rw [hb]
          nlinarith
        acc := acc + a.get (i * n + k) haIdx * b.get (k * n + j) hbIdx
      c := fset c (i * n + j) acc
  return c

def matmulHTupleRange (n token : Nat) (a b : FloatArray)
    (ha : a.size = n * n) (hb : b.size = n * n) : FloatArray := Id.run do
  let shape : Shape (.prod .leaf .leaf) := .prod (.leaf n) (.leaf n)
  let mut c := FloatArray.mk (Array.replicate (n * n) 0.0)
  let bias := Float.ofNat (token % 7) * 0.000001
  for h : idx in (0 : Shape (.prod .leaf .leaf))...shape do
    have hbounds := (HTuple.Range.valid_zero_shape_iff_inBounds (shape := shape) (idx := idx)).mp h
    let .prod (.leaf i) (.leaf j) := idx
    let row := i
    let col := j
    let mut acc := bias
    for hk : k in 0...n do
      have hkLt : k < n := by
        simp only [Membership.mem] at hk
        omega
      have hi : row < n := hbounds.1
      have hj : col < n := hbounds.2
      have haIdx : row * n + k < a.size := by
        rw [ha]
        nlinarith
      have hbIdx : k * n + col < b.size := by
        rw [hb]
        nlinarith
      acc := acc + a.get (row * n + k) haIdx * b.get (k * n + col) hbIdx
    let out := row * n + col
    c := fset c out acc
  return c

def inner3Direct (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for hi : i in 0...d0 do
    have hiLt : i < d0 := by
      simp only [Membership.mem] at hi
      omega
    for hj : j in 0...d1 do
      have hjLt : j < d1 := by
        simp only [Membership.mem] at hj
        omega
      for hk : k in 0...d2 do
        have hkLt : k < d2 := by
          simp only [Membership.mem] at hk
          omega
        let linear := (i * d1 + j) * d2 + k
        have hlinear : linear < a.size := by
          rw [ha]
          exact flat3_lt hiLt hjLt hkLt
        have hlinearB : linear < b.size := by
          rw [hb]
          exact flat3_lt hiLt hjLt hkLt
        acc := acc + a.get linear hlinear * b.get linear hlinearB
  return acc

def inner3HTupleRange (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let shape : Shape _ := h(d0, d1, d2)
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h : h(i,j,k) in 0...shape do
    have hbounds := HTuple.Range.valid_zero_shape_iff_inBounds.mp h
    have hi : i < d0 := hbounds.1
    have hj : j < d1 := hbounds.2.1
    have hk : k < d2 := hbounds.2.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def inner3HTupleEnumRange (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let shape : Shape _ := h(d0, d1, d2)
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h : (linIdx, h(i,j,k)) in (0...shape).enum do
    have hbounds := HTuple.Range.valid_zero_shape_iff_inBounds.mp h.1
    have hi : i < d0 := hbounds.1
    have hj : j < d1 := hbounds.2.1
    have hk : k < d2 := hbounds.2.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def inner3DirectUInt64Uget (d0 d1 d2 token : Nat) (a b : FloatArray)
    (_ha : a.size = d0 * d1 * d2) (_hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let d0u := UInt64.ofNat d0
  let d1u := UInt64.ofNat d1
  let d2u := UInt64.ofNat d2
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for i in (0 : UInt64)...d0u do
    for j in (0 : UInt64)...d1u do
      for k in (0 : UInt64)...d2u do
        let flat := (i * d1u + j) * d2u + k
        let flatIdx := flat.toUSize
        acc := acc + a.uget flatIdx (by sorry) * b.uget flatIdx (by sorry)
  return acc

def inner3HTupleUInt64RangeUget (d0 d1 d2 token : Nat) (a b : FloatArray)
    (_ha : a.size = d0 * d1 * d2) (_hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let shape : TIndex UInt64 _ := h(UInt64.ofNat d0, UInt64.ofNat d1, UInt64.ofNat d2)
  let d1u := UInt64.ofNat d1
  let d2u := UInt64.ofNat d2
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h(i,j,k) in (0 : TIndex UInt64 _)...shape do
    let flat := (i * d1u + j) * d2u + k
    let flatIdx := flat.toUSize
    acc := acc + a.uget flatIdx (by sorry) * b.uget flatIdx (by sorry)
  return acc

def inner3HTupleUInt64ShapeDirectUget (d0 d1 d2 token : Nat) (a b : FloatArray)
    (_ha : a.size = d0 * d1 * d2) (_hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let shape : TIndex UInt64 _ := h(UInt64.ofNat d0, UInt64.ofNat d1, UInt64.ofNat d2)
  let h(d0u,d1u,d2u) := shape
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for i in (0 : UInt64)...d0u do
    for j in (0 : UInt64)...d1u do
      for k in (0 : UInt64)...d2u do
        let flat := (i * d1u + j) * d2u + k
        let flatIdx := flat.toUSize
        acc := acc + a.uget flatIdx (by sorry) * b.uget flatIdx (by sorry)
  return acc

def inner3HTupleUInt64FoldRangeUget (d0 d1 d2 token : Nat) (a b : FloatArray)
    (_ha : a.size = d0 * d1 * d2) (_hb : b.size = d0 * d1 * d2) : Float :=
  let shape : TIndex UInt64 _ := h(UInt64.ofNat d0, UInt64.ofNat d1, UInt64.ofNat d2)
  let d1u := UInt64.ofNat d1
  let d2u := UInt64.ofNat d2
  let init := Float.ofNat (token % 7) * 0.000001
  HTuple.Range.foldRange ((0 : TIndex UInt64 _)...shape) init fun h(i,j,k) _ acc =>
    let flat := (i * d1u + j) * d2u + k
    let flatIdx := flat.toUSize
    acc + a.uget flatIdx (by sorry) * b.uget flatIdx (by sorry)

def inner3HPTupleRange (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let lo : HList.HPTuple Nat hlp(•, •, •) := hl(0, 0, 0)
  let hi : HList.HPTuple Nat hlp(•, •, •) := hl(d0, d1, d2)
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h : hl(i,j,k) in lo...hi do
    have hbounds : i < d0 ∧ j < d1 ∧ k < d2 := by
      simpa [lo, hi, Membership.mem, HList.Range.Valid, HList.HPTuple.cons, HList.HPTuple.leaf] using h
    have hi : i < d0 := hbounds.1
    have hj : j < d1 := hbounds.2.1
    have hk : k < d2 := hbounds.2.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def inner3HPTupleEnumRange (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let lo : HList.HPTuple Nat hlp(•, •, •) := hl(0, 0, 0)
  let hi : HList.HPTuple Nat hlp(•, •, •) := hl(d0, d1, d2)
  let r := lo...hi
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h : (linIdx, hl(i,j,k)) in r.enum do
    have hbounds : i < d0 ∧ j < d1 ∧ k < d2 := by
      simpa [Std.Rco.enum, Std.Rco.HasEnum.enum, r, lo, hi, Membership.mem, HList.Range.Valid,
        Std.Rco.instHasEnumRcoHPTuple, HList.HPTuple.cons, HList.HPTuple.leaf] using h.1
    have hi : i < d0 := hbounds.1
    have hj : j < d1 := hbounds.2.1
    have hk : k < d2 := hbounds.2.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def inner3VectorRange (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let lo : Vector Nat 3 := Vector.ofFn fun _ => 0
  let hi : Vector Nat 3 := Vector.ofFn fun i =>
    match i.1 with
    | 0 => d0
    | 1 => d1
    | _ => d2
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h : idx in lo...hi do
    let i := idx[0]
    let j := idx[1]
    let k := idx[2]
    have hbounds : i < d0 ∧ j < d1 ∧ k < d2 := by
      simpa [lo, hi, i, j, k, Membership.mem, Vector.Range.Valid, Vector.head, Vector.tail] using h
    have hi : i < d0 := hbounds.1
    have hj : j < d1 := hbounds.2.1
    have hk : k < d2 := hbounds.2.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def inner3VectorEnumRange (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let lo : Vector Nat 3 := Vector.ofFn fun _ => 0
  let hi : Vector Nat 3 := Vector.ofFn fun i =>
    match i.1 with
    | 0 => d0
    | 1 => d1
    | _ => d2
  let r := lo...hi
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for h : (linIdx, idx) in r.enum do
    let i := idx[0]
    let j := idx[1]
    let k := idx[2]
    have hbounds : i < d0 ∧ j < d1 ∧ k < d2 := by
      simpa [Std.Rco.enum, Std.Rco.HasEnum.enum, Std.Rco.instHasEnumRcoVector, r, lo, hi,
        i, j, k, Membership.mem, Vector.Range.Valid, Vector.head, Vector.tail] using h.1
    have hi : i < d0 := hbounds.1
    have hj : j < d1 := hbounds.2.1
    have hk : k < d2 := hbounds.2.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def matmulDirectChecksum (a b : FloatArray)
    (ha : a.size = matrixSize * matrixSize) (hb : b.size = matrixSize * matrixSize)
    (token : Nat) : Float :=
  checksum (matmulDirect matrixSize token a b ha hb)

def matmulHTupleRangeChecksum (a b : FloatArray)
    (ha : a.size = matrixSize * matrixSize) (hb : b.size = matrixSize * matrixSize)
    (token : Nat) : Float :=
  checksum (matmulHTupleRange matrixSize token a b ha hb)

def inner3DirectChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3Direct rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HTupleRangeChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HTupleRange rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HTupleEnumRangeChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HTupleEnumRange rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3DirectUInt64UgetChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3DirectUInt64Uget rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HTupleUInt64RangeUgetChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HTupleUInt64RangeUget rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HTupleUInt64ShapeDirectUgetChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HTupleUInt64ShapeDirectUget rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HTupleUInt64FoldRangeUgetChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HTupleUInt64FoldRangeUget rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HPTupleRangeChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HPTupleRange rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3HPTupleEnumRangeChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3HPTupleEnumRange rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3VectorRangeChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3VectorRange rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3VectorEnumRangeChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3VectorEnumRange rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def run : IO Unit := do
  IO.println s!"FloatArray iterator benchmark payload: matmul={matrixSize}x{matrixSize}, dense-inner3={rank3Dim0}x{rank3Dim1}x{rank3Dim2}"
  IO.println "Comparisons are direct nested dimension loops vs HTuple range loops."
  IO.println "Inputs and per-run scalars depend on runtime IO.monoMsNow tokens to avoid compile-time folding."
  IO.println "name\ttotal\tper-run\tchecksum"
  let salt ← IO.monoMsNow
  let matA := makeFloatArray (matrixSize * matrixSize) (salt + 1)
  let matB := makeFloatArray (matrixSize * matrixSize) (salt + 2)
  let tensorA := makeFloatArray (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 3)
  let tensorB := makeFloatArray (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 4)
  have hmatA : matA.size = matrixSize * matrixSize := by
    simpa [matA] using makeFloatArray_size (matrixSize * matrixSize) (salt + 1)
  have hmatB : matB.size = matrixSize * matrixSize := by
    simpa [matB] using makeFloatArray_size (matrixSize * matrixSize) (salt + 2)
  have htensorA : tensorA.size = rank3Dim0 * rank3Dim1 * rank3Dim2 := by
    simpa [tensorA] using makeFloatArray_size (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 3)
  have htensorB : tensorB.size = rank3Dim0 * rank3Dim1 * rank3Dim2 := by
    simpa [tensorB] using makeFloatArray_size (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 4)
  timeRun "matmul direct nested loops" 2 (fun token => pure (matmulDirectChecksum matA matB hmatA hmatB token))
  timeRun "matmul HTuple range" 2 (fun token => pure (matmulHTupleRangeChecksum matA matB hmatA hmatB token))
  timeRun "dense inner3 direct nested loops" 64 (fun token => pure (inner3DirectChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 direct UInt64 uget loops" 64 (fun token => pure (inner3DirectUInt64UgetChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HTuple range" 64 (fun token => pure (inner3HTupleRangeChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HTuple enum range" 64 (fun token => pure (inner3HTupleEnumRangeChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HTuple UInt64 uget range" 64 (fun token => pure (inner3HTupleUInt64RangeUgetChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HTuple UInt64 foldRange uget" 64 (fun token => pure (inner3HTupleUInt64FoldRangeUgetChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HTuple UInt64 shape direct uget" 64 (fun token => pure (inner3HTupleUInt64ShapeDirectUgetChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HPTuple range" 64 (fun token => pure (inner3HPTupleRangeChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 HPTuple enum range" 64 (fun token => pure (inner3HPTupleEnumRangeChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 Vector range" 64 (fun token => pure (inner3VectorRangeChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 Vector enum range" 64 (fun token => pure (inner3VectorEnumRangeChecksum tensorA tensorB htensorA htensorB token))

end Tests.FloatArrayTensorBenchmark

def main : IO Unit :=
  Tests.FloatArrayTensorBenchmark.run
