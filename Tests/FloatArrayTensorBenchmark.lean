import NumLean.Data.TensorIndex.FinTIndexFold

open NumLean TensorIndex

namespace Tests.FloatArrayTensorBenchmark

def matrixSize : Nat := 192
def rank3Dim0 : Nat := 96
def rank3Dim1 : Nat := 64
def rank3Dim2 : Nat := 32
def rank3CoordDim0 : Nat := 64
def rank3CoordDim1 : Nat := 48
def rank3CoordDim2 : Nat := 32

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

def matmulRowMajorIter (n token : Nat) (a b : FloatArray)
    (ha : a.size = n * n) (hb : b.size = n * n) : FloatArray := Id.run do
  let shape : Shape (.prod .leaf .leaf) := .prod (.leaf n) (.leaf n)
  let mut c := FloatArray.mk (Array.replicate (n * n) 0.0)
  let bias := Float.ofNat (token % 7) * 0.000001
  for ⟨_linear, idx, _hidx⟩ in FinTIndex.rowMajorFinIter shape do
    let ⟨.prod (.leaf i) (.leaf j), hbounds⟩ := idx
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

def matmulStandaloneLoop (n token : Nat) (a b : FloatArray)
    (ha : a.size = n * n) (hb : b.size = n * n) : FloatArray := Id.run do
  let shape : Shape (.prod .leaf .leaf) := .prod (.leaf n) (.leaf n)
  let bias := Float.ofNat (token % 7) * 0.000001
  return FinTIndex.RowMajorLoop.foldIdx shape (FloatArray.mk (Array.replicate (n * n) 0.0))
    (fun _linear idx c =>
      let ⟨.prod (.leaf i) (.leaf j), hbounds⟩ := idx
      let row := i
      let col := j
      let acc := Id.run do
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
        return acc
      let out := row * n + col
      fset c out acc)

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

def inner3RowMajorIter (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for ⟨_linear, idx, _hidx⟩ in FinTIndex.rowMajorFinIter shape do
    let ⟨.prod (.prod (.leaf i) (.leaf j)) (.leaf k), hbounds⟩ := idx
    have hi : i < d0 := hbounds.1.1
    have hj : j < d1 := hbounds.1.2
    have hk : k < d2 := hbounds.2
    let flat := (i * d1 + j) * d2 + k
    have hflat : flat < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hflatB : flat < b.size := by
      rw [hb]
      exact flat3_lt hi hj hk
    acc := acc + a.get flat hflat * b.get flat hflatB
  return acc

def inner3StandaloneLoop (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float :=
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  FinTIndex.RowMajorLoop.foldIdx shape (Float.ofNat (token % 7) * 0.000001)
    (fun _linear idx acc =>
      let ⟨.prod (.prod (.leaf i) (.leaf j)) (.leaf k), hbounds⟩ := idx
      have hi : i < d0 := hbounds.1.1
      have hj : j < d1 := hbounds.1.2
      have hk : k < d2 := hbounds.2
      let flat := (i * d1 + j) * d2 + k
      have hflat : flat < a.size := by
        rw [ha]
        exact flat3_lt hi hj hk
      have hflatB : flat < b.size := by
        rw [hb]
        exact flat3_lt hi hj hk
      acc + a.get flat hflat * b.get flat hflatB)

def inner3CoordDirect (d0 d1 d2 token : Nat) (a b : FloatArray)
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
        let ai := (i * d1 + j) * d2 + k
        let bi := (i * d1 + (d1 - 1 - j)) * d2 + k
        have hai : ai < a.size := by
          rw [ha]
          exact flat3_lt hiLt hjLt hkLt
        have hjFlip : d1 - 1 - j < d1 := by
          omega
        have hbi : bi < b.size := by
          rw [hb]
          exact flat3_lt hiLt hjFlip hkLt
        acc := acc + a.get ai hai * b.get bi hbi
  return acc

def inner3CoordRowMajorIter (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float := Id.run do
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  let mut acc := Float.ofNat (token % 7) * 0.000001
  for ⟨_linear, idx, _hidx⟩ in FinTIndex.rowMajorFinIter shape do
    let ⟨.prod (.prod (.leaf i) (.leaf j)) (.leaf k), hbounds⟩ := idx
    have hi : i < d0 := hbounds.1.1
    have hj : j < d1 := hbounds.1.2
    have hk : k < d2 := hbounds.2
    let ai := (i * d1 + j) * d2 + k
    let bi := (i * d1 + (d1 - 1 - j)) * d2 + k
    have hai : ai < a.size := by
      rw [ha]
      exact flat3_lt hi hj hk
    have hjFlip : d1 - 1 - j < d1 := by
      omega
    have hbi : bi < b.size := by
      rw [hb]
      exact flat3_lt hi hjFlip hk
    acc := acc + a.get ai hai * b.get bi hbi
  return acc

def inner3CoordStandaloneLoop (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float :=
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  FinTIndex.RowMajorLoop.foldIdx shape (Float.ofNat (token % 7) * 0.000001)
    (fun _linear idx acc =>
      let ⟨.prod (.prod (.leaf i) (.leaf j)) (.leaf k), hbounds⟩ := idx
      have hi : i < d0 := hbounds.1.1
      have hj : j < d1 := hbounds.1.2
      have hk : k < d2 := hbounds.2
      let ai := (i * d1 + j) * d2 + k
      let bi := (i * d1 + (d1 - 1 - j)) * d2 + k
      have hai : ai < a.size := by
        rw [ha]
        exact flat3_lt hi hj hk
      have hjFlip : d1 - 1 - j < d1 := by
        omega
      have hbi : bi < b.size := by
        rw [hb]
        exact flat3_lt hi hjFlip hk
      acc + a.get ai hai * b.get bi hbi)

def inner3CoordStandaloneLoopRecursive (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float :=
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  FinTIndex.RowMajorLoop.foldIdxRecursive shape (Float.ofNat (token % 7) * 0.000001)
    (fun _linear idx acc =>
      let ⟨.prod (.prod (.leaf i) (.leaf j)) (.leaf k), hbounds⟩ := idx
      have hi : i < d0 := hbounds.1.1
      have hj : j < d1 := hbounds.1.2
      have hk : k < d2 := hbounds.2
      let ai := (i * d1 + j) * d2 + k
      let bi := (i * d1 + (d1 - 1 - j)) * d2 + k
      have hai : ai < a.size := by
        rw [ha]
        exact flat3_lt hi hj hk
      have hjFlip : d1 - 1 - j < d1 := by
        omega
      have hbi : bi < b.size := by
        rw [hb]
        exact flat3_lt hi hjFlip hk
      acc + a.get ai hai * b.get bi hbi)

def inner3CoordNatStandaloneLoop (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float :=
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  FinTIndex.RowMajorLoop.foldNatIdx shape (Float.ofNat (token % 7) * 0.000001)
    (fun _linear idx hbounds acc =>
      match idx with
      | .prod (.prod (.leaf i) (.leaf j)) (.leaf k) =>
          have hi : i < d0 := hbounds.1.1
          have hj : j < d1 := hbounds.1.2
          have hk : k < d2 := hbounds.2
          let ai := (i * d1 + j) * d2 + k
          let bi := (i * d1 + (d1 - 1 - j)) * d2 + k
          have hai : ai < a.size := by
            rw [ha]
            exact flat3_lt hi hj hk
          have hjFlip : d1 - 1 - j < d1 := by omega
          have hbi : bi < b.size := by
            rw [hb]
            exact flat3_lt hi hjFlip hk
          acc + a.get ai hai * b.get bi hbi)

def inner3CoordNatStandaloneLoopRecursive (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float :=
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  FinTIndex.RowMajorLoop.foldNatIdxRecursive shape (Float.ofNat (token % 7) * 0.000001)
    (fun _linear idx hbounds acc =>
      match idx with
      | .prod (.prod (.leaf i) (.leaf j)) (.leaf k) =>
          have hi : i < d0 := hbounds.1.1
          have hj : j < d1 := hbounds.1.2
          have hk : k < d2 := hbounds.2
          let ai := (i * d1 + j) * d2 + k
          let bi := (i * d1 + (d1 - 1 - j)) * d2 + k
          have hai : ai < a.size := by
            rw [ha]
            exact flat3_lt hi hj hk
          have hjFlip : d1 - 1 - j < d1 := by omega
          have hbi : bi < b.size := by
            rw [hb]
            exact flat3_lt hi hjFlip hk
          acc + a.get ai hai * b.get bi hbi)

def inner3CoordIntFinStandaloneLoop (d0 d1 d2 token : Nat) (a b : FloatArray)
    (ha : a.size = d0 * d1 * d2) (hb : b.size = d0 * d1 * d2) : Float :=
  let shape : Shape (.prod (.prod .leaf .leaf) .leaf) :=
    .prod (.prod (.leaf d0) (.leaf d1)) (.leaf d2)
  FinTIndex.RowMajorLoop.foldIntFinIdx shape (Float.ofNat (token % 7) * 0.000001)
    (fun _linear idx acc =>
      match idx with
      | ⟨.prod (.prod (.leaf i) (.leaf j)) (.leaf k), _hbounds⟩ =>
          let aiInt := (i * (d1 : Int) + j) * (d2 : Int) + k
          let biInt := (i * (d1 : Int) + ((d1 : Int) - 1 - j)) * (d2 : Int) + k
          let ai := aiInt.toNat
          let bi := biInt.toNat
          have hai : ai < a.size := by
            rw [ha]
            sorry
          have hbi : bi < b.size := by
            rw [hb]
            sorry
          acc + a.get ai hai * b.get bi hbi)

def matmulDirectChecksum (a b : FloatArray)
    (ha : a.size = matrixSize * matrixSize) (hb : b.size = matrixSize * matrixSize)
    (token : Nat) : Float :=
  checksum (matmulDirect matrixSize token a b ha hb)

def matmulRowMajorIterChecksum (a b : FloatArray)
    (ha : a.size = matrixSize * matrixSize) (hb : b.size = matrixSize * matrixSize)
    (token : Nat) : Float :=
  checksum (matmulRowMajorIter matrixSize token a b ha hb)

def matmulStandaloneLoopChecksum (a b : FloatArray)
    (ha : a.size = matrixSize * matrixSize) (hb : b.size = matrixSize * matrixSize)
    (token : Nat) : Float :=
  checksum (matmulStandaloneLoop matrixSize token a b ha hb)

def inner3DirectChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3Direct rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3RowMajorIterChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3RowMajorIter rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3StandaloneLoopChecksum (a b : FloatArray)
    (ha : a.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (hb : b.size = rank3Dim0 * rank3Dim1 * rank3Dim2)
    (token : Nat) : Float :=
  inner3StandaloneLoop rank3Dim0 rank3Dim1 rank3Dim2 token a b ha hb

def inner3CoordDirectChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordDirect rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def inner3CoordRowMajorIterChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordRowMajorIter rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def inner3CoordStandaloneLoopChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordStandaloneLoop rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def inner3CoordStandaloneLoopRecursiveChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordStandaloneLoopRecursive rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def inner3CoordNatStandaloneLoopChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordNatStandaloneLoop rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def inner3CoordNatStandaloneLoopRecursiveChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordNatStandaloneLoopRecursive rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def inner3CoordIntFinStandaloneLoopChecksum (a b : FloatArray)
    (ha : a.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (hb : b.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2)
    (token : Nat) : Float :=
  inner3CoordIntFinStandaloneLoop rank3CoordDim0 rank3CoordDim1 rank3CoordDim2 token a b ha hb

def run : IO Unit := do
  IO.println s!"FloatArray iterator benchmark payload: matmul={matrixSize}x{matrixSize}, dense-inner3={rank3Dim0}x{rank3Dim1}x{rank3Dim2}, coord-inner3={rank3CoordDim0}x{rank3CoordDim1}x{rank3CoordDim2}"
  IO.println "Comparisons are direct nested dimension loops vs rowMajorFinIter aggregate loops."
  IO.println "Inputs and per-run scalars depend on runtime IO.monoMsNow tokens to avoid compile-time folding."
  IO.println "name\ttotal\tper-run\tchecksum"
  let salt ← IO.monoMsNow
  let matA := makeFloatArray (matrixSize * matrixSize) (salt + 1)
  let matB := makeFloatArray (matrixSize * matrixSize) (salt + 2)
  let tensorA := makeFloatArray (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 3)
  let tensorB := makeFloatArray (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 4)
  let coordTensorA := makeFloatArray (rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2) (salt + 5)
  let coordTensorB := makeFloatArray (rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2) (salt + 6)
  have hmatA : matA.size = matrixSize * matrixSize := by
    simpa [matA] using makeFloatArray_size (matrixSize * matrixSize) (salt + 1)
  have hmatB : matB.size = matrixSize * matrixSize := by
    simpa [matB] using makeFloatArray_size (matrixSize * matrixSize) (salt + 2)
  have htensorA : tensorA.size = rank3Dim0 * rank3Dim1 * rank3Dim2 := by
    simpa [tensorA] using makeFloatArray_size (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 3)
  have htensorB : tensorB.size = rank3Dim0 * rank3Dim1 * rank3Dim2 := by
    simpa [tensorB] using makeFloatArray_size (rank3Dim0 * rank3Dim1 * rank3Dim2) (salt + 4)
  have hcoordTensorA : coordTensorA.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2 := by
    simpa [coordTensorA] using makeFloatArray_size (rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2) (salt + 5)
  have hcoordTensorB : coordTensorB.size = rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2 := by
    simpa [coordTensorB] using makeFloatArray_size (rank3CoordDim0 * rank3CoordDim1 * rank3CoordDim2) (salt + 6)
  timeRun "matmul direct nested loops" 2 (fun token => pure (matmulDirectChecksum matA matB hmatA hmatB token))
  timeRun "matmul standalone RowMajorLoop" 2 (fun token => pure (matmulStandaloneLoopChecksum matA matB hmatA hmatB token))
  timeRun "matmul rowMajorFinIter" 2 (fun token => pure (matmulRowMajorIterChecksum matA matB hmatA hmatB token))
  timeRun "dense inner3 direct nested loops" 64 (fun token => pure (inner3DirectChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 standalone RowMajorLoop" 64 (fun token => pure (inner3StandaloneLoopChecksum tensorA tensorB htensorA htensorB token))
  timeRun "dense inner3 rowMajorFinIter" 64 (fun token => pure (inner3RowMajorIterChecksum tensorA tensorB htensorA htensorB token))
  timeRun "coord inner3 direct nested loops" 64 (fun token => pure (inner3CoordDirectChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))
  timeRun "coord inner3 nat standalone RowMajorLoop" 64 (fun token => pure (inner3CoordNatStandaloneLoopChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))
  timeRun "coord inner3 nat recursive RowMajorLoop" 64 (fun token => pure (inner3CoordNatStandaloneLoopRecursiveChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))
  timeRun "coord inner3 IntFinTIndex RowMajorLoop" 64 (fun token => pure (inner3CoordIntFinStandaloneLoopChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))
  timeRun "coord inner3 standalone RowMajorLoop" 64 (fun token => pure (inner3CoordStandaloneLoopChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))
  timeRun "coord inner3 recursive RowMajorLoop" 64 (fun token => pure (inner3CoordStandaloneLoopRecursiveChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))
  timeRun "coord inner3 rowMajorFinIter" 64 (fun token => pure (inner3CoordRowMajorIterChecksum coordTensorA coordTensorB hcoordTensorA hcoordTensorB token))

end Tests.FloatArrayTensorBenchmark

def main : IO Unit :=
  Tests.FloatArrayTensorBenchmark.run
