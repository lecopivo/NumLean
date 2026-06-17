import NumLean.Meta.ForAll

open NumLean TensorIndex Meta.ForAll

namespace Tests.ForAllBenchmark

structure Stats where
  sum : Float
  norm2 : Float
  max : Float
  min : Float
deriving Inhabited

def Stats.checksum (s : Stats) : Float :=
  s.sum + s.norm2 + s.max + s.min

def arraySize : Nat := 1000000

def uint64ArraySize : UInt64 := UInt64.ofNat arraySize

def rank3Dim : Nat := 100

def rank3Size : Nat := rank3Dim * rank3Dim * rank3Dim

def rank3DimUInt64 : UInt64 := UInt64.ofNat rank3Dim

def makeFloatArray (n salt : Nat) : FloatArray :=
  FloatArray.mk <| Array.ofFn fun i : Fin n =>
    Float.ofNat ((i.1 * 17 + salt * 31 + 13) % 1024) / 1024.0

theorem makeFloatArray_size (n salt : Nat) : (makeFloatArray n salt).size = n := by
  unfold makeFloatArray FloatArray.size
  exact Array.size_ofFn

partial def statsTailLoop (xs : FloatArray) (i : Nat)
    (sum norm2 max min : Float) : Stats :=
  if h : i < xs.size then
    let x := xs.get i h
    statsTailLoop xs (i + 1)
      (sum + x)
      (norm2 + x * x)
      (if max < x then x else max)
      (if x < min then x else min)
  else
    { sum, norm2, max, min }

def statsTail (xs : FloatArray) : Stats :=
  statsTailLoop xs 0 0.0 0.0 (-1.0) 2.0

def statsFor (xs : FloatArray) : Stats := Id.run do
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for h : i in 0...xs.size do
    have hi : i < xs.size := by
      simp only [Membership.mem] at h
      omega
    let x := xs.get i hi
    sum := sum + x
    norm2 := norm2 + x * x
    max := if max < x then x else max
    min := if x < min then x else min
  return { sum, norm2, max, min }

set_option backward.do.legacy false in
def statsForAll (xs : FloatArray) : Stats := Id.run do
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for_all h : i in 0...xs.size do
    have hi : i < xs.size := by
      simp only [Membership.mem] at h
      omega
    let x := xs.get i hi
    sum := sum + x
    norm2 := norm2 + x * x
    max := if max < x then x else max
    min := if x < min then x else min
  return { sum, norm2, max, min }

set_option backward.do.legacy false in
def statsUInt64ForAll (xs : FloatArray) (hxs : xs.size = arraySize) : Stats := Id.run do
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for_all h : i in ((0 : UInt64)...uint64ArraySize) do
    have hi : i.toNat < xs.size := by
      have hlt : i.toNat < uint64ArraySize.toNat := UInt64.lt_iff_toNat_lt.mp h.2
      have hupper : uint64ArraySize.toNat = arraySize := by native_decide
      omega
    let x := xs.get i.toNat hi
    sum := sum + x
    norm2 := norm2 + x * x
    max := if max < x then x else max
    min := if x < min then x else min
  return { sum, norm2, max, min }

partial def statsUInt64TailLoop (xs : FloatArray) (hxs : xs.size = arraySize)
    (i : UInt64) (sum norm2 max min : Float) : Stats :=
  if h : i < uint64ArraySize then
    have hi : i.toNat < xs.size := by
      have hlt : i.toNat < uint64ArraySize.toNat := UInt64.lt_iff_toNat_lt.mp h
      have hupper : uint64ArraySize.toNat = arraySize := by native_decide
      omega
    let x := xs.get i.toNat hi
    statsUInt64TailLoop xs hxs (i + 1)
      (sum + x)
      (norm2 + x * x)
      (if max < x then x else max)
      (if x < min then x else min)
  else
    { sum, norm2, max, min }

def statsUInt64Tail (xs : FloatArray) (hxs : xs.size = arraySize) : Stats :=
  statsUInt64TailLoop xs hxs 0 0.0 0.0 (-1.0) 2.0

def statsUInt64For (xs : FloatArray) (hxs : xs.size = arraySize) : Stats := Id.run do
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for h : i in ((0 : UInt64)...uint64ArraySize) do
    have hi : i.toNat < xs.size := by
      have hlt : i.toNat < uint64ArraySize.toNat := UInt64.lt_iff_toNat_lt.mp h.2
      have hupper : uint64ArraySize.toNat = arraySize := by native_decide
      omega
    let x := xs.get i.toNat hi
    sum := sum + x
    norm2 := norm2 + x * x
    max := if max < x then x else max
    min := if x < min then x else min
  return { sum, norm2, max, min }

def statsRank3NatFor (xs : FloatArray) : Stats := Id.run do
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for i in 0...rank3Dim do
    for j in 0...rank3Dim do
      for k in 0...rank3Dim do
        let flat := (i * rank3Dim + j) * rank3Dim + k
        let x := xs.get! flat
        sum := sum + x
        norm2 := norm2 + x * x
        max := if max < x then x else max
        min := if x < min then x else min
  return { sum, norm2, max, min }

def statsRank3UInt64For (xs : FloatArray) : Stats := Id.run do
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for i in ((0 : UInt64)...rank3DimUInt64) do
    for j in ((0 : UInt64)...rank3DimUInt64) do
      for k in ((0 : UInt64)...rank3DimUInt64) do
        let flat := (i * rank3DimUInt64 + j) * rank3DimUInt64 + k
        let x := xs.get! flat.toNat
        sum := sum + x
        norm2 := norm2 + x * x
        max := if max < x then x else max
        min := if x < min then x else min
  return { sum, norm2, max, min }

partial def statsRank3NatTailLoop (xs : FloatArray) (i j k : Nat)
    (sum norm2 max min : Float) : Stats :=
  if i < rank3Dim then
    if j < rank3Dim then
      if k < rank3Dim then
        let flat := (i * rank3Dim + j) * rank3Dim + k
        let x := xs.get! flat
        statsRank3NatTailLoop xs i j (k + 1)
          (sum + x)
          (norm2 + x * x)
          (if max < x then x else max)
          (if x < min then x else min)
      else
        statsRank3NatTailLoop xs i (j + 1) 0 sum norm2 max min
    else
      statsRank3NatTailLoop xs (i + 1) 0 0 sum norm2 max min
  else
    { sum, norm2, max, min }

def statsRank3NatTail (xs : FloatArray) : Stats :=
  statsRank3NatTailLoop xs 0 0 0 0.0 0.0 (-1.0) 2.0

partial def statsRank3UInt64TailLoop (xs : FloatArray) (i j k : UInt64)
    (sum norm2 max min : Float) : Stats :=
  if i < rank3DimUInt64 then
    if j < rank3DimUInt64 then
      if k < rank3DimUInt64 then
        let flat := (i * rank3DimUInt64 + j) * rank3DimUInt64 + k
        let x := xs.get! flat.toNat
        statsRank3UInt64TailLoop xs i j (k + 1)
          (sum + x)
          (norm2 + x * x)
          (if max < x then x else max)
          (if x < min then x else min)
      else
        statsRank3UInt64TailLoop xs i (j + 1) 0 sum norm2 max min
    else
      statsRank3UInt64TailLoop xs (i + 1) 0 0 sum norm2 max min
  else
    { sum, norm2, max, min }

def statsRank3UInt64Tail (xs : FloatArray) : Stats :=
  statsRank3UInt64TailLoop xs 0 0 0 0.0 0.0 (-1.0) 2.0

set_option backward.do.legacy false in
def statsHTupleNatForAll (xs : FloatArray) : Stats := Id.run do
  let shape : Shape _ := h(rank3Dim, rank3Dim, rank3Dim)
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for_all h(i, j, k) in 0...shape do
    let flat := (i * rank3Dim + j) * rank3Dim + k
    let x := xs.get! flat
    sum := sum + x
    norm2 := norm2 + x * x
    max := if max < x then x else max
    min := if x < min then x else min
  return { sum, norm2, max, min }

set_option backward.do.legacy false in
def statsHTupleUInt64ForAll (xs : FloatArray) : Stats := Id.run do
  let shape : TIndex UInt64 _ := h(rank3DimUInt64, rank3DimUInt64, rank3DimUInt64)
  let mut sum := 0.0
  let mut norm2 := 0.0
  let mut max := -1.0
  let mut min := 2.0
  for_all h(i, j, k) in 0...shape do
    let flat := (i * rank3DimUInt64 + j) * rank3DimUInt64 + k
    let x := xs.get! flat.toNat
    sum := sum + x
    norm2 := norm2 + x * x
    max := if max < x then x else max
    min := if x < min then x else min
  return { sum, norm2, max, min }

def padRight (width : Nat) (s : String) : String :=
  s.pushn ' ' (width - s.length)

def printBenchHeader : IO Unit := do
  IO.println s!"{padRight 18 "method"}{padRight 16 "range"}{padRight 10 "index"}{padRight 10 "n"}{padRight 12 "total"}{padRight 18 "per-run"}checksum"
  IO.println (String.ofList (List.replicate 114 '-'))

def printBenchRow (index range n method total perRun checksum : String) : IO Unit := do
  IO.println s!"{padRight 18 method}{padRight 16 range}{padRight 10 index}{padRight 10 n}{padRight 12 total}{padRight 18 perRun}{checksum}"

def timeRun (index range n method : String) (runs : Nat) (body : Nat → IO Float) : IO Unit := do
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
  printBenchRow index range n method s!"{elapsed}ms" s!"{perRun}ms/run" s!"{guard}"

def run : IO Unit := do
  IO.println "for_all benchmark payload: FloatArray statistics"
  IO.println "Computes sum, squared norm, maximum, and minimum."
  printBenchHeader
  let salt ← IO.monoMsNow
  let xs := makeFloatArray arraySize salt
  have hxs : xs.size = arraySize := by
    simpa [xs] using makeFloatArray_size arraySize salt
  timeRun "Nat" "0...n" s!"{arraySize}" "tail recursive" 64 fun token =>
    let s := statsTail xs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "Nat" "0...n" s!"{arraySize}" "direct for" 64 fun token =>
    let s := statsFor xs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "Nat" "0...n" s!"{arraySize}" "for_all" 64 fun token =>
    let s := statsForAll xs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "UInt64" "0...n" s!"{arraySize}" "tail recursive" 64 fun token =>
    let s := statsUInt64Tail xs hxs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "UInt64" "0...n" s!"{arraySize}" "direct for" 64 fun token =>
    let s := statsUInt64For xs hxs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "UInt64" "0...n" s!"{arraySize}" "for_all" 64 fun token =>
    let s := statsUInt64ForAll xs hxs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  let tensor := makeFloatArray rank3Size (salt + 1)
  timeRun "Nat" "0...h(n,n,n)" s!"{rank3Dim}" "tail recursive" 64 fun token =>
    let s := statsRank3NatTail tensor
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "Nat" "0...h(n,n,n)" s!"{rank3Dim}" "direct nested" 64 fun token =>
    let s := statsRank3NatFor tensor
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "Nat" "0...h(n,n,n)" s!"{rank3Dim}" "for_all" 64 fun token =>
    let s := statsHTupleNatForAll tensor
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "UInt64" "0...h(n,n,n)" s!"{rank3Dim}" "tail recursive" 64 fun token =>
    let s := statsRank3UInt64Tail tensor
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "UInt64" "0...h(n,n,n)" s!"{rank3Dim}" "direct nested" 64 fun token =>
    let s := statsRank3UInt64For tensor
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "UInt64" "0...h(n,n,n)" s!"{rank3Dim}" "for_all" 64 fun token =>
    let s := statsHTupleUInt64ForAll tensor
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)

end Tests.ForAllBenchmark

def main : IO Unit :=
  Tests.ForAllBenchmark.run
