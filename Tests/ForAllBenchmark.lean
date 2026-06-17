import NumLean.Meta.ForAll

open NumLean.Meta.ForAll

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

def makeFloatArray (n salt : Nat) : FloatArray :=
  FloatArray.mk <| Array.ofFn fun i : Fin n =>
    Float.ofNat ((i.1 * 17 + salt * 31 + 13) % 1024) / 1024.0

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

def run : IO Unit := do
  IO.println s!"for_all benchmark payload: FloatArray size={arraySize}"
  IO.println "Computes sum, squared norm, maximum, and minimum."
  IO.println "name\ttotal\tper-run\tchecksum"
  let salt ← IO.monoMsNow
  let xs := makeFloatArray arraySize salt
  timeRun "tail recursive stats" 64 fun token =>
    let s := statsTail xs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "standard for stats" 64 fun token =>
    let s := statsFor xs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)
  timeRun "for_all stats" 64 fun token =>
    let s := statsForAll xs
    pure (s.checksum + Float.ofNat (token % 7) * 0.000001)

end Tests.ForAllBenchmark

def main : IO Unit :=
  Tests.ForAllBenchmark.run
