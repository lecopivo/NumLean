import Mathlib


structure Vec3 (R : Type) where
  (x y z : R)

#check ForIn

/-- As is effectivelly `Array A` -/
class ArrayType (As : Type u) (A : outParam (Type w)) where
  size : As → Nat
  usize : As → UInt64

  uget (xs : As) (i : UInt64) (h : i.toNat < size xs) : A
  get  (xs : As) (i : Nat) (h : i < size xs) : A

  uset (xs : As) (i : UInt64) (v : α) (h : i.toNat < size xs) : A
  set (xs : As) (i : Nat) (v : α) (h : i < size xs) : As


variable {R : Type} {Vec : Type → Nat → Type} -- [Scalar R] [VectorType Vec]

def addVectors (x y : Vec (Vec3 R) 10) : Vec (Vec3 R) 10 := Id.run do

  for i in [0:10] do
    x[i] += y[i]

  return x



theorem addVectors_linear : IsLinearMap ℝ fun xy : Fin 10 → (Vec3 ℝ) => addVectors xy.1 xy.2 := sorry



def sampleFun (n : Nat) (f : R → R) : Vec R n := Id.run do
  let mut data : Vec R n := 0
  for i in 0...n do
    let x := (i : R) / (n - 1 : R)
    vals[i] += f x
  return data


def sampleFunData {n} (data : Vec R n) (x : R) : R :=
  let dx := (1 : R) / (n - 1 : R)
  let ix := floor (x / dx)
  let wx := fmod x dx
  if 0 ≤ ix ∧ ix < n - 1 then
    let y0 := data[ix]
    let y1 := data[ix+1]
    y0 + wx * (y1 - y0)
  else
    0

open Filter Topology
theorem sampleFunData_convertes (x : ℝ) (hx : x ∈ Set.Ioo 0 1) (f : ℝ → ℝ) (hf : Continuous f) :
  Tendsto (fun n => sampleFunData (sampleFun n f) x) (atTop) (nhds (f x)) := sorry
