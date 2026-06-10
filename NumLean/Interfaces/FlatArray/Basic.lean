import NumLean.Interfaces.ArrayType.Basic
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

/-- Type `X` can be stored in an array `Ks` whose scalar element type is `K`. -/
class FlatArray (X : Type u) (Ks : Type v) (nX : outParam Nat)
    {K : outParam (Type w)} [ArrayType Ks K]
    extends FlatRepr X K nX where

  /-- Read `X` from `ks` starting at scalar offset `off`. -/
  get (ks : Ks) (off : Nat) (h : off + nX ≤ ArrayType.size ks) : X
  get_spec (ks : Ks) (off : Nat) (h : off + nX ≤ ArrayType.size ks) :
    get ks off h =
      FlatRepr.fromVector (.ofFn fun i : Fin nX =>
        ArrayType.get ks (off + i.1) (by
          have hi := i.2
          omega))

  /-- Read `X` from `ks` starting at `USize` scalar offset `off`. -/
  uget (ks : Ks) (off : USize) (h : off.toNat + nX ≤ ArrayType.size ks) : X

  /-- Write `x` into `ks` starting at scalar offset `off`. -/
  set (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayType.size ks) : Ks
  set_spec (ks : Ks) (off : Nat) (x : X) (h : off + nX ≤ ArrayType.size ks) :
    set ks off x h =
      (ArrayType.fromArray <| _root_.Vector.toArray <|
        Fin.foldl (n:=nX) (init := _root_.Vector.mk (ArrayType.toArray ks) rfl)
          (fun acc i => acc.set (off + i.1) (FlatRepr.toVector x)[i]
            (by simp [← ArrayType.size_spec]; omega)))

  /-- Write `x` into `ks` starting at `USize` scalar offset `off`. -/
  uset (ks : Ks) (off : USize) (x : X) (h : off.toNat + nX ≤ ArrayType.size ks) : Ks

/-- The default flat array type for `X`. -/
class DefaultFlatArray (X : Type u) (Ks : outParam (Type v)) (nX : outParam Nat)
    {K : outParam (Type w)} [ArrayType Ks K]
    extends FlatArray X Ks nX

end NumLean
