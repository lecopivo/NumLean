



/-- `As` is an array with values of type `A` i.e. is isomoprhic to `Array A`. -/
class ArrayType (As : Type u) (A : outParam (Type v)) where
  toArray : As → Array A
  fromArray : Array A → As

/-- Attach default array type for value type `A` which is usually more efficient that `Array A`.

For example
- for `Float` we have `FloatArray`
- for `Real` we have `Array Real`
- for `UInt8` we have `ByteArray` -/
class DefaultArrayType (As : outParam (Type u)) (A : Type u) extends
  ArrayType As A


/-- Type `X` has flat representation as a collection of `K` i.e. is isomorphic to `Vector K n`.

Some types might be understood as a flat representation on different levels.  -/
class FlatRepr (X : Type u) (K : Type v) (n : outParam Nat) where
  -- specification only, probably too slow
  toVector : X → Vector K n
  fromVector : Vector K n → X

  -- getComp
  -- ugetComp
  -- setComp
  -- usetComp

/-- Default flat represetation of type `X`. -/
class DefaultFlatRepr (X : Type u) (K : outParam (Type v)) (n : outParam Nat) extends
  FlatRepr X K n

/-- Type `X` can be stored in an array `Ks` that is an array of `K`. -/
class FlatArray (X : Type u) (Ks : Type v) (nX : outParam Nat) {K : outParam (Type w)} [ArrayType Ks K]
  extends
    FlatRepr X K nX

/-- The default flat array type -/
class DafaultFlatArray (X : Type u) (Ks : outParam (Type v)) (nX : outParam Nat) {K : outParam (Type w)} [ArrayType Ks K]
  extends
    FlatArray X Ks nX
