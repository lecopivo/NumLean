module

public import NumLean.Interfaces.HasFlatRepr.Deriving

@[expose] public section

namespace NumLean.Tests.HasFlatReprDeriving

structure Float3 where
  x : Float
  y : Float
  z : Float
#derive_has_flat_repr Float3

def float3ToVector (x : Float3) := HasFlatRepr.toVector (Ks := Vector Float) x

def float3Get (x : Float3) := fun i : Fin 3 => HasFlatRepr.getComp (Ks := Vector Float) x i (by grind)

def float3Get' (x : Float3) (i : Fin 3) :=
  match i with
  | 0 => x.x
  | 1 => x.y
  | 2 => x.z

structure Vec3 (X : Type u) where
  x : X
  y : X
  z : X
#derive_has_flat_repr Vec3

structure Mat3 (X : Type u) where
  r0 : Vec3 X
  r1 : Vec3 X
  r2 : Vec3 X
#derive_has_flat_repr Mat3

variable (A : Type)

example : HasFlatRepr (Mat3 A) (Vector A) 9 := inferInstance
example : HasFlatRepr (Mat3 (Vec3 A)) (Vector A) 27 := inferInstance

structure SizedVec3 (m : Nat) (X : Type) where
  x : X
  y : X
  z : X
#derive_has_flat_repr SizedVec3

end NumLean.Tests.HasFlatReprDeriving
