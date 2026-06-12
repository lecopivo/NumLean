import NumLean.Interfaces.FlatRepr.Deriving
import NumLean.Interfaces.FlatRepr.Float

namespace NumLean

structure Float3 where
  x : Float
  y : Float
  z : Float
deriving FlatRepr

def float3ToVector (x : Float3) := FlatRepr.toVector Float x

def float3Get (x : Float3) := fun i : Fin 3 => FlatRepr.getComp Float x i (by grind)

def float3Get' (x : Float3) (i : Fin 3) :=
  match i with
  | 0 => x.x
  | 1 => x.y
  | 2 => x.z

structure Vec3 (X : Type u) where
  x : X
  y : X
  z : X
deriving FlatRepr

structure Mat3 (X : Type u) where
  r0 : Vec3 X
  r1 : Vec3 X
  r2 : Vec3 X
deriving FlatRepr


structure SizedVec3 (m : Nat) (X : Type) where
  x : X
  y : X
  z : X
deriving FlatRepr

end NumLean
