import NumLean.Interfaces.FlatRepr.Deriving
import NumLean.Interfaces.FlatRepr.Float

namespace NumLean

structure Float3 where
  x : Float
  y : Float
  z : Float
deriving FlatRepr

#synth FlatRepr Float3 Float 3

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

#synth FlatRepr (Vec3 Float) Float 3

structure Mat3 (X : Type u) where
  r0 : Vec3 X
  r1 : Vec3 X
  r2 : Vec3 X
deriving FlatRepr

#synth FlatRepr (Mat3 Float) Float 9

structure SizedVec3 (m : Nat) (X : Type) where
  x : X
  y : X
  z : X
deriving FlatRepr

#synth FlatRepr (SizedVec3 4 Float) Float 3

end NumLean
