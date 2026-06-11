import NumLean.Algebra.Deriving
import NumLean.Algebra.Float

namespace NumLean

structure Float2 where
  x : Float
  y : Float
deriving AddGroupOps, GroupOps

def add (a b : Float2) := (a + b)

def add' (a b : Float2) : Float2 := { x := a.x + b.x, y := a.y + b.y }

structure Vec2 (X : Type) where
  x : X
  y : X
deriving AddGroupOps, GroupOps

#synth AddGroupOps (Vec2 Float)
#synth GroupOps (Vec2 Float)

structure SizedVec2 (m : Nat) (X : Type) where
  x : X
  y : X
deriving AddGroupOps, GroupOps

#synth AddGroupOps (SizedVec2 4 Float)
#synth GroupOps (SizedVec2 4 Float)

end NumLean
