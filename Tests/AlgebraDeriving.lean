import NumLean.Meta.Deriving.Algebra
import NumLean.Data.Scalars.Float64.Algebra

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

structure SizedVec2 (m : Nat) (X : Type) where
  x : X
  y : X
deriving AddGroupOps, GroupOps

end NumLean
