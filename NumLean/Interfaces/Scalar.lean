import Mathlib.Algebra.Notation.Defs

namespace NumLean

class AddGroupOps (G : Type u) extends Add G, Sub G, Neg G, Zero G

class GroupOps (G : Type u) extends Mul G, Div G, Inv G, One G

class FieldOps (F : Type u) extends AddGroupOps F, GroupOps F

class RCLikeOps (K : Type u) (R : outParam (Type v)) extends FieldOps K where
  norm : K → R

class ModuleOps (𝕜 : Type u) (V : Type u) [FieldOps 𝕜] [AddGroupOps V]
  extends SMul 𝕜 V

class AddTorsorOps (V : outParam (Type u)) (A : Type v) [AddGroupOps V]
  extends VAdd V A, VSub V A


end NumLean
