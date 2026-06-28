module

public import NumLean.Experimental.Data.HList.Notation
import all NumLean.Experimental.Data.HList.Basic
public import NumLean.Interfaces.Order

@[expose] public section

namespace NumLean

namespace HList

namespace HPTuple

mutual

/-- Pointwise zero tuple. -/
def zero {α : Type u} [Zero α] : (p : Profile) → HPTuple α p
  | .leaf => leaf 0
  | .node ps =>
      let payload := zeroPayload ps
      { val := .node payload.vals, of_profile := payload.of_profile }

/-- Pointwise zero node payload. -/
def zeroPayload {α : Type u} [Zero α] : (ps : List Profile) → NodePayload α ps
  | [] => { vals := [], of_profile := .node_nil }
  | p :: ps =>
      let head := zero p
      let tail := zeroPayload ps
      { vals := head.val :: tail.vals,
        of_profile := .node_cons head.of_profile tail.of_profile }

end

mutual

/-- Pointwise one tuple. -/
def one {α : Type u} [One α] : (p : Profile) → HPTuple α p
  | .leaf => leaf 1
  | .node ps =>
      let payload := onePayload ps
      { val := .node payload.vals, of_profile := payload.of_profile }

/-- Pointwise one node payload. -/
def onePayload {α : Type u} [One α] : (ps : List Profile) → NodePayload α ps
  | [] => { vals := [], of_profile := .node_nil }
  | p :: ps =>
      let head := one p
      let tail := onePayload ps
      { vals := head.val :: tail.vals,
        of_profile := .node_cons head.of_profile tail.of_profile }

end

instance {α : Type u} [Zero α] {p : Profile} : Zero (HPTuple α p) where
  zero := zero p

instance {α : Type u} [One α] {p : Profile} : One (HPTuple α p) where
  one := one p

instance {α : Type u} [Add α] {p : Profile} : Add (HPTuple α p) where
  add := HPTuple.map₂ (· + ·)

instance {α : Type u} [Mul α] {p : Profile} : Mul (HPTuple α p) where
  mul := HPTuple.map₂ (· * ·)

instance {α : Type u} [Neg α] {p : Profile} : Neg (HPTuple α p) where
  neg := HPTuple.map Neg.neg

instance {α : Type u} [Sub α] {p : Profile} : Sub (HPTuple α p) where
  sub := HPTuple.map₂ (· - ·)

instance (priority := low) {R : Type u} {α : Type v} [SMul R α] {p : Profile} :
    SMul R (HPTuple α p) where
  smul r := HPTuple.map (fun x => r • x)

instance {α : Type u} [LT α] {p : Profile} : LT (LexOrder (HPTuple α p)) where
  lt x y := NumLean.List.lexLT x.val.toList y.val.toList

instance {α : Type u} [LT α] {p : Profile} : LE (LexOrder (HPTuple α p)) where
  le x y := NumLean.List.lexLE x.val.toList y.val.toList

instance {α : Type u} [LT α] {p : Profile} : LT (ColexOrder (HPTuple α p)) where
  lt x y := NumLean.List.colexLT x.val.toList y.val.toList

instance {α : Type u} [LT α] {p : Profile} : LE (ColexOrder (HPTuple α p)) where
  le x y := NumLean.List.colexLE x.val.toList y.val.toList

instance {α : Type u} [LT α] {p : Profile} : LT (ElementwiseOrder (HPTuple α p)) where
  lt x y := NumLean.List.elementwiseLT x.val.toList y.val.toList

instance {α : Type u} [LE α] {p : Profile} : LE (ElementwiseOrder (HPTuple α p)) where
  le x y := NumLean.List.elementwiseLE x.val.toList y.val.toList

/-- The basis tuple whose selected leaf is `1` and all other leaves are `0`. -/
def basis {α : Type u} [Zero α] [One α] {p : Profile} (i : Index p) : HPTuple α p :=
  (zero p).set i 1

/-- All basis tuples for a profile, arranged with the same profile. -/
def basisTuple {α : Type u} [Zero α] [One α] (p : Profile) : HPTuple (HPTuple α p) p :=
  ofFn (basis (α := α))

section Examples

example : (0 : HPTuple Nat hlp(•)).toList = [0] := by cbv

example : (0 : HPTuple Nat hlp(•, •)).toList = [0, 0] := by cbv

example : ((hl(1, 2) : HPTuple Nat hlp(•, •)) + hl(3, 4)).toList = [4, 6] := by cbv

example : ((2 : Nat) • (hl(3, (4, 5)) : HPTuple Nat hlp(•, (•, •)))).toList = [6, 8, 10] := by cbv

end Examples

end HPTuple

end HList

end NumLean
