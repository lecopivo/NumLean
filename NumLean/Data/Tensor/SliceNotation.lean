module

public import NumLean.Data.Tensor.View
public import NumLean.Data.HTuple.RangeNotation
public meta import NumLean.Data.HTuple.Basic
public meta import Lean

@[expose] public section

namespace NumLean
namespace Tensor

open Lean Elab Term Meta Macro

declare_syntax_cat tensor_slice_axis (behavior := both)
syntax hrange_axis : tensor_slice_axis
syntax "[" tensor_slice_axis,* "]" : tensor_slice_axis

syntax (name := tensorSliceNotation) term noWs "[" tensor_slice_axis,* "]&" : term

namespace SliceNotation

abbrev TermStx := TSyntax `term

meta def mkNatLit (n : Nat) : TermStx := Syntax.mkNumLit (toString n)

meta def natLit? (t : TermStx) : Option Nat := t.raw.isNatLit?

meta def numLit? (n : TSyntax `num) : Option Nat := n.raw.isNatLit?

meta def subStx (hi lo : TermStx) : MacroM TermStx := do
  match natLit? hi, natLit? lo with
  | some hi, some lo => pure (mkNatLit (hi - lo))
  | _, some 0 => pure hi
  | _, _ => `($hi - $lo)

inductive ShapeTree where
  | leaf (dim : TermStx) (value? : Option Nat)
  | prod (left right : ShapeTree)

instance : Inhabited ShapeTree where
  default := .leaf ⟨Syntax.missing⟩ none

meta partial def ShapeTree.toTerm : ShapeTree → MacroM TermStx
  | .leaf dim _ => `(HTuple.leaf $dim)
  | .prod left right => do
      `(HTuple.prod $(← left.toTerm) $(← right.toTerm))

meta partial def shapeTreeOfTerm : HTuple.Profile → TermStx → MacroM ShapeTree
  | .leaf, shape => do
      let dim ← `(($shape).toScalar)
      pure (.leaf dim none)
  | .prod left right, shape => do
      pure (.prod (← shapeTreeOfTerm left (← `(($shape).fst)))
                  (← shapeTreeOfTerm right (← `(($shape).snd))))

meta partial def shapeTreeOfExpr? (profile : HTuple.Profile) (shape : Expr) : TermElabM (Option ShapeTree) := do
  let shape ← instantiateMVars shape
  match profile with
  | .leaf =>
      let (fn, args) := shape.getAppFnArgs
      if fn == ``HTuple.leaf then
        if _h : 0 < args.size then
          let dim := args.back!
          let value? ←
            match dim with
            | .lit (.natVal n) => pure (some n)
            | _ => pure none
          return some (.leaf (← Term.exprToSyntax dim) value?)
      return none
  | .prod leftProfile rightProfile =>
      let (fn, args) := shape.getAppFnArgs
      if fn == ``HTuple.prod then
        if _h : 2 ≤ args.size then
          let leftExpr := args[args.size - 2]!
          let rightExpr := args[args.size - 1]!
          match ← shapeTreeOfExpr? leftProfile leftExpr, ← shapeTreeOfExpr? rightProfile rightExpr with
          | some left, some right => return some (.prod left right)
          | _, _ => return none
      return none

meta partial def natLitValue? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => pure (some n)
  | _ => do
      let e ← reduce e
      match e with
      | .lit (.natVal n) => pure (some n)
      | _ => pure none

meta def shapeTreeOfExpr (profile : HTuple.Profile) (shape : Expr) : TermElabM ShapeTree := do
  match ← shapeTreeOfExpr? profile shape with
  | some tree => pure tree
  | none => liftMacroM <| shapeTreeOfTerm profile (← Term.exprToSyntax shape)

meta partial def shapeTreeOfIndexType? (profile : HTuple.Profile) (I : Expr) : TermElabM (Option ShapeTree) := do
  let I ← instantiateMVars I
  match profile with
  | .leaf =>
      let (fn, args) := I.getAppFnArgs
      if fn == ``Fin then
        if _h : 0 < args.size then
          let dim := args.back!
          let value? ← natLitValue? dim
          return some (.leaf (← Term.exprToSyntax dim) value?)
      return none
  | .prod leftProfile rightProfile =>
      let (fn, args) := I.getAppFnArgs
      if fn == ``Prod then
        if _h : 2 ≤ args.size then
          let leftExpr := args[args.size - 2]!
          let rightExpr := args[args.size - 1]!
          match ← shapeTreeOfIndexType? leftProfile leftExpr,
              ← shapeTreeOfIndexType? rightProfile rightExpr with
          | some left, some right => return some (.prod left right)
          | _, _ => return none
      return none

meta def sourceShapeTreeOf (profile : HTuple.Profile) (I _shape : Expr) : TermElabM ShapeTree := do
  match ← shapeTreeOfIndexType? profile I with
  | some tree => pure tree
  | none => throwError "tensor slice notation could not recover tensor shape from index type{indentExpr I}"

meta def normalizeBoundStx (dim : TermStx) (bound : TermStx) : MacroM TermStx := do
  match bound with
  | `(term| - $n:num) => `($dim - $n)
  | _ => pure bound

meta def negNum? (bound : TermStx) : Option Nat :=
  match bound with
  | `(term| - $n:num) => numLit? n
  | _ => none

meta def rangeLenStx (_dim : TermStx) (dim? : Option Nat) (lo hi : TermStx) : MacroM TermStx := do
  match natLit? lo, natLit? hi with
  | some loNat, some hiNat => pure (mkNatLit (hiNat - loNat))
  | some loNat, none =>
      match dim? with
      | some dimNat => pure (mkNatLit (dimNat - loNat))
      | none => subStx hi lo
  | none, some _hiNat => subStx hi lo
  | none, none =>
      match dim?, negNum? lo, negNum? hi with
      | some _, some loNat, some hiNat => pure (mkNatLit (loNat - hiNat))
      | some dimNat, some loNat, none => pure (mkNatLit (dimNat - loNat))
      | _, _, _ => subStx hi lo

meta def leafHTupleStx (x : TermStx) : MacroM TermStx :=
  `(HTuple.leaf $x)

meta def prodHTupleStx (x y : TermStx) : MacroM TermStx :=
  `(HTuple.prod $x $y)

structure SliceOut where
  profile : HTuple.Profile
  shape : TermStx
  layout : TermStx

structure SliceBuild where
  point : TermStx
  out? : Option SliceOut

instance : Inhabited SliceOut where
  default := { profile := .leaf, shape := ⟨Syntax.missing⟩, layout := ⟨Syntax.missing⟩ }

instance : Inhabited SliceBuild where
  default := { point := ⟨Syntax.missing⟩, out? := none }

meta def isAtom (value : String) : Syntax → Bool
  | .atom _ value' => value == value'
  | _ => false

meta def singleAxis? (axis : TSyntax `tensor_slice_axis) : Option (TSyntax `hrange_axis) :=
  match axis.raw with
  | .node _ k args =>
      if k == ``Parser.Term.hole then none else
      if args.size == 1 then some ⟨args[0]!⟩ else none
  | _ => none

meta def parseNested? (axis : TSyntax `tensor_slice_axis) : Option (Array (TSyntax `tensor_slice_axis)) :=
  let args := axis.raw.getArgs
  if args.size == 3 && isAtom "[" args[0]! && isAtom "]" args[2]! then
    some (args[1]!.getArgs.filter (fun stx => !(isAtom "," stx)) |>.map (fun stx => ⟨stx⟩))
  else
    none

meta def axisBounds (dim : TermStx) (dim? : Option Nat) (axis : TSyntax `hrange_axis) : MacroM (Bool × TermStx × TermStx × TermStx) := do
  match axis with
  | `(hrange_axis| :) =>
      pure (true, ← `(0), dim, dim)
  | `(hrange_axis| - $n:num :) =>
      let lo ← `($dim - $n)
      let len ←
        match dim?, numLit? n with
        | some _, some n => pure (mkNatLit n)
        | _, _ => subStx dim lo
      pure (true, lo, dim, len)
  | `(hrange_axis| $lo:term :) =>
      let lo ← normalizeBoundStx dim lo
      pure (true, lo, dim, ← rangeLenStx dim dim? lo dim)
  | `(hrange_axis| : - $n:num) =>
      let hi ← `($dim - $n)
      let len ←
        match dim?, numLit? n with
        | some dimNat, some n => pure (mkNatLit (dimNat - n))
        | _, _ => subStx hi (← `(0))
      pure (true, ← `(0), hi, len)
  | `(hrange_axis| : $hi:term) =>
      let hi ← normalizeBoundStx dim hi
      pure (true, ← `(0), hi, hi)
  | `(hrange_axis| - $n:num : - $m:num) =>
      let lo ← `($dim - $n)
      let hi ← `($dim - $m)
      let len ←
        match numLit? n, numLit? m with
        | some n, some m => pure (mkNatLit (n - m))
        | _, _ => subStx hi lo
      pure (true, lo, hi, len)
  | `(hrange_axis| $lo:term : - $m:num) =>
      let lo ← normalizeBoundStx dim lo
      let hi ← `($dim - $m)
      pure (true, lo, hi, ← rangeLenStx dim dim? lo hi)
  | `(hrange_axis| - $n:num : $hi:term) =>
      let lo ← `($dim - $n)
      let hi ← normalizeBoundStx dim hi
      pure (true, lo, hi, ← subStx hi lo)
  | `(hrange_axis| $lo:term : $hi:term) =>
      let lo ← normalizeBoundStx dim lo
      let hi ← normalizeBoundStx dim hi
      pure (true, lo, hi, ← rangeLenStx dim dim? lo hi)
  | `(hrange_axis| $point:term) =>
      let point ← normalizeBoundStx dim point
      pure (false, point, point, ← `(1))
  | _ => Macro.throwUnsupported

meta partial def buildSlice (sourceProfile : HTuple.Profile)
    (sourceShape : ShapeTree) (axis : TSyntax `tensor_slice_axis) : MacroM SliceBuild := do
  match sourceProfile with
  | .leaf =>
      let some axis := singleAxis? axis
        | Macro.throwErrorAt axis "expected a slice axis for tensor rank leaf"
      let .leaf dim dim? := sourceShape
        | Macro.throwErrorAt axis "internal error: expected leaf source shape"
      let (isRange, lo, _hi, len) ← axisBounds dim dim? axis
      let point ← leafHTupleStx lo
      if isRange then
        let shape ← leafHTupleStx len
        let layout ← `(FinHTupleMap.contiguous1D (len := $len) (n := $dim) $lo (by first | omega | (simp; omega) | simp))
        pure { point, out? := some { profile := .leaf, shape, layout } }
      else
        pure { point, out? := none }
  | .prod left right =>
      let .prod leftShapeTree rightShapeTree := sourceShape
        | Macro.throwErrorAt axis "internal error: expected product source shape"
      let some axes := parseNested? axis
        | Macro.throwErrorAt axis "expected nested slice axes for tensor product rank"
      if axes.size != 2 then
        Macro.throwErrorAt axis "nested tensor slice rank mismatch: expected exactly two components"
      let leftShape ← leftShapeTree.toTerm
      let rightShape ← rightShapeTree.toTerm
      let leftBuild ← buildSlice left leftShapeTree ⟨axes[0]!⟩
      let rightBuild ← buildSlice right rightShapeTree ⟨axes[1]!⟩
      let point ← prodHTupleStx leftBuild.point rightBuild.point
      let out? ←
        match leftBuild.out?, rightBuild.out? with
        | none, none => pure none
        | some out, none => do
            let constRight ← `(FinHTupleMap.const $out.shape $rightShape $(rightBuild.point) (by get_elem_tactic))
            let layout ← `(($out.layout).prod $constRight)
            pure (some { out with layout })
        | none, some out => do
            let constLeft ← `(FinHTupleMap.const $out.shape $leftShape $(leftBuild.point) (by get_elem_tactic))
            let layout ← `(($constLeft).prod $out.layout)
            pure (some { out with layout })
        | some lout, some rout => do
            let shape ← prodHTupleStx lout.shape rout.shape
            let layout ← `(($lout.layout).pair $rout.layout)
            pure (some { profile := .prod lout.profile rout.profile, shape, layout })
      pure { point, out? }

meta def mkTopAxis (axes : Array (TSyntax `tensor_slice_axis)) : MacroM (TSyntax `tensor_slice_axis) := do
  match axes.toList with
  | [] => Macro.throwError "tensor slice notation needs at least one axis"
  | [axis] => pure axis
  | axis :: rest =>
      let mut args : Array Syntax := #[axis.raw]
      for axis in rest do
        args := args.push (mkAtom ",") |>.push axis.raw
      let node := Syntax.node SourceInfo.none `NumLean.Tensor.tensor_slice_axis_ #[mkAtom "[", Syntax.node SourceInfo.none nullKind args, mkAtom "]"]
      pure ⟨node⟩

meta def tensorType? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnf type
  let fn := type.getAppFn
  unless fn.isConstOf ``Tensor do
    return none
  let args := type.getAppArgs
  if h : 2 ≤ args.size then
    return some (args[0], args[1])
  return none

meta partial def profileOfExpr? (e : Expr) : MetaM (Option HTuple.Profile) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``HTuple.Profile.leaf, #[]) => pure (some .leaf)
  | (``HTuple.Profile.prod, #[left, right]) =>
      match ← profileOfExpr? left, ← profileOfExpr? right with
      | some left, some right => pure (some (.prod left right))
      | _, _ => pure none
  | _ => pure none

meta def elabKnownRank (rank : Expr) : TermElabM HTuple.Profile := do
  let rank ← instantiateMVars rank
  unless (← getMVars rank).isEmpty do
    throwError "tensor slice notation requires the tensor rank to be known at elaboration time"
  match ← profileOfExpr? rank with
  | some rank => pure rank
  | none =>
    throwError "tensor slice notation requires the tensor rank to be known at elaboration time"

end SliceNotation

open SliceNotation

@[term_elab tensorSliceNotation]
meta def elabTensorSliceNotation : TermElab := fun stx expectedType? => do
  match stx with
  | `(term| $x:term[$axes:tensor_slice_axis,*]&) => do
      let xExpr ← elabTerm x none
      let some (_X, I) ← tensorType? (← inferType xExpr)
        | throwErrorAt x "tensor slice notation expects a `Tensor`, got{indentExpr (← inferType xExpr)}"
      let nI ← mkFreshExprMVar (mkConst ``Nat)
      let rank ← mkFreshExprMVar (mkConst ``HTuple.Profile)
      let shapeType := mkAppN (mkConst ``HTuple [0]) #[mkConst ``Nat, rank]
      let shape ← mkFreshExprMVar shapeType
      let cls ← mkAppM ``TensorIndexType #[I, nI, rank, shape]
      let _ ← synthInstance cls
      let rank ← instantiateMVars rank
      let shape ← instantiateMVars shape
      let rankVal ← elabKnownRank rank
      let sourceShapeTerm ← Term.exprToSyntax shape
      let sourceShapeTree ← sourceShapeTreeOf rankVal I shape
      let topAxis ← liftMacroM <| mkTopAxis axes.getElems
      let built ← liftMacroM <| buildSlice rankVal sourceShapeTree topAxis
      let layoutStx ← liftMacroM <|
        match built.out? with
        | some out => pure out.layout
        | none => do
            `(FinHTupleMap.const (HTuple.leaf 1) $sourceShapeTerm $(built.point) (by get_elem_tactic))
      let xStx ← Term.exprToSyntax xExpr
      let viewStx ← `(Tensor.mkView $xStx $layoutStx)
      let injectiveViewStx ← `(($viewStx).toInjective (by simp [Tensor.mkView]; grind))
      match expectedType? with
      | some expected => elabTermEnsuringType injectiveViewStx expected
      | none => elabTerm injectiveViewStx none
  | _ => throwUnsupportedSyntax

end Tensor
end NumLean
