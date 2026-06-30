module

public import NumLean.Data.HTuple.Basic
public import NumLean.Data.HTuple.GetElemTactic
public import Lean

@[expose] public section

namespace NumLean

namespace HTuple

declare_syntax_cat hrange_axis (behavior := both)
syntax term : hrange_axis
syntax ":" : hrange_axis
syntax term ":" : hrange_axis
syntax ":" term : hrange_axis
syntax term ":" term : hrange_axis

open Lean Elab Term Meta Macro

abbrev TermStx := TSyntax `term

meta def mkNatLit (n : Nat) : TermStx := Syntax.mkNumLit (toString n)

meta def mkProfileStx : Nat → MacroM TermStx
  | 0 => Macro.throwError "range notation needs at least one ':' axis; all-point indexing is not a range"
  | 1 => `(HTuple.Profile.leaf)
  | n + 2 => do
      let right ← mkProfileStx (n + 1)
      `(HTuple.Profile.prod HTuple.Profile.leaf $right)

meta def mkTupleStx : List TermStx → MacroM TermStx
  | [] => Macro.throwError "internal error: range slice tuple is empty"
  | [x] => `(HTuple.leaf $x)
  | x :: xs => do
      let rest ← mkTupleStx xs
      `(HTuple.prod (HTuple.leaf $x) $rest)

meta partial def htupleLeafTerms : TSyntax `htuple_stx → MacroM (Array TermStx)
  | `(htuple_stx| ( $x:htuple_stx ) ) => htupleLeafTerms x
  | `(htuple_stx| $x:term ) => pure #[x]
  | `(htuple_stx| $x:htuple_stx , $y:htuple_stx, $ys:htuple_stx,* ) => do
      let left ← htupleLeafTerms x
      let right ← htupleLeafTerms y
      let mut out := left ++ right
      for z in ys.getElems do
        out := out ++ (← htupleLeafTerms z)
      pure out
  | `(htuple_stx| $x:htuple_stx , $y:htuple_stx ) => do
      pure ((← htupleLeafTerms x) ++ (← htupleLeafTerms y))
  | _ => Macro.throwUnsupported

meta def shapeDims? (shape : TermStx) : MacroM (Option (Array TermStx)) := do
  match shape with
  | `(term| h($xs:htuple_stx)) => pure (some (← htupleLeafTerms xs))
  | _ => pure none

meta def dimAtStx (shape : TermStx) (shapeDims? : Option (Array TermStx)) (i : Nat) : MacroM TermStx := do
  if let some dims := shapeDims? then
    if h : i < dims.size then
      return dims[i]
  let idx := mkNatLit i
  `(HTuple.toList $shape |>.getD $idx 0)

meta def normalizeBoundStx (dim : TermStx) (bound : TermStx) : MacroM TermStx := do
  match bound with
  | `(term| - $n:num) => `($dim - $n)
  | _ => pure bound

meta def axisBoundsStx (shape : TermStx) (shapeDims? : Option (Array TermStx))
    (axis : Syntax) (i : Nat) : MacroM (Option (TermStx × TermStx)) := do
  let dim ← dimAtStx shape shapeDims? i
  match axis with
  | `(hrange_axis| :) =>
      `(0) >>= fun lo => pure (some (lo, dim))
  | `(hrange_axis| $lo:term :) =>
      let lo ← normalizeBoundStx dim lo
      pure (some (lo, dim))
  | `(hrange_axis| : $hi:term) =>
      let hi ← normalizeBoundStx dim hi
      `(0) >>= fun lo => pure (some (lo, hi))
  | `(hrange_axis| $lo:term : $hi:term) =>
      let lo ← normalizeBoundStx dim lo
      let hi ← normalizeBoundStx dim hi
      pure (some (lo, hi))
  | `(hrange_axis| $_:term) =>
      pure none
  | _ => Macro.throwUnsupported

meta def inputAtStx (profile : TermStx) (x : Ident) (i : Nat) : MacroM TermStx := do
  let idx := mkNatLit i
  `(HTuple.get $x (HTuple.Index.ofFin $profile (⟨$idx, by decide⟩ : Fin ($profile).size)))

meta def axisValueStx (shape : TermStx) (shapeDims? : Option (Array TermStx))
    (profile : TermStx) (x : Ident) (axis : Syntax) (axisIdx sliceIdx : Nat) :
    MacroM (TermStx × Nat) := do
  let dim ← dimAtStx shape shapeDims? axisIdx
  match axis with
  | `(hrange_axis| $point:term) =>
      let point ← normalizeBoundStx dim point
      pure (point, sliceIdx)
  | _ =>
      let value ← inputAtStx profile x sliceIdx
      pure (value, sliceIdx + 1)

meta def mkAxisValueStx (shape : TermStx) (shapeDims? : Option (Array TermStx))
    (profile : TermStx) (x : Ident) (axes : List Syntax) (axisIdx : Nat) (sliceIdx : Nat)
    (outIdx : TermStx) : MacroM TermStx := do
  match axes with
  | [] => `(0)
  | axis :: rest =>
      let (value, sliceIdx) ← axisValueStx shape shapeDims? profile x axis axisIdx sliceIdx
      let fallback ← mkAxisValueStx shape shapeDims? profile x rest (axisIdx + 1) sliceIdx outIdx
      let idx := mkNatLit axisIdx
      `(if ($outIdx).toFin.val = $idx then $value else $fallback)

meta def mkEmbedStx (shape : TermStx) (shapeDims? : Option (Array TermStx))
    (profile : TermStx) (axes : List Syntax) : MacroM TermStx := do
  let x := mkIdent `x
  let i := mkIdent `i
  let value ← mkAxisValueStx shape shapeDims? profile x axes 0 0 i
  `(fun $x => HTuple.ofFn (fun $i => $value))

structure RangePartsStx where
  profile : TermStx
  lower : TermStx
  upper : TermStx
  embed : TermStx
  range : TermStx

meta def mkRangePartsStx (shape : TermStx) (axes : List Syntax) : MacroM (Option RangePartsStx) := do
  let shapeDims? ← shapeDims? shape
  let mut lows : List Term := []
  let mut highs : List Term := []
  for h : i in [0:axes.length] do
    if let some (lo, hi) ← axisBoundsStx shape shapeDims? axes[i] i then
      lows := lows.concat lo
      highs := highs.concat hi
  if lows.isEmpty then
    return none
  let profile ← mkProfileStx lows.length
  let lower ← mkTupleStx lows
  let upper ← mkTupleStx highs
  let embed ← mkEmbedStx shape shapeDims? profile axes
  let range ← `(($lower)...($upper))
  pure (some { profile, lower, upper, embed, range })

/-- Elaborated pieces of range notation.  The current term elaborator returns `range`; `embed` is
computed here so later indexing/slicing elaborators can build the reindexing function without
re-parsing the notation. -/
structure RangeParts where
  source : Expr
  sourceProfile : Expr
  profile : Expr
  lower : Expr
  upper : Expr
  embed : Expr
  range : Expr

meta def inferHTupleNatProfile (shape : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType shape)
  match type.getAppFnArgs with
  | (``HTuple, #[natTy, profile]) =>
      unless ← isDefEq natTy (mkConst ``Nat) do
        throwError "range shape must have type `HTuple Nat p`, got{indentExpr type}"
      instantiateMVars profile
  | _ => throwError "range shape must have type `HTuple Nat p`, got{indentExpr type}"

/-- Elaborate `hr[shape](axes...)` into clean expression pieces.

Returns `none` when all axes are point axes, so callers can fall back to point indexing. -/
meta def elabRangeParts (shapeStx : TermStx) (axes : Array (TSyntax `hrange_axis)) :
    TermElabM (Option RangeParts) := do
  let some partsStx ← liftMacroM <| mkRangePartsStx shapeStx axes.toList
    | return none
  let source ← elabTerm shapeStx none
  let sourceProfile ← inferHTupleNatProfile source
  let profile ← elabTerm partsStx.profile (some (mkConst ``HTuple.Profile))
  let tupleType := mkAppN (mkConst ``HTuple [0]) #[mkConst ``Nat, profile]
  let lower ← elabTerm partsStx.lower (some tupleType)
  let upper ← elabTerm partsStx.upper (some tupleType)
  let sourceType := mkAppN (mkConst ``HTuple [0]) #[mkConst ``Nat, sourceProfile]
  let embedType ← mkArrow tupleType sourceType
  let embed ← elabTerm partsStx.embed (some embedType)
  let rangeType := mkApp (mkConst ``Std.Rco [0]) tupleType
  let range ← elabTerm partsStx.range (some rangeType)
  return some { source, sourceProfile, profile, lower, upper, embed, range }

/-- Range-only slicing notation for hierarchical tuples.

Examples:
  - `hr[10](:) = h(0)...h(10)`
  - `hr[10,20](2:4, :5) = h(2,0)...h(4,5)`
  - `hr[10, 20](:-1, -1:) = h(0,19)...h(9,20)`
  - `hr[10, 20](2:4, 5) = h(2)...h(4)`
-/
syntax (name := hRangeNotation) "hr[" htuple_stx "](" hrange_axis,* ")" : term

@[term_elab hRangeNotation]
meta def elabHRangeNotation : TermElab := fun stx _expectedType? => do
  match stx with
  | `(term| hr[$shape:htuple_stx]($axes:hrange_axis,*)) => do
      let shape ← `(term| h($shape:htuple_stx))
      match ← elabRangeParts shape axes.getElems with
      | some parts => return parts.range
      | none => throwError "range notation needs at least one ':' axis; all-point indexing is not a range"
  | _ => throwUnsupportedSyntax

section Examples

section OneDimensionalLiteral

example : hr[10](:) = h(0)...h(10) := rfl

example : hr[10](2:) = h(2)...h(10) := rfl

example : hr[10](:5) = h(0)...h(5) := rfl

example : hr[10](2:5) = h(2)...h(5) := rfl

example : hr[10](:-1) = h(0)...h(9) := rfl

example : hr[10](-3:) = h(7)...h(10) := rfl

end OneDimensionalLiteral

section OneDimensionalSymbolic

example (n : Nat) : hr[n](:) = h(0)...h(n) := rfl

example (n : Nat) : hr[n](2:) = h(2)...h(n) := rfl

example (n : Nat) : hr[n](:5) = h(0)...h(5) := rfl

example (n : Nat) : hr[n](2:5) = h(2)...h(5) := rfl

example (n : Nat) : hr[n](:-1) = h(0)...h(n - 1) := rfl

example (n : Nat) : hr[n](-3:) = h(n - 3)...h(n) := rfl

example (n k : Nat) : hr[n](k:) = h(k)...h(n) := rfl

example (n k : Nat) : hr[n](:k) = h(0)...h(k) := rfl

example (n k l : Nat) : hr[n](k:l) = h(k)...h(l) := rfl

end OneDimensionalSymbolic

section MixedAxes

example : hr[10, 8](:, :) = h(0, 0)...h(10, 8) := rfl

example : hr[10, 8](5, :) = h(0)...h(8) := rfl

example : hr[10, 8](:, 5) = h(0)...h(10) := rfl

example (n m : Nat) : hr[n, m](-3:, :5) = h(n - 3, 0)...h(n, 5) := rfl

example (n m : Nat) : hr[n, m](2:5, 3) = h(2)...h(5) := rfl

example (n m : Nat) : hr[n, m](3, 2:5) = h(2)...h(5) := rfl

end MixedAxes

section AllPointRejection

/-- error: range notation needs at least one ':' axis; all-point indexing is not a range -/
#guard_msgs in
#check hr[10](5)

end AllPointRejection

section Membership

example : h(2) ∈ h(0)...h(10) := by
  get_elem_tactic

example (n : Nat) (h : n > 10) : h(n - 2) ∈ h(n - 3)...h(n) := by
  get_elem_tactic

example (n : Nat) (h : n > 10) : h(n - 2) ∈ hr[n](-3:) := by
  get_elem_tactic

example (n : Nat) (h : n > 10) : h(n - 2) ∈ hr[n, 10](-3:) := by
  get_elem_tactic

example (n : Nat) (h : n > 10) : h(n - 2, 3) ∈ hr[n, 10](-3:, :5) := by
  get_elem_tactic


end Membership

end Examples

end HTuple

end NumLean
