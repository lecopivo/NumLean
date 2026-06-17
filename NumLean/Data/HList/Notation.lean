import NumLean.Data.HList.Basic

namespace NumLean

namespace HList

declare_syntax_cat hlist_profile_stx (behavior := both)
syntax "•" : hlist_profile_stx
syntax (priority := high) hlist_profile_stx ", " hlist_profile_stx,* : hlist_profile_stx
syntax (priority := high) "(" hlist_profile_stx ")" : hlist_profile_stx

open Lean Macro

private def mkListTerm (xs : Array Term) : MacroM Term := do
  let mut out ← `(List.nil)
  for x in xs.reverse do
    out ← `(List.cons $x $out)
  pure out

private partial def profileItems : TSyntax `hlist_profile_stx → MacroM (Array (TSyntax `hlist_profile_stx))
  | `(hlist_profile_stx| ( $x:hlist_profile_stx ) ) => do
      let grouped ← `(hlist_profile_stx| ($x:hlist_profile_stx))
      pure #[grouped]
  | `(hlist_profile_stx| • ) => do
      let item ← `(hlist_profile_stx| •)
      pure #[item]
  | `(hlist_profile_stx| $x:hlist_profile_stx, $xs:hlist_profile_stx,* ) => do
      let mut out ← profileItems x
      for x in xs.getElems do
        out := out ++ (← profileItems ⟨x⟩)
      pure out
  | _ => Macro.throwUnsupported

syntax:max "hlp(" hlist_profile_stx ")" : term

macro_rules
  | `(hlist_profile_stx| ( $x:hlist_profile_stx ) ) =>
      `(hlist_profile_stx| $x:hlist_profile_stx)
  | `(hlist_profile_stx| • ) =>
      `(Profile.leaf)
  | `(hlist_profile_stx| $x:hlist_profile_stx, $xs:hlist_profile_stx,* ) => do
      let mut items ← profileItems x
      for x in xs.getElems do
        items := items ++ (← profileItems ⟨x⟩)
      let elems ← items.mapM fun stx => do
        let stx ← `(hlist_profile_stx| ($stx:hlist_profile_stx))
        match ← Macro.expandMacro? stx.raw with
        | some stx => pure ⟨stx⟩
        | none => Macro.throwUnsupported
      let elems ← mkListTerm elems
      `(Profile.node $elems)
  | `(term| hlp($x:hlist_profile_stx)) => do
      let x ← `(hlist_profile_stx| ($x:hlist_profile_stx))
      match ← Macro.expandMacro? x.raw with
      | some x => pure x
      | none => Macro.throwUnsupported

private partial def mkProfileStx : Array (TSyntax `hlist_profile_stx) → Lean.PrettyPrinter.UnexpandM (TSyntax `hlist_profile_stx)
  | #[] => throw ()
  | #[x] => pure x
  | xs => do
      let x := xs[0]!
      let rest ← mkProfileStx (xs.extract 1 xs.size)
      `(hlist_profile_stx| $x:hlist_profile_stx, $rest:hlist_profile_stx)

private def profileStxOfTerm : TSyntax `term → Lean.PrettyPrinter.UnexpandM (TSyntax `hlist_profile_stx)
  | `(term| hlp($x:hlist_profile_stx)) => pure x
  | _ => throw ()

@[app_unexpander Profile.leaf] def unexpandHListProfileLeaf : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(hlp(•))

@[app_unexpander Profile.node] def unexpandHListProfileNode : Lean.PrettyPrinter.Unexpander
  | `($(_) [$x:term, $xs:term,*]) => do
      let elems ← (#[x.raw] ++ xs.getElems).mapM fun stx => profileStxOfTerm ⟨stx⟩
      let profile ← mkProfileStx elems
      `(hlp($profile:hlist_profile_stx))
  | _ => throw ()

declare_syntax_cat hlist_value_stx (behavior := both)
syntax term : hlist_value_stx
syntax (priority := high) hlist_value_stx ", " hlist_value_stx,* : hlist_value_stx
syntax (priority := high) "(" hlist_value_stx ")" : hlist_value_stx

private structure Parts where
  value : Term
  profile : Term
  deriving Inhabited

private partial def partsOf : TSyntax `hlist_value_stx → MacroM Parts
  | `(hlist_value_stx| ( $x:hlist_value_stx ) ) => partsOf x
  | `(hlist_value_stx| $x:term ) => do
      pure { value := ← `(HList.value $x), profile := ← `(Profile.leaf) }
  | `(hlist_value_stx| $x:hlist_value_stx, $xs:hlist_value_stx,* ) => do
      let parts ← (#[x.raw] ++ xs.getElems).mapM fun stx => partsOf ⟨stx⟩
      let values ← mkListTerm (parts.map (·.value))
      let profiles ← mkListTerm (parts.map (·.profile))
      pure {
        value := ← `(HList.node $values)
        profile := ← `(Profile.node $profiles)
      }
  | _ => Macro.throwUnsupported

private partial def tupleItems : TSyntax `hlist_value_stx → MacroM (Array (TSyntax `hlist_value_stx))
  | `(hlist_value_stx| ( $x:hlist_value_stx ) ) => do
      let grouped ← `(hlist_value_stx| ($x:hlist_value_stx))
      pure #[grouped]
  | `(hlist_value_stx| $x:term ) => do
      let item ← `(hlist_value_stx| $x:term)
      pure #[item]
  | `(hlist_value_stx| $x:hlist_value_stx, $xs:hlist_value_stx,* ) => do
      let mut out ← tupleItems x
      for x in xs.getElems do
        out := out ++ (← tupleItems ⟨x⟩)
      pure out
  | _ => Macro.throwUnsupported

private partial def tupleOf : TSyntax `hlist_value_stx → MacroM Term
  | `(hlist_value_stx| ( $x:hlist_value_stx ) ) => tupleOf x
  | `(hlist_value_stx| $x:term ) => `(HPTuple.leaf $x)
  | `(hlist_value_stx| $x:hlist_value_stx, $xs:hlist_value_stx,* ) => do
      let mut elems ← tupleItems x
      for x in xs.getElems do
        elems := elems ++ (← tupleItems ⟨x⟩)
      let mut out ← `(HPTuple.nil)
      for x in elems.reverse do
        let x ← tupleOf x
        out ← `(HPTuple.cons $x $out)
      pure out
  | _ => Macro.throwUnsupported

/-- Raw hierarchical list value notation. -/
syntax:max "hlv(" hlist_value_stx ")" : term

/-- Profile-indexed hierarchical tuple notation. -/
syntax:max "hl(" hlist_value_stx ")" : term

macro_rules
  | `(term| hlv($x:hlist_value_stx)) => do
      let parts ← partsOf x
      return parts.value
  | `(term| hl($x:hlist_value_stx)) => do
      tupleOf x

@[app_unexpander HPTuple.leaf] def unexpandHPTupleLeaf : Lean.PrettyPrinter.Unexpander
  | `($(_) $x:term) => `(hl($x:term))
  | _ => throw ()

@[app_unexpander HPTuple.cons] def unexpandHPTupleCons : Lean.PrettyPrinter.Unexpander
  | `($(_) hl($x:hlist_value_stx) HPTuple.nil) => `(hl($x:hlist_value_stx))
  | `($(_) hl($x:hlist_value_stx) hl($y:hlist_value_stx)) => `(hl($x:hlist_value_stx, $y:hlist_value_stx))
  | _ => throw ()

section Examples

example : hlp(•) = Profile.leaf := rfl
example : hlp(•, •) = Profile.node [Profile.leaf, Profile.leaf] := rfl
example : hlp(•, (•, •)) = Profile.node [Profile.leaf, Profile.node [Profile.leaf, Profile.leaf]] := rfl

example : hlv(10) = HList.value 10 := rfl
example : hlv(10, 20) = HList.node [HList.value 10, HList.value 20] := rfl
example : hlv(10, (20, 30)) = HList.node [HList.value 10, HList.node [HList.value 20, HList.value 30]] := rfl

example : (hl(10) : HPTuple Nat hlp(•)).toList = [10] := by simp
example : (hl(10, 20) : HPTuple Nat hlp(•, •)).toList = [10, 20] := by simp
example : (hl(10, (20, 30)) : HPTuple Nat hlp(•, (•, •))).toList = [10, 20, 30] := by simp

end Examples

end HList

end NumLean
