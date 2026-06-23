import Mathlib.Tactic

/-! Discusting AI generated tactic that is proving inequalities like `i * nX + j < nI * nX` that
show up all the time.

The spec of this tactic is effectivelly the test file `Tests/TBounds.lean` which states all the
inequalities we want to prove. -/

open Lean Elab Tactic Meta

namespace NumLean

namespace TBounds

theorem row_lt {i j nI nJ : Nat} (hi : i < nI) (hj : j < nJ) :
    i * nJ + j < nI * nJ := by
  calc
    i * nJ + j < i * nJ + nJ := by gcongr
    _ = (i + 1) * nJ := by ring
    _ ≤ nI * nJ := by gcongr; omega

theorem row_next_le {i nI nJ : Nat} (hi : i < nI) :
    i * nJ + nJ ≤ nI * nJ := by
  calc
    i * nJ + nJ = (i + 1) * nJ := by ring
    _ ≤ nI * nJ := by gcongr; omega

theorem row3_lt {i j k nI nJ nK : Nat} (hi : i < nI) (hj : j < nJ) (hk : k < nK) :
    (i * nJ + j) * nK + k < (nI * nJ) * nK := by
  exact row_lt (row_lt hi hj) hk

theorem row3_next_le {i j nI nJ nK : Nat} (hi : i < nI) (hj : j < nJ) :
    (i * nJ + j) * nK + nK ≤ (nI * nJ) * nK := by
  exact row_next_le (nJ := nK) (row_lt hi hj)

theorem row4_lt {i j k l nI nJ nK nL : Nat}
    (hi : i < nI) (hj : j < nJ) (hk : k < nK) (hl : l < nL) :
    (((i * nJ + j) * nK + k) * nL + l) < (((nI * nJ) * nK) * nL) := by
  exact row_lt (row3_lt hi hj hk) hl

theorem row4_next_le {i j k nI nJ nK nL : Nat}
    (hi : i < nI) (hj : j < nJ) (hk : k < nK) :
    (((i * nJ + j) * nK + k) * nL + nL) ≤ (((nI * nJ) * nK) * nL) := by
  exact row_next_le (nJ := nL) (row3_lt hi hj hk)

theorem stride_lt {xoff xinc xn n i : Nat}
    (hx : xoff + n * xinc ≤ xn) (hxinc : xinc ≠ 0) (hi : i < n) :
    xoff + i * xinc < xn := by
  have hxinc_pos : 0 < xinc := Nat.pos_of_ne_zero hxinc
  have hmul : i * xinc < n * xinc := Nat.mul_lt_mul_of_pos_right hi hxinc_pos
  exact lt_of_lt_of_le (Nat.add_lt_add_left hmul xoff) hx

theorem stride_lt_rco {xoff xinc xn n i : Nat}
    (hx : xoff + n * xinc ≤ xn) (hxinc : xinc ≠ 0)
    (hi : i ∈ (0...n : Std.Rco Nat)) :
    xoff + i * xinc < xn := by
  rw [Std.Rco.mem_iff] at hi
  exact stride_lt hx hxinc hi.2

theorem stride_lt_rco_of_bound {xoff xinc xn n i : Nat}
    (hx : xoff + n * xinc ≤ xn ∧ xinc ≠ 0) (hi : i ∈ (0...n : Std.Rco Nat)) :
    xoff + i * xinc < xn :=
  stride_lt_rco hx.1 hx.2 hi

end TBounds

private def isNatLtHyp (decl : LocalDecl) : MetaM Bool := do
  if !decl.isImplementationDetail then
    let t := decl.type
    let args := t.getAppArgs
    if t.getAppFn.isConstOf ``LT.lt && args.size ≥ 1 then
      isDefEq args[0]! (mkConst ``Nat)
    else
      return false
  else
    return false

private def isNatVar (decl : LocalDecl) : MetaM Bool := do
  if !decl.isImplementationDetail then
    isDefEq decl.type (mkConst ``Nat)
  else
    return false

private def finBoundSource? (decl : LocalDecl) : MetaM (Option Expr) := do
  if decl.isImplementationDetail then
    return none
  if decl.type.getAppFn.isConstOf ``Fin && decl.type.getAppNumArgs == 1 then
    return some decl.toExpr
  return none

private def tboundsCore (sources : Array Expr) : TacticM Unit := do
  try
    evalTactic (← `(tactic| first
      | omega
      | simp only [Std.Rco.mem_iff] at *; omega
      | apply TBounds.stride_lt_rco_of_bound <;> assumption
      | apply TBounds.stride_lt_rco <;> assumption
      | apply TBounds.stride_lt <;> assumption
      | apply TBounds.row4_lt <;> assumption
      | apply TBounds.row4_next_le <;> assumption
      | apply TBounds.row3_lt <;> assumption
      | apply TBounds.row3_next_le <;> assumption
      | apply TBounds.row_lt <;> assumption
      | apply TBounds.row_next_le <;> assumption
      | simp only [Std.Rco.mem_iff] at *; ring_nf; omega
      | ring_nf; omega))
    return
  catch _ => pure ()

  let lctx ← getLCtx
  let hs ← lctx.foldlM (init := #[]) fun acc decl => do
    if ← isNatLtHyp decl then
      return acc.push decl.toExpr
    else
      return acc
  let finHs ← lctx.foldlM (init := #[]) fun acc decl => do
    match ← finBoundSource? decl with
    | some i => return acc.push (← mkAppM ``Fin.isLt #[i])
    | none => return acc
  let ns ← lctx.foldlM (init := #[]) fun acc decl => do
    if ← isNatVar decl then
      return acc.push decl.toExpr
    else
      return acc

  let mut facts : Array Expr := #[]
  for i in sources do
    facts := facts.push (← mkAppM ``Fin.isLt #[i])
  for h in finHs do
    facts := facts.push h
  for h in hs do
    for n in ns do
      facts := facts.push (← mkAppOptM ``TBounds.row_next_le #[none, none, some n, some h])
  let hs := hs ++ finHs
  for a in [:hs.size] do
    for b in [a + 1:hs.size] do
      let h₁ := hs[a]!
      let h₂ := hs[b]!
      facts := facts.push (← mkAppM ``TBounds.row_lt #[h₁, h₂])
      for n in ns do
        facts := facts.push (← mkAppOptM ``TBounds.row3_next_le #[none, none, none, none, some n, some h₁, some h₂])
  for a in [:hs.size] do
    for b in [a + 1:hs.size] do
      for c in [b + 1:hs.size] do
        let h₁ := hs[a]!
        let h₂ := hs[b]!
        let h₃ := hs[c]!
        facts := facts.push (← mkAppM ``TBounds.row3_lt #[h₁, h₂, h₃])
        for n in ns do
          facts := facts.push (← mkAppOptM ``TBounds.row4_next_le #[none, none, none, none, none, none, some n, some h₁, some h₂, some h₃])
  for a in [:hs.size] do
    for b in [a + 1:hs.size] do
      for c in [b + 1:hs.size] do
        for d in [c + 1:hs.size] do
          facts := facts.push (← mkAppM ``TBounds.row4_lt #[hs[a]!, hs[b]!, hs[c]!, hs[d]!])

  let mut g ← getMainGoal
  for fact in facts do
    let fact ← instantiateMVars fact
    g ← g.assert (← mkFreshUserName `hbound) (← inferType fact) fact
    let (_, g') ← g.intro1P
    g := g'
  replaceMainGoal [g]
  evalTactic (← `(tactic| first | assumption | ring_nf at *; nlinarith))

elab "tbounds" : tactic => tboundsCore #[]

elab "tbounds" " using " xs:term,* : tactic => do
  let sources ← xs.getElems.mapM fun x => Term.elabTerm x none
  tboundsCore sources

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| tbounds)

end NumLean
