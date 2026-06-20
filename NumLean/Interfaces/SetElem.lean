import Lean

namespace NumLean

class SetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
              (valid : outParam (coll → idx → Prop)) where
  setElem (xs : coll) (i : idx) (v : elem) (h : valid xs i) : coll
  setElem_valid {xs : coll} {i j : idx} {v : elem} {hi : valid xs i} :
    valid xs j ↔ valid (setElem xs i v hi) j

export SetElem (setElem setElem_valid)

open SetElem
class LawfulSetElem (coll : Type u) (idx : Type v)
    {elem : outParam (Type w)} {valid : outParam (coll → idx → Prop)}
    [SetElem coll idx elem valid] [GetElem coll idx elem valid] : Prop where
  getElem_setElem_eq (xs : coll) (i : idx) (v : elem) (h : valid xs i) :
    getElem (setElem xs i v h) i (setElem_valid.1 h) = v
  getElem_setElem_neq (xs : coll) (i j : idx) (v : elem) (hi : valid xs i) (hj) :
    i≠j → getElem (setElem xs i v hi) j (hj) = getElem xs j (setElem_valid.2 hj)



open Lean in
/-- Turn an array of terms in into a tuple. -/
private def mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  `(term| ($(xs[0]!), $(xs[1:]),*))

class DefaultIndexOfRank (X : Type u) (r : Nat) (I : outParam (Type w))

open Lean in
initialize registerTraceClass `getElem_notation

open Lean Elab Term Meta in
/--
The syntax `x[i,j,k]` gets the element of `x : X` indexed by `(i,j,k)`.

Note that product is right associated thus `x[i,j,k]`, `x[i,(j,k)]` and `x[(i,j,k)]` result in
the same expression.
-/
elab:max (priority:=high+1) x:term noWs "[" is:term,* "]" : term => do
  try
    let rank := is.getElems.size
    let x ← elabTermAndSynthesize x none
    let X ← inferType x
    let Idx ← mkFreshTypeMVar
    let Elem ← mkFreshTypeMVar
    let Valid ← mkFreshExprMVar none
    let cls := (mkAppN (← mkConstWithFreshMVarLevels ``DefaultIndexOfRank) #[X, mkNatLit rank, Idx])
    let _ ← synthInstance cls
    trace[getElem_notation] "Default index type {Idx} of rank {rank} for {X}"
    let getElemCls := mkAppN (← mkConstWithFreshMVarLevels ``GetElem) #[X, Idx, Elem, Valid]
    let inst ← synthInstance getElemCls
    let i ← elabTerm (← liftMacroM (mkTuple is.getElems)) Idx
    -- todo: remplate this with a elaborator that calls (by get_elem_tactic)
    return ← mkAppOptM ``getElem #[X,Idx,Elem,Valid,inst,x,i,Expr.const ``True.intro []]
  catch e =>
    let i ← liftMacroM (mkTuple is.getElems)
    trace[getElem_notation] "Failed to infer default index type with error:\n{e.toMessageData}"
    return ← elabTerm (← `(getElem $x $i (by get_elem_tactic))) none


-- a[i] := x
macro (priority:=high) x:ident noWs "[" i:term "]" " := " xi:term : doElem => do
  `(doElem| $x:ident := setElem $x $i $xi (by get_elem_tactic))

-- a[i] := x
macro (priority:=high) x:ident noWs "[" i:term "]'" h:term " := " xi:term : doElem => do
  `(doElem| $x:ident := setElem $x $i $xi $h)


local instance {X n} : DefaultIndexOfRank (Vector X n) 1 (Fin n) := ⟨⟩

/-- info: fun i => #v[1, 2, 3, 4][i] : Fin 4 → Nat -/
#guard_msgs in
#check fun i => #v[1,2,3,4][i]


-- variable (A : Float^[a,b,c])
-- #check A[:,0,1]
-- #check A[:,1,:]
-- #check A[:,1,:]
-- #check A[3,1,:]
