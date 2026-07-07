module

public import NumLean.Data.Vector.Basic
public import NumLean.Data.Tensor.Layout
public import NumLean.Data.FinHTuple.Fold
public import NumLean.Data.HTuple.Fold
public import NumLean.Meta.ForAll.Notation

@[expose] public section

namespace NumLean
namespace Tensor

namespace Layout

open Classical

/-- Update exactly the entries targeted by a flat layout.

`map layout xs f` traverses the logical source shape of `layout`; at each logical index `i`, it
replaces the physical entry `xs[layout i]` by `f i xs[layout i]`. Entries outside
`layout.rangeNat` are left unchanged. -/
def map {C : Type u} {α : Type v} {valid : C → Nat → Prop}
    [GetElem C Nat α valid] [SetElem C Nat α valid]
    {n : Nat} {r : Rank} {shape : Shape r}
    (layout : Layout shape h(n)) (xs : C)
    (f : FinHTuple shape → α → α)
    (hvalid : ∀ xs i, i < n → valid xs i := by intros; get_elem_tactic) : C :=
  Fold.fold (0...shape) xs fun i hi xs =>
    setElem xs (layout i : Nat)
      (f ⟨i, by grind⟩ (getElem xs (layout i : Nat)
        (hvalid xs (layout i : Nat) (by simpa using layout.inBounds i (by grind)))))
      (hvalid xs (layout i : Nat) (by simpa using layout.inBounds i (by grind)))

@[simp]
theorem getElem_map {α : Type u} {n : Nat} {r : Rank} {shape : Shape r}
    (layout : Layout shape h(n)) (xs : Vector α n) (f : FinHTuple shape → α → α)
    (hlayout : layout.Injective) (j : Nat) (hj : j < n) :
    (map layout xs f)[j]
      = if h : j ∈ layout.rangeNat then
          f (layout.rangeNatInv j h) xs[j]
        else
          xs[j] := by
  simpa only [map] using
    Fold.fold_layout_ext (map := layout) (init := xs) (hmap := hlayout)
      (f := fun i hi xi => f ⟨i, hi⟩ xi) (j := j) (hj := hj)

set_option backward.do.legacy false

def map₂ {C : Type u} {α : Type v} {valid : C → Nat → Prop}
    [GetElem C Nat α valid] [SetElem C Nat α valid]
    {n : Nat} {r : Rank} {shape : Shape r}
    (layout layout' : Layout shape h(n)) (xs : C)
    (f : FinHTuple shape → α → α → α)
    (hvalid : ∀ xs i, i < n → valid xs i := by intros; get_elem_tactic) : C :=
  Fold.fold (0...shape) xs fun i _hi xs =>
    let j : Nat := layout i
    let j' : Nat := layout' i
    let xj := getElem xs j (hvalid xs j (by simpa using layout.inBounds i (by grind)))
    let xj' := getElem xs j' (hvalid xs j' (by simpa using layout'.inBounds i (by grind)))
    setElem xs j (f ⟨i, by grind⟩ xj xj')
      (hvalid xs j (by simpa using layout.inBounds i (by grind)))

private theorem ne_apply_of_disjoint_range {n : Nat} {r : Rank} {shape : Shape r}
    {layout layout' : Layout shape h(n)}
    (h : Disjoint layout.range layout'.range) (i j : FinHTuple shape) :
    (layout i : Nat) ≠ (layout' j : Nat) := by
  intro hij
  have htuple : layout i = layout' j := by
    apply HTuple.toScalar_injective
    simpa using hij
  exact (Set.disjoint_left.mp h) ⟨i, rfl⟩ ⟨j, htuple.symm⟩

@[simp]
theorem getElem_map₂ {α : Type u} {n : Nat} {r : Rank} {shape : Shape r}
    (layout layout' : Layout shape h(n)) (xs : Vector α n) (f : FinHTuple shape → α → α → α)
    (hlayout : layout.Injective) (h : Disjoint layout.range layout'.range) (j : Nat) (hj : j < n) :
    (map₂ layout layout' xs f)[j]
      = if h : j ∈ layout.rangeNat then
          let i := (layout.rangeNatInv j h)
          let j' := layout' i
          f i  xs[j] xs[j']
        else
          xs[j] := by
  simp [map₂]
  let range := ((0 : Shape r)...shape)
  let stepCur : Vector α n → {i // i ∈ range} → Vector α n := fun ys i =>
    setElem ys (layout i.1 : Nat)
      (f ⟨i.1, by grind⟩ ys[(layout i.1 : Nat)] ys[(layout' i.1 : Nat)])
      (by simpa using layout.inBounds i.1 (by grind))
  let stepInit : Vector α n → {i // i ∈ range} → Vector α n := fun ys i =>
    setElem ys (layout i.1 : Nat)
      (f ⟨i.1, by grind⟩ ys[(layout i.1 : Nat)] xs[(layout' i.1 : Nat)])
      (by simpa using layout.inBounds i.1 (by grind))
  let sourcePreserved : Vector α n → Prop := fun ys =>
    ∀ k : FinHTuple shape, ys[(layout' k : Nat)] = xs[(layout' k : Nat)]
  have hfold_eq :
      Fold.fold (0...shape) (init := xs) (fun i _hi ys =>
        setElem ys (layout i : Nat)
          (f ⟨i, by grind⟩ ys[(layout i : Nat)] ys[(layout' i : Nat)])
          (by simpa using layout.inBounds i (by grind))) =
      Fold.fold (0...shape) (init := xs) (fun i _hi ys =>
        setElem ys (layout i : Nat)
          (f ⟨i, by grind⟩ ys[(layout i : Nat)] xs[(layout' i : Nat)])
          (by simpa using layout.inBounds i (by grind))) := by
    rw [LawfulFold.fold_eq_foldl, LawfulFold.fold_eq_foldl]
    change (NumLean.entries range).foldl stepCur xs = (NumLean.entries range).foldl stepInit xs
    have hmain : ∀ entries : List {i // i ∈ range}, ∀ ysCur ysInit : Vector α n,
        ysCur = ysInit → sourcePreserved ysInit →
        entries.foldl stepCur ysCur = entries.foldl stepInit ysInit ∧
          sourcePreserved (entries.foldl stepInit ysInit) := by
      intro entries
      induction entries with
      | nil =>
          intro ysCur ysInit heq hsrc
          exact ⟨heq, hsrc⟩
      | cons i entries ih =>
          intro ysCur ysInit heq hsrc
          have hreadInit :
              ysInit[(layout' i.1 : Nat)] = xs[(layout' i.1 : Nat)] :=
            hsrc (⟨i.1, by grind⟩ : FinHTuple shape)
          have hstep : stepCur ysCur i = stepInit ysInit i := by
            simp [stepCur, stepInit, heq, hreadInit]
          have hsrc_step : sourcePreserved (stepInit ysInit i) := by
            intro k
            have hneq : (layout i.1 : Nat) ≠ (layout' k : Nat) :=
              ne_apply_of_disjoint_range h (⟨i.1, by grind⟩ : FinHTuple shape) k
            have hget := LawfulSetElem.getElem_setElem_neq
              ysInit (layout i.1 : Nat) (layout' k : Nat)
              (f ⟨i.1, by grind⟩ ysInit[(layout i.1 : Nat)]
                xs[(layout' i.1 : Nat)])
              (by simpa using layout.inBounds i.1 (by grind))
              (by simpa using layout'.inBounds k.val k.isLt) hneq
            calc
              (stepInit ysInit i)[(layout' k : Nat)]
                  = ysInit[(layout' k : Nat)] := by
                    simpa [stepInit] using hget
              _ = xs[(layout' k : Nat)] := hsrc k
          exact ih (stepCur ysCur i) (stepInit ysInit i) hstep hsrc_step
    exact (hmain (NumLean.entries range) xs xs rfl (by intro k; rfl)).1
  calc
    (Fold.fold (0...shape) (init := xs) (fun i _hi ys =>
        setElem ys (layout i : Nat)
          (f ⟨i, by grind⟩ ys[(layout i : Nat)] ys[(layout' i : Nat)])
          (by simpa using layout.inBounds i (by grind))))[j]
        = (Fold.fold (0...shape) (init := xs) (fun i _hi ys =>
            setElem ys (layout i : Nat)
              (f ⟨i, by grind⟩ ys[(layout i : Nat)] xs[(layout' i : Nat)])
              (by simpa using layout.inBounds i (by grind))))[j] := by
          exact congrArg (fun ys => ys[j]) hfold_eq
    _ = (if h : j ∈ layout.rangeNat then
          f (layout.rangeNatInv j h) xs[j] xs[(layout' (layout.rangeNatInv j h) : Nat)]
        else
          xs[j]) := by
          simpa using
            (Fold.fold_layout_ext (map := layout) (init := xs) (hmap := hlayout)
              (f := fun i hi xi => f ⟨i, hi⟩ xi xs[(layout' i : Nat)]) (j := j) (hj := hj))


end Layout
end Tensor
end NumLean
