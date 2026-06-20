import NumLean.Data.Vector.Basic
import Mathlib.Data.Set.Basic

namespace NumLean

namespace Vector

namespace FoldMap

theorem List.foldl_eq_foldl_filter_of_neutral {α β : Type u} (entries : List α)
    (step : β → α → β) (init : β) (p : α → Prop) [DecidablePred p]
    (hneutral : ∀ acc a, ¬ p a → step acc a = acc) :
    entries.foldl step init = (entries.filter p).foldl step init := by
  induction entries generalizing init with
  | nil => rfl
  | cons a entries ih =>
      by_cases ha : p a
      · simp [ha, ih]
      · simp [ha]
        rw [hneutral init a ha]
        exact ih init

/-- Pointwise extensionality for vector folds.

If reading index `i` after one vector step is described by a scalar transition `readStep`, then
reading `i` after the full vector fold is the scalar fold of `readStep` over the same entries. -/
theorem foldl_get_eq_foldl_read {α K : Type u} {m : Nat} (entries : List α)
    (init : Vector K m) (step : Vector K m → α → Vector K m) (i : Fin m)
    (readStep : α → K → K)
    (hstep : ∀ acc a, (step acc a)[i] = readStep a acc[i]) :
    (entries.foldl step init)[i] =
      entries.foldl (fun x a => readStep a x) init[i] := by
  induction entries generalizing init with
  | nil => rfl
  | cons a entries ih =>
      rw [List.foldl_cons, ih]
      rw [hstep]
      rfl

/-- Pointwise vector-fold extensionality with neutral iterations removed.

This is useful for loop proofs: for a fixed read index, choose `p` to select exactly the iterations
that can modify that index. All other iterations disappear from the scalar fold. -/
theorem foldl_get_eq_foldl_read_filter {α K : Type u} {m : Nat} (entries : List α)
    (init : Vector K m) (step : Vector K m → α → Vector K m) (i : Fin m)
    (readStep : α → K → K) (p : α → Prop) [DecidablePred p]
    (hstep : ∀ acc a, (step acc a)[i] = readStep a acc[i])
    (hneutral : ∀ x a, ¬ p a → readStep a x = x) :
    (entries.foldl step init)[i] =
      (entries.filter p).foldl (fun x a => readStep a x) init[i] := by
  rw [foldl_get_eq_foldl_read entries init step i readStep hstep]
  rw [List.foldl_eq_foldl_filter_of_neutral entries (fun x a => readStep a x) init[i] p]
  intro acc a hpa
  exact hneutral acc a hpa


open Classical in
/-- Remove iterations that cannot affect the dependency cone of a read coordinate.

This generic form works for any mutable state `σ` observed through a read function
`read : σ → ι → β`. For a fixed coordinate `i`, entries outside `affectors i` may be
discarded when they preserve every coordinate in `deps i`, and all retained steps compute reads
on `deps i` only from previous reads on `deps i`. -/
theorem foldl_get_eq_foldl_filter_affectors {α : Type u} {σ : Type v} {ι : Type w}
    {β : Type x} (entries : List α) (init : σ) (step : σ → α → σ)
    (read : σ → ι → β) (deps : ι → Set ι) (affectors : ι → Set α) (i : ι)
    (hself : i ∈ deps i)
    (hpreserve : ∀ j ∈ deps i, ∀ a ∉ affectors i, ∀ xs,
      read (step xs a) j = read xs j)
    (hdeps : ∀ a xs ys,
      (∀ j ∈ deps i, read xs j = read ys j) →
      ∀ j ∈ deps i, read (step xs a) j = read (step ys a) j) :
    read (entries.foldl step init) i =
      read ((entries.filter fun a => a ∈ affectors i).foldl step init) i := by
  have aux : ∀ (entries : List α) (full filtered : σ),
      (∀ j ∈ deps i, read full j = read filtered j) →
      ∀ j ∈ deps i, read (entries.foldl step full) j =
        read ((entries.filter fun a => a ∈ affectors i).foldl step filtered) j := by
    intro entries
    induction entries with
  | nil =>
      intro full filtered hagree j hj
      exact hagree j hj
  | cons a entries ih =>
      intro full filtered hagree j hj
      by_cases ha : a ∈ affectors i
      · simp [ha]
        apply ih (step full a) (step filtered a)
        intro k hk
        exact hdeps a full filtered hagree k hk
        · exact hj
      · simp [ha]
        apply ih (step full a) filtered
        intro k hk
        exact (hpreserve k hk a ha full).trans (hagree k hk)
        exact hj
  exact aux entries init init (by intro j _; rfl) i hself

open Classical in
/-- Vector-specialized wrapper around `foldl_get_eq_foldl_filter_affectors`.

For a fixed coordinate `i`, `deps i` is the set of coordinates whose values must be preserved
to keep the final read at `i` unchanged. If entries outside `affectors i` preserve every
coordinate in `deps i`, and every step computes coordinates in `deps i` only from `deps i`,
then reading `i` after the full fold is the same as reading `i` after filtering to
`affectors i`. -/
theorem foldl_get_eq_foldl_filter_affectors_vector {α K : Type u} {m : Nat} (entries : List α)
    (init : Vector K m) (step : Vector K m → α → Vector K m)
    (deps : Fin m → Set (Fin m)) (affectors : Fin m → Set α) (i : Nat) (h : i < m)
    (hself : ⟨i,h⟩ ∈ deps ⟨i,h⟩)
    (hpreserve : ∀ j ∈ deps ⟨i,h⟩, ∀ a ∉ affectors ⟨i,h⟩, ∀ xs,
      (step xs a)[j] = xs[j])
    (hdeps : ∀ a xs ys,
      (∀ j ∈ deps ⟨i,h⟩, xs[j] = ys[j]) →
      ∀ j ∈ deps ⟨i,h⟩, (step xs a)[j] = (step ys a)[j]) :
    (entries.foldl step init)[i] =
      ((entries.filter fun a => a ∈ affectors ⟨i,h⟩).foldl step init)[i] := by
  exact foldl_get_eq_foldl_filter_affectors entries init step
    (fun xs j => xs[j]) deps affectors ⟨i,h⟩ hself hpreserve hdeps

theorem getElem_swap_fin_left {K m} (xs : Vector K m) (i j : Fin m) :
    (xs.swap i.1 j.1 i.2 j.2)[i] = xs[j] := by
  exact Vector.getElem_swap_left i.2 j.2

theorem getElem_swap_fin_right {K m} (xs : Vector K m) (i j : Fin m) :
    (xs.swap i.1 j.1 i.2 j.2)[j] = xs[i] := by
  exact Vector.getElem_swap_right i.2 j.2

theorem getElem_swap_fin_of_ne {K m} (xs : Vector K m) (i j t : Fin m)
    (hti : t ≠ i) (htj : t ≠ j) :
    (xs.swap i.1 j.1 i.2 j.2)[t] = xs[t] := by
  exact Vector.getElem_swap_of_ne (hi' := Fin.val_ne_of_ne hti) (hj' := Fin.val_ne_of_ne htj)

@[simp]
theorem getElem_setElem_fin_self {K m} (b : Vector K m) (i : Fin m) (x : K) :
    (setElem b i x (by trivial))[i] = x := by
  change (b.set i.1 x i.2)[i] = x
  simp

theorem getElem_setElem_fin_ne {K m} (b : Vector K m) (i j : Fin m) (x : K)
    (hij : i ≠ j) :
    (setElem b i x (by trivial))[j] = b[j] := by
  change (b.set i.1 x i.2)[j] = b[j]
  exact Vector.getElem_set_ne i.2 j.2 (Fin.val_ne_of_ne hij)

/-- Later writes to other injective destinations preserve an already-written destination. -/
theorem foldl_write_preserve {α K m} (entries : List α) (dst : Vector K m)
    (dstIdx : α → Fin m) (value : α → K)
    (hinj : Function.Injective dstIdx) (a : α)
    (h : dst[dstIdx a] = value a) :
    (List.foldl (fun acc x => setElem acc (dstIdx x) (value x) (by trivial)) dst entries)[dstIdx a]
      = value a := by
  classical
  induction entries generalizing dst with
  | nil => exact h
  | cons x xs ih =>
      apply ih
      by_cases hxa : x = a
      · simpa [hxa] using getElem_setElem_fin_self dst (dstIdx a) (value a)
      · have hne : dstIdx x ≠ dstIdx a := by
          intro heq
          exact hxa (hinj heq)
        rw [getElem_setElem_fin_ne]
        · exact h
        · exact hne

/-- If an element is visited by the fold, its injective destination contains its value afterward. -/
theorem foldl_write_get_of_mem {α K m} (entries : List α) (dst : Vector K m)
    (dstIdx : α → Fin m) (value : α → K)
    (hinj : Function.Injective dstIdx) {a : α} (ha : a ∈ entries) :
    (List.foldl (fun acc x => setElem acc (dstIdx x) (value x) (by trivial)) dst entries)[dstIdx a]
      = value a := by
  classical
  induction entries generalizing dst with
  | nil => cases ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hxa | hxs
      · apply foldl_write_preserve xs (setElem dst (dstIdx x) (value x) (by trivial)) dstIdx value hinj a
        subst hxa
        exact getElem_setElem_fin_self dst (dstIdx a) (value a)
      · exact ih (setElem dst (dstIdx x) (value x) (by trivial)) hxs

/-- If no visited write targets an index, that index is unchanged by the fold. -/
theorem foldl_write_get_of_not_mem_range {α K m} (entries : List α) (dst : Vector K m)
    (dstIdx : α → Fin m) (value : α → K)
    (i : Fin m)
    (hmiss : ∀ a, a ∈ entries → dstIdx a ≠ i) :
    (List.foldl (fun acc x => setElem acc (dstIdx x) (value x) (by trivial)) dst entries)[i]
      = dst[i] := by
  induction entries generalizing dst with
  | nil => rfl
  | cons x xs ih =>
      calc
        (List.foldl (fun acc x => setElem acc (dstIdx x) (value x) (by trivial)) dst (x :: xs))[i]
            = (List.foldl (fun acc x => setElem acc (dstIdx x) (value x) (by trivial))
                (setElem dst (dstIdx x) (value x) (by trivial)) xs)[i] := rfl
        _ = (setElem dst (dstIdx x) (value x) (by trivial))[i] := by
          apply ih
          intro a ha
          exact hmiss a (List.mem_cons_of_mem x ha)
        _ = dst[i] := by
          have hne : dstIdx x ≠ i := hmiss x (List.mem_cons_self)
          exact getElem_setElem_fin_ne dst (dstIdx x) i (value x) hne

end FoldMap

end Vector

end NumLean
