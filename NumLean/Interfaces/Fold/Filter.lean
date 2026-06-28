module

public import NumLean.Data.Vector.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace NumLean

namespace FoldMap

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

-- this might be a nice form to work with
-- open Classical in
-- theorem foldl_get_eq_foldl_filter_affectors' {α : Type u} {σ : Type v} {ι : Type w}
--     {β : Type x} (entries : List α) (init : σ) (step : σ → α → σ)
--     (read : σ → ι → β) (deps : ι → Set ι) (affectors : ι → List α) (i : ι)
--     (hself : i ∈ deps i)
--     (hpreserve : ∀ j ∈ deps i, ∀ a ∉ affectors i, ∀ xs,
--       read (step xs a) j = read xs j)
--     (hdeps : ∀ a xs ys,
--       (∀ j ∈ deps i, read xs j = read ys j) →
--       ∀ j ∈ deps i, read (step xs a) j = read (step ys a) j)
--     (horder : entries.filter (· ∈ affectors i) = affectors i) :
--     read (entries.foldl step init) i =
--       read ((affectors i).foldl step init) i := sorry

end FoldMap

end NumLean
