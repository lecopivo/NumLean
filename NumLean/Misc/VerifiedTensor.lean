import NumLean.Data.FinHTuple
import NumLean.Data.Prod.Fold

public section

namespace NumLean

namespace Misc

namespace VerifiedTensor

namespace RangeTransport

theorem rangeIso_fold_eq {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : Fold.RangeIso xs ys) (init : γ)
    (f : (b : β) → b ∈ ys → γ → γ) :
    Fold.fold ys init f =
      Fold.fold xs init fun a ha acc =>
        f (e.toEquiv ⟨a, ha⟩).1 (e.toEquiv ⟨a, ha⟩).2 acc := by
  exact Fold.RangeIso.fold_eq e init f

theorem rangeEquiv_fold_eq_of_commutes {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : Fold.RangeEquiv xs ys) (init : γ)
    (f : (b : β) → b ∈ ys → γ → γ) (hcomm : Fold.PairwiseCommutes ys f) :
    Fold.fold ys init f =
      Fold.fold xs init fun a ha acc =>
        f (e.toEquiv ⟨a, ha⟩).1 (e.toEquiv ⟨a, ha⟩).2 acc := by
  exact Fold.RangeEquiv.fold_eq_of_pairwise_commutes e init f hcomm

theorem rangeMonoEmbedding_fold_eq_guarded {ρ : Type u} {σ : Type v} {α : Type w} {β : Type x}
    {γ : Type y} {dρ : Membership α ρ} {dσ : Membership β σ}
    [FoldEntries ρ α dρ] [FoldEntries σ β dσ] [Fold ρ] [Fold σ]
    [LawfulFold ρ α dρ] [LawfulFold σ β dσ]
    {xs : ρ} {ys : σ} (e : Fold.RangeMonoEmbedding xs ys) (init : γ)
    (f : (a : α) → a ∈ xs → γ → γ) :
    Fold.fold xs init f
    =
    Fold.fold ys init fun b hb acc =>
      if h : e.guard b hb then
        f (e.invFun b hb h).1 (e.invFun b hb h).2 acc
      else
        acc := by
  exact Fold.RangeMonoEmbedding.fold_eq_guarded e init f

end RangeTransport

namespace ProductFold

theorem product_fold_merge {α : Type u} {β : Type v} {γ : Type w}
    [Membership α (Std.Rco α)] [Membership β (Std.Rco β)]
    [FoldEntries (Std.Rco α) α inferInstance] [FoldEntries (Std.Rco β) β inferInstance]
    [Fold (Std.Rco α)] [Fold (Std.Rco β)]
    [LawfulFold (Std.Rco α) α inferInstance] [LawfulFold (Std.Rco β) β inferInstance]
    (lo hi : α × β) (init : γ)
    (f : (x : α × β) → x ∈ (lo...hi : Std.Rco (α × β)) → γ → γ) :
    Fold.fold (lo...hi : Std.Rco (α × β)) init f
    =
    Fold.fold (lo.1...hi.1 : Std.Rco α) init fun a ha acc =>
      Fold.fold (lo.2...hi.2 : Std.Rco β) acc fun b hb acc =>
        f (a, b) (by grind [Fold.mem_rco_prod_iff]) acc := by
  exact Fold.fold_rco_prod_eq_outer_inner lo hi init f

end ProductFold

namespace FlattenUnflatten

def htuple_zero_range_flatten_equiv {p : HTuple.Profile} (shape : HTuple Nat p) :
    Fold.RangeEquiv
      ((0 : HTuple Nat p)...shape)
      (0...shape.numel : Std.Rco Nat) :=
  FinHTuple.zeroRangeRangeEquivFin shape

end FlattenUnflatten

namespace SplitTile

/-- Placeholder for a future guarded embedding of one folded range into a larger folded range.

This should eventually carry a map into the target range, a positive decidable guard on the target
range, and a guarded inverse for target entries satisfying the guard. Avoid existential image
witnesses in the API; they are inconvenient for fold proofs and generated guards. -/
opaque RangeEmbeddingTarget : Type

/-- Placeholder for the eventual scalar full-blocks-plus-tail tiling range.

The intended decomposition is
`0...n ≃ ((0...k) × (0...(n / k))) ⊕ (0...(n % k))`.
The concrete range type is deferred until the Sum/tail range design is settled. -/
opaque TileTailRange : Nat → Nat → Type

-- theorem scalar_tile_fullBlocks_tail_target (n k : Nat) : Nonempty (TileTailRange n k) := by
--   sorry

/-- Placeholder for padded rectangular tiling.

Intended shape:
`0...n ≲ (0...k) × (0...((n + k - 1) / k))`, where padded coordinates take the neutral branch.

The concrete theorem should relate

```lean
Fold.fold (0...n) init f
```

to a fold over the rectangular product range with an `if padded ij then acc else f (tileIndex ij)`
step. The exact `padded` and `tileIndex` definitions are deferred until the coordinate convention
is fixed.

For `(block, inner)` coordinates, the generic guard is `block * k + inner < n`. A more
code-friendly padded test is `n % k ≠ 0 ∧ block = ((n + k - 1) / k) - 1 ∧ n % k ≤ inner`, which
avoids skipping a full last block when `n % k = 0`. -/
theorem scalar_tile_padded_rectangular_target (_n _k : Nat) : True := by
  trivial

end SplitTile

namespace GuardedExtension

/-- Placeholder target for extending a fold over `lo...hi` to a larger rectangular range with
a guard/neutral step outside the original range. The exact API is deferred until guard/filter
semantics are settled. -/
theorem fold_extend_guarded_target : True := by
  trivial

end GuardedExtension

namespace ScatterToGather

/-- Placeholder target for the paper's scatter-to-gather rewrite. The range API should support
the loop-domain permutation/reindexing part; expression-level arithmetic and algebraic facts will
be added separately. -/
theorem scatter_to_gather_1d_target : True := by
  trivial

end ScatterToGather

namespace Im2col

/-- Placeholder target for the paper's im2col hoisting rewrite. The range API should support the
domain splitting/reindexing part; hoisting requires separate independence lemmas. -/
theorem im2col_1d_target : True := by
  trivial

end Im2col

end VerifiedTensor

end Misc

end NumLean
