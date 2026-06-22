import NumLean.Data.BTuple.Range
import NumLean.Interfaces.Fold

/-!
# Folding over unbundled `BTuple` ranges

The fold range is a half-open range of shapes:

```lean
r : Std.Rco (BTuple.Shape p)  -- written `lo...hi`
```

and the loop index is an unbundled value:

```lean
idx : BTuple Nat p
idx ∈ r  -- means `BTuple.Range.InBounds r.lower r.upper idx`
```

This gives the intended spelling for loops over tensor/direct-sum shapes while keeping the index
unbundled, just like raw `HTuple Nat p` is the unbundled counterpart of `FinHTuple shape`.
-/

namespace NumLean

namespace BTuple

/-- Reference entries for folding over a half-open shape range. -/
def foldShapeEntries {p : Profile} (r : Std.Rco (Shape p)) :
    List {idx : BTuple Nat p // idx ∈ r} :=
  (Range.toList r.lower r.upper).attach.map fun idx =>
    ⟨idx.1, Range.mem_toList_iff_inBounds.mp idx.2⟩

/-- Fold over all unbundled indices in a half-open shape range.

This is the executable fold, not a replay of `foldShapeEntries`. Leaves delegate to the scalar
`Std.Rco Nat` fold. Product nodes are nested row-major loops, with the right child innermost. Sum
nodes traverse the left summand block first, then the right summand block. -/
@[always_inline, inline, specialize] def foldShape {β : Type v}
    [Fold (Std.Rco Nat) Nat inferInstance] : {p : Profile} → (r : Std.Rco (Shape p)) →
    (init : β) → ((idx : BTuple Nat p) → idx ∈ r → β → β) → β
  | .leaf, ⟨.leaf lo, .leaf hi⟩, init, f =>
      Fold.fold (lo...hi) init fun idx hidx acc =>
        f (.leaf idx)
          (by
            change idx ∈ (lo...hi)
            exact hidx) acc
  | .prod p q, ⟨.prod lo₀ lo₁, .prod hi₀ hi₁⟩, init, f =>
      let r₀ : Std.Rco (Shape p) := lo₀...hi₀
      let r₁ : Std.Rco (Shape q) := lo₁...hi₁
      foldShape r₀ init fun idx₀ hidx₀ acc =>
        foldShape r₁ acc fun idx₁ hidx₁ acc =>
          f (.prod idx₀ idx₁)
            (by
              change Range.InBounds lo₀ hi₀ idx₀ ∧ Range.InBounds lo₁ hi₁ idx₁
              exact ⟨hidx₀, hidx₁⟩) acc
  | .sum p q, ⟨.sum lo₀ lo₁, .sum hi₀ hi₁⟩, init, f =>
      let r₀ : Std.Rco (Shape p) := lo₀...hi₀
      let r₁ : Std.Rco (Shape q) := lo₁...hi₁
      let acc := foldShape r₀ init fun idx₀ hidx₀ acc =>
        f (.sumLeft idx₀ q)
          (by
            change Range.InBounds lo₀ hi₀ idx₀
            exact hidx₀) acc
      foldShape r₁ acc fun idx₁ hidx₁ acc =>
        f (.sumRight p idx₁)
          (by
            change Range.InBounds lo₁ hi₁ idx₁
            exact hidx₁) acc

instance {p : Profile} [Fold (Std.Rco Nat) Nat inferInstance] :
    Fold (Std.Rco (Shape p)) (BTuple Nat p) Range.instMembershipRcoShape where
  fold r init f := foldShape r init f
  entries := foldShapeEntries

theorem entries_shape_rco {p : Profile} (lo hi : Shape p) :
    foldShapeEntries (lo...hi : Std.Rco (Shape p)) =
      (Range.toList lo hi).attach.map fun idx =>
        ⟨idx.1, Range.mem_toList_iff_inBounds.mp idx.2⟩ := rfl

end BTuple

end NumLean
