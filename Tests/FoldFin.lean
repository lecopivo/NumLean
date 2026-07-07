module

public import NumLean.Interfaces.Fold
public import NumLean.Data.FinHTuple.Fold

@[expose] public section

namespace NumLean
namespace Tests
namespace FoldFin

example {p : HTuple.Profile} {idx shape : HTuple Nat p} :
    idx ∈ ((0 : HTuple Nat p)...shape) ↔ idx <ₑ shape := by
  simp

example {idx hi : Nat} :
    (HTuple.leaf idx) ∈ ((0 : HTuple Nat .leaf)...HTuple.leaf hi) ↔ idx < hi := by
  simp [Std.Rco.mem_iff]

example {α : Type u} [LE α] [LT α] {p q : HTuple.Profile}
    {idx₀ lo₀ hi₀ : HTuple α p} {idx₁ lo₁ hi₁ : HTuple α q} :
    (HTuple.prod idx₀ idx₁) ∈
      ((HTuple.prod lo₀ lo₁)...(HTuple.prod hi₀ hi₁) : Std.Rco (HTuple α (.prod p q))) ↔
        idx₀ ∈ (lo₀...hi₀ : Std.Rco (HTuple α p)) ∧
          idx₁ ∈ (lo₁...hi₁ : Std.Rco (HTuple α q)) := by
  simp

example (n : Nat) : (Fold.finViewZeroNat n).size = n := rfl

example (n : Nat) (i : Fin n) : (Fold.finViewZeroNat n).fromFin i = i := rfl

example (n : Nat) (i : Fin n) :
    (Fold.finViewZeroNat n).toFin ((Fold.finViewZeroNat n).fromFin i)
      ((Fold.finViewZeroNat n).mem_fromFin i) = i := by
  exact (Fold.finViewZeroNat n).toFin_fromFin i

example (n : Nat) (i : Nat) (h : i ∈ (0...n : Std.Rco Nat)) :
    (Fold.finViewZeroNat n).fromFin ((Fold.finViewZeroNat n).toFin i h) = i := by
  simp

example (n : Nat) (init : β)
    (f : (i : Nat) → i ∈ (0...n : Std.Rco Nat) → β → β) :
    Fold.fold (0...n : Std.Rco Nat) init f =
      Fin.foldl (Fold.finViewZeroNat n).size
        (fun acc i => f ((Fold.finViewZeroNat n).fromFin i)
          ((Fold.finViewZeroNat n).mem_fromFin i) acc)
        init := by
  rw [Fold.fold_zeroNat_eq_fin_foldl]

example (lo hi : Nat) : (Fold.finViewNat lo hi).size = hi - lo := rfl

example (lo hi : Nat) (i : Fin (hi - lo)) :
    (Fold.finViewNat lo hi).fromFin i = lo + i := rfl

example (lo hi : Nat) (init : β)
    (f : (i : Nat) → i ∈ (lo...hi : Std.Rco Nat) → β → β) :
    Fold.fold (lo...hi : Std.Rco Nat) init f =
      Fin.foldl (Fold.finViewNat lo hi).size
        (fun acc i => f ((Fold.finViewNat lo hi).fromFin i)
          ((Fold.finViewNat lo hi).mem_fromFin i) acc)
        init := by
  rw [Fold.fold_nat_eq_fin_foldl]

example (n : Nat) :
    ∑ a ∈ (NumLean.entries (0...n : Std.Rco Nat)).toFinset, a.1 =
      ∑ i : Fin n, (i : Nat) := by
  simpa [Fold.finViewZeroNat] using
    (Fold.finViewZeroNat.{0} n).sum_entries_eq_fin_sum (fun a => (a.1 : Nat))

example (n : Nat) :
    ∏ a ∈ (NumLean.entries (0...n : Std.Rco Nat)).toFinset, (a.1 + 1) =
      ∏ i : Fin n, ((i : Nat) + 1) := by
  simpa [Fold.finViewZeroNat] using
    (Fold.finViewZeroNat.{0} n).prod_entries_eq_fin_prod (fun a => (a.1 : Nat) + 1)

example (n : Nat) :
    Fold.fold (0...n : Std.Rco Nat) 0 (fun i _h acc => acc + i) =
      0 + ∑ i : Fin n, (i : Nat) := by
  simpa [Fold.finViewZeroNat] using
    (Fold.finViewZeroNat n).fold_eq_fin_sum 0 (fun i _ => i)

example (n : Nat) :
    Fold.fold (0...n : Std.Rco Nat) 1 (fun i _h acc => acc * (i + 1)) =
      1 * (∏ i : Fin n, ((i : Nat) + 1)) := by
  simpa [Fold.finViewZeroNat] using
    (Fold.finViewZeroNat n).fold_eq_fin_prod 1 (fun i _ => i + 1)

example (lo hi : Int) (init : β)
    (f : (i : Int) → i ∈ (lo...hi : Std.Rco Int) → β → β) :
    Fold.fold (lo...hi : Std.Rco Int) init f =
      Fin.foldl (Fold.finViewInt lo hi).size
        (fun acc i => f ((Fold.finViewInt lo hi).fromFin i)
          ((Fold.finViewInt lo hi).mem_fromFin i) acc)
        init := by
  rw [Fold.fold_int_eq_fin_foldl]

example (lo hi : Nat) (init : β)
    (f : (i : Nat) → i ∈ (lo...hi : Std.Rco Nat) → β → β) :
    Fold.fold (lo...hi : Std.Rco Nat) init f =
      Fin.foldl (Fold.FinRangeView.ofEntries (xs := (lo...hi : Std.Rco Nat))).size
        (fun acc i => f ((Fold.FinRangeView.ofEntries (xs := (lo...hi : Std.Rco Nat))).fromFin i)
          ((Fold.FinRangeView.ofEntries (xs := (lo...hi : Std.Rco Nat))).mem_fromFin i) acc)
        init := by
  simpa using Fold.fold_eq_fin_foldl_of_entries (xs := (lo...hi : Std.Rco Nat)) init f

example (lo hi : Nat × Nat) (init : β)
    (f : (x : Nat × Nat) → x ∈ (lo...hi : Std.Rco (Nat × Nat)) → β → β) :
    Fold.fold (lo...hi : Std.Rco (Nat × Nat)) init f =
      Fin.foldl (Fold.finViewRcoProd lo hi).size
        (fun acc i => f ((Fold.finViewRcoProd lo hi).fromFin i)
          ((Fold.finViewRcoProd lo hi).mem_fromFin i) acc)
        init := by
  simpa using Fold.fold_rco_prod_eq_fin_foldl lo hi init f

example {p : HTuple.Profile} (shape : HTuple Nat p) (init : β)
    (f : (idx : HTuple Nat p) → idx ∈ ((0 : HTuple Nat p)...shape) → β → β)
    [DecidableEq {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...shape)}] :
    Fold.fold ((0 : HTuple Nat p)...shape) init f =
      Fin.foldl (Fold.finViewZeroHTuple shape).size
        (fun acc i => f ((Fold.finViewZeroHTuple shape).fromFin i)
          ((Fold.finViewZeroHTuple shape).mem_fromFin i) acc)
        init := by
  rw [Fold.fold_zeroHTuple_eq_fin_foldl]

example {p q : HTuple.Profile}
    (lo₀ hi₀ : HTuple Nat p) (lo₁ hi₁ : HTuple Nat q) (init : β)
    (f : (idx : HTuple Nat (.prod p q)) →
      idx ∈ ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple Nat (.prod p q))) →
      β → β) :
    Fold.fold ((lo₀.prod lo₁)...(hi₀.prod hi₁) : Std.Rco (HTuple Nat (.prod p q))) init f =
      Fold.fold ((lo₀, lo₁)...(hi₀, hi₁) : Std.Rco (HTuple Nat p × HTuple Nat q)) init
        fun idx hidx acc =>
          f (idx.1.prod idx.2) ((htupleProdRangeIso lo₀ hi₀ lo₁ hi₁).toEquiv ⟨idx, hidx⟩).2 acc := by
  rw [fold_htuple_prod_eq_pair]

end FoldFin
end Tests
end NumLean
