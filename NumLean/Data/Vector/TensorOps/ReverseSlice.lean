import NumLean.Data.Vector.TensorOps.Defs
import NumLean.Data.Vector.TensorOps.FoldMap
import NumLean.Data.TensorIndex.Basic

namespace NumLean

namespace Vector

namespace ForAll

open TensorIndex

theorem reverseIndex_reverseIndex {k r} {shape : Shape r}
    (i : FinHTuple (.prod (.leaf k) shape)) :
    reverseIndex (reverseIndex i) = i := by
  apply FinHTuple.ext
  cases i with
  | mk val hval =>
    cases val with
    | prod left right =>
      cases left with
      | leaf a =>
        simp [reverseIndex]
        have ha : a < k := by
          exact hval.1
        omega

theorem reverseSlice_in_map_range
    {K n k r} {shape : Shape r}
    (xs : Vector K n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (h : map.Injective) (i : Nat) (hi : h(i) ∈ map.range) :
    (reverseSlice xs map h)[i] =
      xs[map (reverseIndex (map.rangeInv h(i) hi))] := by
  classical
  unfold reverseSlice
  simp only [Id.run, bind_pure]
  simp only [Fold.fold_rco_outer_inner_eq_prod, pure]
  simp only [LawfulFold.fold_eq_foldl]
  let entries := Fold.entries ((0, (0 : HTuple Nat r))...(k / 2, shape))
  let step := fun (acc : Vector K n)
      (a : {idx : Nat × HTuple Nat r // idx ∈ ((0, (0 : HTuple Nat r))...(k / 2, shape))}) =>
    acc.swap (map ((HTuple.leaf a.1.1).prod a.1.2)).toScalar
      (map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2)).toScalar
      (by sorry) (by sorry)
  change (List.foldl step xs entries)[i] = xs[map (reverseIndex (map.rangeInv h(i) hi))]
  have hExt :
      (List.foldl step xs entries)[i] =
      (List.foldl step xs (entries.filter
        (fun a => map ((HTuple.leaf a.1.1).prod a.1.2) = h(i) ∨
          map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2) = h(i))))[i] := by
    -- Vector fold extensionality at `i`, with dependencies restricted to the swapped pair.
    sorry
  rw [hExt]
  let target := map.rangeInv h(i) hi
  let targetRev := reverseIndex target
  by_cases htargetLower : ∃ active : {idx : Nat × HTuple Nat r //
      idx ∈ ((0, (0 : HTuple Nat r))...(k / 2, shape))},
      map ((HTuple.leaf active.1.1).prod active.1.2) = h(i)
  · let active : {idx : Nat × HTuple Nat r // idx ∈ ((0, (0 : HTuple Nat r))...(k / 2, shape))} :=
      Classical.choose htargetLower
    have hEntries :
        (entries.filter
          (fun a : Subtype _ =>
            map ((HTuple.leaf a.1.1).prod a.1.2) = h(i) ∨
              map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2) = h(i))) =
          [active] := by
      sorry
    rw [hEntries]
    simp only [List.foldl_cons, List.foldl_nil]
    -- The active entry swaps `target` with `targetRev`, and the read is the left endpoint.
    sorry
  · let active : {idx : Nat × HTuple Nat r // idx ∈ ((0, (0 : HTuple Nat r))...(k / 2, shape))} :=
      Classical.choice (show Nonempty {idx : Nat × HTuple Nat r //
        idx ∈ ((0, (0 : HTuple Nat r))...(k / 2, shape))} from by sorry)
    have hEntries :
        (entries.filter
          (fun a : Subtype _ =>
            map ((HTuple.leaf a.1.1).prod a.1.2) = h(i) ∨
              map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2) = h(i))) =
          [active] := by
      sorry
    rw [hEntries]
    simp only [List.foldl_cons, List.foldl_nil]
    -- The active entry swaps `targetRev` with `target`, and the read is the right endpoint.
    sorry

theorem reverseSlice_out_map_range
    {K n k r} {shape : Shape r}
    (xs : Vector K n) (map : FinHTupleMap (.prod (.leaf k) shape) h(n))
    (h : map.Injective) (i : Nat) (hi : h(i) ∉ map.range) (hi' : i < n) :
    (reverseSlice xs map h)[i] = xs[i] := by
  classical
  unfold reverseSlice
  simp only [Id.run, bind_pure]
  simp only [Fold.fold_rco_outer_inner_eq_prod, pure]
  simp only [LawfulFold.fold_eq_foldl]
  let entries := Fold.entries ((0, (0 : HTuple Nat r))...(k / 2, shape))
  let step := fun (acc : Vector K n)
      (a : {idx : Nat × HTuple Nat r // idx ∈ ((0, (0 : HTuple Nat r))...(k / 2, shape))}) =>
    acc.swap (map ((HTuple.leaf a.1.1).prod a.1.2)).toScalar
      (map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2)).toScalar
      (by sorry) (by sorry)
  change (List.foldl step xs entries)[i] = xs[i]
  have hExt :
      (List.foldl step xs entries)[i] =
      (List.foldl step xs (entries.filter
        (fun a => map ((HTuple.leaf a.1.1).prod a.1.2) = h(i) ∨
          map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2) = h(i))))[i] := by
    -- Vector fold extensionality at an out-of-range coordinate.
    sorry
  rw [hExt]
  have hEntries :
      (entries.filter
        (fun a : Subtype _ =>
          map ((HTuple.leaf a.1.1).prod a.1.2) = h(i) ∨
            map ((HTuple.leaf (k - a.1.1 - 1)).prod a.1.2) = h(i))) = [] := by
    sorry
  rw [hEntries]
  simp only [List.foldl_nil]

end ForAll

end Vector

end NumLean
