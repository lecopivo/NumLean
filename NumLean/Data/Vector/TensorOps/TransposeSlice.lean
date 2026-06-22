import NumLean.Data.Vector.TensorOps.Defs

namespace NumLean

namespace Vector

namespace ForAll

theorem transposeSlice_in_map_range
    {K n r} {shape : HTuple Nat r}
    (xs : Vector K n) (map : FinHTupleMap (.prod shape shape) h(n))
    (h : map.Injective) (i : Nat) (hi : h(i) ∈ map.range) :
    (transposeSlice xs map h)[i] =
      xs[map (transposeIndex (map.rangeInv h(i) hi))] := by
  classical
  unfold transposeSlice
  simp only [Id.run, bind_pure]
  simp only [LawfulFold.fold_eq_foldl]
  let outerEntries := Fold.entries ((0 : HTuple Nat r)...shape)
  let innerEntries := Fold.entries ((0 : HTuple Nat r)...shape)
  let outerStep := fun (acc : Vector K n)
      (a : {idx : HTuple Nat r // idx ∈ ((0 : HTuple Nat r)...shape)}) =>
    List.foldl
      (fun acc (b : {idx : HTuple Nat r // idx ∈ ((0 : HTuple Nat r)...shape)}) =>
        let ij := map (a.1.prod b.1)
        let ji := map (b.1.prod a.1)
        if ij.toScalar < ji.toScalar then
          acc.swap ij.toScalar ji.toScalar (by sorry) (by sorry)
        else acc)
      acc innerEntries
  change (List.foldl outerStep xs outerEntries)[i] =
    xs[map (transposeIndex (map.rangeInv h(i) hi))]
  let entries : List {idx : HTuple Nat (.prod r r) //
      idx ∈ (((0 : HTuple Nat r).prod (0 : HTuple Nat r))...(shape.prod shape))} :=
    []
  let step := fun (acc : Vector K n)
      (a : {idx : HTuple Nat (.prod r r) //
        idx ∈ (((0 : HTuple Nat r).prod (0 : HTuple Nat r))...(shape.prod shape))}) =>
    let ij := map a.1
    let ji := map (transposeIndex' (shape := shape) a.1)
    if ij.toScalar < ji.toScalar then
      acc.swap ij.toScalar ji.toScalar (by sorry) (by sorry)
    else acc
  have hExt :
      (List.foldl outerStep xs outerEntries)[i] =
      (List.foldl step xs (entries.filter
        (fun a => map a.1 = h(i) ∨ map (transposeIndex' (shape := shape) a.1) = h(i))))[i] := by
    -- Transport the nested square fold to the product entries and keep only entries touching `i`.
    sorry
  rw [hExt]
  let target := map.rangeInv h(i) hi
  let targetT := transposeIndex target
  let targetEntry : {idx : HTuple Nat (.prod r r) //
      idx ∈ (((0 : HTuple Nat r).prod (0 : HTuple Nat r))...(shape.prod shape))} :=
    ⟨target.val, by sorry⟩
  let targetTEntry : {idx : HTuple Nat (.prod r r) //
      idx ∈ (((0 : HTuple Nat r).prod (0 : HTuple Nat r))...(shape.prod shape))} :=
    ⟨targetT.val, by sorry⟩
  have hEntries :
      (entries.filter
        (fun a : Subtype _ => map a.1 = h(i) ∨ map (transposeIndex' (shape := shape) a.1) = h(i))) =
          [targetEntry, targetTEntry] ∨
      (entries.filter
        (fun a : Subtype _ => map a.1 = h(i) ∨ map (transposeIndex' (shape := shape) a.1) = h(i))) =
          [targetTEntry, targetEntry] := by
    sorry
  rcases hEntries with hEntries | hEntries
  · rw [hEntries]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hlt : (map target).toScalar < (map targetT).toScalar
    · -- First entry performs the swap; the second entry's guard is false.
      sorry
    · -- If the first guard is false, the transposed entry performs the swap or both entries are fixed.
      sorry
  · rw [hEntries]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hlt : (map targetT).toScalar < (map target).toScalar
    · -- Transposed entry performs the swap first.
      sorry
    · -- Original entry performs the swap or the coordinate is diagonal.
      sorry

theorem transposeSlice_out_map_range
    {K n r} {shape : HTuple Nat r}
    (xs : Vector K n) (map : FinHTupleMap (.prod shape shape) h(n))
    (h : map.Injective) (i : Nat) (hi : h(i) ∉ map.range) (hi' : i < n) :
    (transposeSlice xs map h)[i] = xs[i] := by
  classical
  unfold transposeSlice
  simp only [Id.run, bind_pure]
  simp only [LawfulFold.fold_eq_foldl]
  let outerEntries := Fold.entries ((0 : HTuple Nat r)...shape)
  let innerEntries := Fold.entries ((0 : HTuple Nat r)...shape)
  let outerStep := fun (acc : Vector K n)
      (a : {idx : HTuple Nat r // idx ∈ ((0 : HTuple Nat r)...shape)}) =>
    List.foldl
      (fun acc (b : {idx : HTuple Nat r // idx ∈ ((0 : HTuple Nat r)...shape)}) =>
        let ij := map (a.1.prod b.1)
        let ji := map (b.1.prod a.1)
        if ij.toScalar < ji.toScalar then
          acc.swap ij.toScalar ji.toScalar (by sorry) (by sorry)
        else acc)
      acc innerEntries
  change (List.foldl outerStep xs outerEntries)[i] = xs[i]
  let entries : List {idx : HTuple Nat (.prod r r) //
      idx ∈ (((0 : HTuple Nat r).prod (0 : HTuple Nat r))...(shape.prod shape))} :=
    []
  let step := fun (acc : Vector K n)
      (a : {idx : HTuple Nat (.prod r r) //
        idx ∈ (((0 : HTuple Nat r).prod (0 : HTuple Nat r))...(shape.prod shape))}) =>
    let ij := map a.1
    let ji := map (transposeIndex' (shape := shape) a.1)
    if ij.toScalar < ji.toScalar then
      acc.swap ij.toScalar ji.toScalar (by sorry) (by sorry)
    else acc
  have hExt :
      (List.foldl outerStep xs outerEntries)[i] =
      (List.foldl step xs (entries.filter
        (fun a => map a.1 = h(i) ∨ map (transposeIndex' (shape := shape) a.1) = h(i))))[i] := by
    -- Transport the nested square fold to the product entries and keep only entries touching `i`.
    sorry
  rw [hExt]
  have hEntries :
      (entries.filter
        (fun a : Subtype _ => map a.1 = h(i) ∨ map (transposeIndex' (shape := shape) a.1) = h(i))) = [] := by
    sorry
  rw [hEntries]
  simp only [List.foldl_nil]

end ForAll

end Vector

end NumLean
