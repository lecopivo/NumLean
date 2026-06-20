import NumLean.Data.Vector.TensorOps.Defs
import NumLean.Data.Vector.TensorOps.ShapeEntries
import NumLean.Data.Vector.TensorOps.FoldMap

namespace NumLean

namespace Vector

namespace ForAll

open TensorIndex

theorem swapSlice_fst_in_xmap_range
    {K m n r} {shape : Shape r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : h(i) ∈ xmap.range) :
    (swapSlice xs xmap ys ymap h h').1[i] =
      ys[ymap (xmap.rangeInv h(i) hi)] := by
  classical
  let range : Std.Rco (HTuple Nat r) := (0 : HTuple Nat r)...shape
  let entries : List {idx : HTuple Nat r // idx ∈ range} := Fold.entries.{0,0,0} range
  let entryFin := fun a : {idx : HTuple Nat r // idx ∈ range} =>
    FinHTuple.equivZeroRange shape a
  let step := fun (acc : MProd (Vector K m) (Vector K n))
      (a : {idx : HTuple Nat r // idx ∈ range}) =>
    let idx := xmap[(entryFin a).val]'(entryFin a).isLt
    let jdx := ymap[(entryFin a).val]'(entryFin a).isLt
    MProd.mk (setElem acc.fst idx acc.snd[jdx] (by trivial))
      (setElem acc.snd jdx acc.fst[idx] (by trivial))
  let target := xmap.rangeInv h(i) hi
  let targetEntry : {idx : HTuple Nat r // idx ∈ range} :=
    ⟨target.val, FinHTuple.val_mem_zero_shape target⟩
  have hExt :
      (swapSlice xs xmap ys ymap h h').1[i] =
      (List.foldl step (MProd.mk xs ys)
        (entries.filter
          (fun a : {idx : HTuple Nat r // idx ∈ range} =>
            xmap (entryFin a) = h(i)))).fst[i] := by
    -- Pair-state fold extensionality with dependencies `{fst[i], snd[ymap target]}`.
    sorry
  rw [hExt]
  have hEntries :
      (entries.filter
        (fun a : {idx : HTuple Nat r // idx ∈ range} => xmap (entryFin a) = h(i))) =
        [targetEntry] := by
    sorry
  rw [hEntries]
  simp only [List.foldl_cons, List.foldl_nil]
  -- The singleton entry writes `ys[ymap target]` into `xs[xmap target]`.
  sorry

theorem swapSlice_fst_out_xmap_range
    {K m n r} {shape : Shape r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : h(i) ∉ xmap.range) (hi' : i < m) :
    (swapSlice xs xmap ys ymap h h').1[i] = xs[i] := by
  classical
  let range : Std.Rco (HTuple Nat r) := (0 : HTuple Nat r)...shape
  let entries : List {idx : HTuple Nat r // idx ∈ range} := Fold.entries.{0,0,0} range
  let entryFin := fun a : {idx : HTuple Nat r // idx ∈ range} =>
    FinHTuple.equivZeroRange shape a
  let step := fun (acc : MProd (Vector K m) (Vector K n))
      (a : {idx : HTuple Nat r // idx ∈ range}) =>
    let idx := xmap[(entryFin a).val]'(entryFin a).isLt
    let jdx := ymap[(entryFin a).val]'(entryFin a).isLt
    MProd.mk (setElem acc.fst idx acc.snd[jdx] (by trivial))
      (setElem acc.snd jdx acc.fst[idx] (by trivial))
  have hExt :
      (swapSlice xs xmap ys ymap h h').1[i] =
      (List.foldl step (MProd.mk xs ys)
        (entries.filter
          (fun a : {idx : HTuple Nat r // idx ∈ range} =>
            xmap (entryFin a) = h(i)))).fst[i] := by
    -- Pair-state fold extensionality with dependency `{fst[i]}`.
    sorry
  rw [hExt]
  have hEntries :
      (entries.filter
        (fun a : {idx : HTuple Nat r // idx ∈ range} => xmap (entryFin a) = h(i))) = [] := by
    sorry
  rw [hEntries]
  simp only [List.foldl_nil]

theorem swapSlice_snd_in_ymap_range
    {K m n r} {shape : Shape r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : h(i) ∈ ymap.range) :
    (swapSlice xs xmap ys ymap h h').2[i] =
      xs[xmap (ymap.rangeInv h(i) hi)] := by
  classical
  let range : Std.Rco (HTuple Nat r) := (0 : HTuple Nat r)...shape
  let entries : List {idx : HTuple Nat r // idx ∈ range} := Fold.entries.{0,0,0} range
  let entryFin := fun a : {idx : HTuple Nat r // idx ∈ range} =>
    FinHTuple.equivZeroRange shape a
  let step := fun (acc : MProd (Vector K m) (Vector K n))
      (a : {idx : HTuple Nat r // idx ∈ range}) =>
    let idx := xmap[(entryFin a).val]'(entryFin a).isLt
    let jdx := ymap[(entryFin a).val]'(entryFin a).isLt
    MProd.mk (setElem acc.fst idx acc.snd[jdx] (by trivial))
      (setElem acc.snd jdx acc.fst[idx] (by trivial))
  let target := ymap.rangeInv h(i) hi
  let targetEntry : {idx : HTuple Nat r // idx ∈ range} :=
    ⟨target.val, FinHTuple.val_mem_zero_shape target⟩
  have hExt :
      (swapSlice xs xmap ys ymap h h').2[i] =
      (List.foldl step (MProd.mk xs ys)
        (entries.filter
          (fun a : {idx : HTuple Nat r // idx ∈ range} =>
            ymap (entryFin a) = h(i)))).snd[i] := by
    -- Pair-state fold extensionality with dependencies `{snd[i], fst[xmap target]}`.
    sorry
  rw [hExt]
  have hEntries :
      (entries.filter
        (fun a : {idx : HTuple Nat r // idx ∈ range} => ymap (entryFin a) = h(i))) =
        [targetEntry] := by
    sorry
  rw [hEntries]
  simp only [List.foldl_cons, List.foldl_nil]
  -- The singleton entry writes old `xs[xmap target]` into `ys[ymap target]`.
  sorry

theorem swapSlice_snd_out_ymap_range
    {K m n r} {shape : Shape r}
    (xs : Vector K m) (xmap : FinHTupleMap shape h(m))
    (ys : Vector K n) (ymap : FinHTupleMap shape h(n))
    (h : xmap.Injective) (h' : ymap.Injective) (i : Nat) (hi : h(i) ∉ ymap.range) (hi' : i < n) :
    (swapSlice xs xmap ys ymap h h').2[i] = ys[i] := by
  classical
  let range : Std.Rco (HTuple Nat r) := (0 : HTuple Nat r)...shape
  let entries : List {idx : HTuple Nat r // idx ∈ range} := Fold.entries.{0,0,0} range
  let entryFin := fun a : {idx : HTuple Nat r // idx ∈ range} =>
    FinHTuple.equivZeroRange shape a
  let step := fun (acc : MProd (Vector K m) (Vector K n))
      (a : {idx : HTuple Nat r // idx ∈ range}) =>
    let idx := xmap[(entryFin a).val]'(entryFin a).isLt
    let jdx := ymap[(entryFin a).val]'(entryFin a).isLt
    MProd.mk (setElem acc.fst idx acc.snd[jdx] (by trivial))
      (setElem acc.snd jdx acc.fst[idx] (by trivial))
  have hExt :
      (swapSlice xs xmap ys ymap h h').2[i] =
      (List.foldl step (MProd.mk xs ys)
        (entries.filter
          (fun a : {idx : HTuple Nat r // idx ∈ range} =>
            ymap (entryFin a) = h(i)))).snd[i] := by
    -- Pair-state fold extensionality with dependency `{snd[i]}`.
    sorry
  rw [hExt]
  have hEntries :
      (entries.filter
        (fun a : {idx : HTuple Nat r // idx ∈ range} => ymap (entryFin a) = h(i))) = [] := by
    sorry
  rw [hEntries]
  simp only [List.foldl_nil]

end ForAll

end Vector

end NumLean
