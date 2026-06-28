module

public import NumLean.Data.HTuple
public import NumLean.Interfaces.SetElem
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

namespace NumLean

open HTuple

@[simp]
theorem HTuple.numel_leaf (n : Nat) : (h(n) : HTuple Nat .leaf).numel = n := rfl

@[simp]
theorem HTuple.numel_prod {p q : Profile} (ns : HTuple Nat p) (ms : HTuple Nat q) :
    (HTuple.prod ns ms).numel = ns.numel * ms.numel := rfl

theorem HTuple.numel_eq_range_card_zero {p : Profile} (ns : HTuple Nat p) :
    ns.numel = HTuple.Range.card 0 ns := by
  induction ns with
  | leaf n => rfl
  | prod ns ms hns hms => simp [HTuple.numel, hns, hms]

/-- A bounded hierarchical tuple of natural numbers, analogous to `Fin n`. -/
structure FinHTuple {p : Profile} (ns : HTuple Nat p) where
  val : HTuple Nat p
  isLt : val <ₑ ns

attribute [inline] FinHTuple.val
attribute [grind ←, grind_htuple_order ←] FinHTuple.isLt

namespace FinHTuple

/-- Bounded hierarchical tuples are equal when their underlying tuples are equal. -/
@[ext]
theorem ext {p : Profile} {ns : HTuple Nat p} {i j : FinHTuple ns}
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp at h
  subst h
  rfl

theorem val_injective {p : Profile} {ns : HTuple Nat p} :
    Function.Injective (FinHTuple.val : FinHTuple ns → HTuple Nat p) :=
  fun _ _ h => ext h

instance {p : Profile} {ns : HTuple Nat p} : CoeOut (FinHTuple ns) (HTuple Nat p) where
  coe i := i.val

instance {p : Profile} {ns : HTuple Nat p} :
    CanLift (HTuple Nat p) (FinHTuple ns) FinHTuple.val (fun i => i <ₑ ns) where
  prf i hi := ⟨⟨i, hi⟩, rfl⟩

instance {cont : Type u} {elem : Type v} {p : Profile} {ns : HTuple Nat p}
    {dom : cont → HTuple Nat p → Prop} [GetElem cont (HTuple Nat p) elem dom] :
    GetElem cont (FinHTuple ns) elem (fun xs i => dom xs i.val) where
  getElem xs i h := xs[i.val]'h

instance {cont : Type u} {elem : Type v} {p : Profile} {ns : HTuple Nat p}
    {dom : cont → HTuple Nat p → Prop} [SetElem cont (HTuple Nat p) elem dom] :
    SetElem cont (FinHTuple ns) elem (fun xs i => dom xs i.val) where
  setElem xs i x h := setElem xs i.val x h
  setElem_valid := by
    intro xs i j v hi
    exact SetElem.setElem_valid

@[simp]
theorem getElem_val {p : Profile} {ns : HTuple Nat p}
    {dom : cont → HTuple Nat p → Prop}
    [GetElem cont (HTuple Nat p) elem dom]
    (xs : cont) (i : FinHTuple ns) (h) :
    xs[i]'h = xs[i.val] := by
  rfl

@[simp]
theorem setElem_val {p : Profile} {ns : HTuple Nat p}
    {dom : cont → HTuple Nat p → Prop}
    [SetElem cont (HTuple Nat p) elem dom]
    (xs : cont) (i : FinHTuple ns) (x : elem) (h) :
    setElem xs i x h = setElem xs i.val x h := by
  rfl

/-- Bounded tuples over a leaf are ordinary finite indices. -/
@[inline, simps]
def leafEquiv (n : Nat) : FinHTuple h(n) ≃ Fin n where
  toFun i :=
    match i with
    | ⟨.leaf i, h⟩ => ⟨i, by simpa using h⟩
  invFun i := ⟨.leaf i.1, by simp [i.2]⟩
  left_inv := by
    intro i
    cases i with
    | mk val h =>
      cases val with
      | leaf i =>
        apply ext
        rfl
  right_inv := by intro i; rfl

/-- Bounded tuples over a product are pairs of bounded tuples. -/
@[inline, simps]
def prodEquiv {p q : Profile} (ns : HTuple Nat p) (ms : HTuple Nat q) :
    FinHTuple (HTuple.prod ns ms) ≃ FinHTuple ns × FinHTuple ms where
  toFun i :=
    match i with
    | ⟨.prod i j, h⟩ => (⟨i, h.1⟩, ⟨j, h.2⟩)
  invFun i :=
    ⟨.prod i.1.val i.2.val, ⟨i.1.2, i.2.2⟩⟩
  left_inv := by
    intro i
    cases i with
    | mk val h =>
      cases val with
      | prod i j => rfl
  right_inv := by
    intro i
    cases i with
    | mk i j => rfl

/-- Canonical row-major equivalence between bounded hierarchical tuples and flat finite indices. -/
@[inline] def equivFin : {p : Profile} → (ns : HTuple Nat p) → FinHTuple ns ≃ Fin ns.numel
  | .leaf, .leaf n => leafEquiv n
  | .prod _ _, .prod ns ms =>
      let f := prodEquiv ns ms
      let g := Equiv.prodCongr (equivFin ns) (equivFin ms)
      let h := finProdFinEquiv
      f.trans (g.trans h)

@[implicit_reducible]
def fintype {p : Profile} (ns : HTuple Nat p) : Fintype (FinHTuple ns) :=
  Fintype.ofEquiv (Fin ns.numel) (equivFin ns).symm

instance {p : Profile} {ns : HTuple Nat p} : Fintype (FinHTuple ns) :=
  fintype ns

theorem card_eq_htuple_card {p : Profile} (ns : HTuple Nat p) :
    Fintype.card (FinHTuple ns) = ns.numel := by
  simpa using Fintype.card_congr (equivFin ns)

theorem equivFin_val_eq_linearIndex_zero {p : Profile} (ns : HTuple Nat p)
    (i : FinHTuple ns) :
    (equivFin ns i).val = HTuple.Range.linearIndex 0 ns i.val := by
  induction ns with
  | leaf n =>
      cases i with
      | mk val h =>
        cases val with | leaf i =>
        rfl
  | prod ns ms hns hms =>
      cases i with
      | mk val h =>
        cases val with | prod i j =>
        let fi : FinHTuple ns := ⟨i, h.1⟩
        let fj : FinHTuple ms := ⟨j, h.2⟩
        set_option backward.isDefEq.respectTransparency false in
        simp [equivFin, prodEquiv, finProdFinEquiv, HTuple.Range.linearIndex]
        rw [hns (⟨i, h.1⟩ : FinHTuple ns),
          hms (⟨j, h.2⟩ : FinHTuple ms),
          HTuple.numel_eq_range_card_zero ms]
        simp [HTuple.Range.linearIndex, HTuple.Range.card, HTuple.rowMajorIndex]

theorem val_mem_zero_shape {p : Profile} {ns : HTuple Nat p} (i : FinHTuple ns) :
    i.val ∈ ((0 : HTuple Nat p)...ns) := by
  apply HTuple.Range.mem_iff_le_lt.2
  constructor
  · rw [HTuple.elementwiseLE_iff_get]
    intro axis
    simp [Nat.zero_le (i.val.get axis)]
  · exact i.isLt

/-- The zero-origin tuple range `0...ns` is exactly the subtype representation of
`FinHTuple ns`. -/
def equivZeroRange {p : Profile} (ns : HTuple Nat p) :
    {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...ns)} ≃ FinHTuple ns where
  toFun idx := ⟨idx.1, (HTuple.Range.mem_iff_le_lt.1 idx.2).2⟩
  invFun idx := ⟨idx.val, val_mem_zero_shape idx⟩
  left_inv := by
    intro idx
    apply Subtype.ext
    rfl
  right_inv := by
    intro idx
    apply ext
    rfl

/-- Row-major equivalence between the zero-origin tuple range `0...ns` and flat finite indices. -/
def zeroRangeEquivFlatFin {p : Profile} (ns : HTuple Nat p) :
    {idx : HTuple Nat p // idx ∈ ((0 : HTuple Nat p)...ns)} ≃ Fin ns.numel :=
  (equivZeroRange ns).trans (equivFin ns)

@[coe]
def toFin {n} (i : FinHTuple h(n)) : Fin n :=
  leafEquiv n i

@[coe]
def toNat {n} (i : FinHTuple h(n)) : Nat :=
  leafEquiv n i

@[simp, norm_cast]
theorem coe_coe (i : FinHTuple h(n)) : i.toFin.val = i.toNat := by rfl

@[simp, norm_cast]
theorem coe_toFin_nat (i : FinHTuple h(n)) : ((i.toFin : Nat) = (i : Nat)) := by
  cases i with
  | mk val h =>
      cases val
      rfl

@[simp]
theorem toNat_eq_val_toScalar (i : FinHTuple h(n)) : i.toNat = i.val.toScalar := by
  cases i with
  | mk val h =>
      cases val
      rfl

@[simp]
theorem toFin_val_eq_val_toScalar (i : FinHTuple h(n)) :
    (i.toFin : Nat) = i.val.toScalar := by
  cases i with
  | mk val h =>
      cases val
      rfl

/-- Build a scalar bounded tuple from a `Fin`. -/
def ofFin {n} (i : Fin n) : FinHTuple h(n) :=
  (leafEquiv n).symm i

/-- Build a scalar bounded tuple from a natural number and a bound proof. -/
def ofNatLt {n} (i : Nat) (hi : i < n) : FinHTuple h(n) :=
  ofFin ⟨i, hi⟩

@[simp]
theorem toFin_ofFin {n} (i : Fin n) : (ofFin i).toFin = i := by
  rfl

@[simp]
theorem ofFin_toFin {n} (i : FinHTuple h(n)) : ofFin i.toFin = i := by
  simpa [ofFin, toFin] using (leafEquiv n).left_inv i

@[simp]
theorem ofNatLt_toNat {n} (i : Nat) (hi : i < n) : (ofNatLt i hi : FinHTuple h(n)).toNat = i := by
  rfl

@[simp]
theorem ofNatLt_val_toScalar {n} (i : Nat) (hi : i < n) :
    (ofNatLt i hi : FinHTuple h(n)).val.toScalar = i := by
  rfl

instance {n : Nat} : CanLift Nat (FinHTuple h(n)) (fun i => (i : Nat)) (fun i => i < n) where
  prf i hi := ⟨ofNatLt i hi, rfl⟩

instance : Coe (FinHTuple (.leaf n)) (Fin n) := ⟨fun i => i.toFin⟩
instance : CoeOut (FinHTuple (.leaf n)) Nat := ⟨fun i => i.toNat⟩

@[simp]
theorem coe_eq_toNat (i : FinHTuple h(n)) : (i : Nat) = i.toNat := by
  cases i with
  | mk val h =>
      cases val
      rfl

@[simp]
theorem coe_eq_val_toScalar (i : FinHTuple h(n)) : (i : Nat) = i.val.toScalar := by
  cases i with
  | mk val h =>
      cases val
      rfl

@[simp]
theorem coe_ofNatLt {n} (i : Nat) (hi : i < n) : ((ofNatLt i hi : FinHTuple h(n)) : Nat) = i := by
  change (ofNatLt i hi).val.toScalar = i
  rfl

@[simp]
theorem coe_val_ofNatLt {n} (i : Nat) (hi : i < n) :
    (((ofNatLt i hi : FinHTuple h(n)).val : HTuple Nat .leaf) : Nat) = i := by
  rfl

@[simp, norm_cast]
theorem coe_toFin_nat' (i : FinHTuple h(n)) : (((i : Fin n) : Nat) = (i : Nat)) := by
  cases i with
  | mk val h =>
      cases val
      rfl

variable {n} (i : FinHTuple h(n)) (j : Fin n)

instance [GetElem cont (Fin n) elem dom] :
    GetElem cont (FinHTuple (.leaf n)) elem (fun xs i => dom xs i.toFin) where
  getElem xs i h := xs[i.toFin]'h

instance [SetElem cont (Fin n) elem dom] :
    SetElem cont (FinHTuple (.leaf n)) elem (fun xs i => dom xs i.toFin) where
  setElem xs i x h := setElem xs i.toFin x h
  setElem_valid := by
    intro xs i j v hi
    exact SetElem.setElem_valid

@[simp]
theorem getElem_toFin [GetElem cont (Fin n) elem dom] (xs : cont) (i : FinHTuple (.leaf n)) (h) :
  xs[i]'h = xs[i.toFin] := by rfl

@[simp]
theorem setElem_toFin [SetElem cont (Fin n) elem dom]
    (xs : cont) (i : FinHTuple (.leaf n)) (x : elem) (h) :
    setElem xs i x h = setElem xs i.toFin x h := by
  rfl

end FinHTuple

end NumLean
