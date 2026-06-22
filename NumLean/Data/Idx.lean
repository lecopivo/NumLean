import Mathlib.Data.FinEnum

namespace NumLean

/-- `Idx n` is the type of indices `0, 1, …, n-1` backed by a native `UInt64`.

It is the fast counterpart of `Fin n`: arithmetic on the underlying `UInt64` compiles to
machine integer operations. The conversion to/from `Fin n` is a genuine bijection exactly when
`n ≤ 2 ^ 64`; for larger `n` the type `Idx n` simply cannot represent every index (there are only
`2 ^ 64` machine integers), which is why several lemmas relating `Idx n` and `Fin n` carry the
hypothesis `n < 2 ^ 64`. -/
structure Idx (n : Nat) where
  val : UInt64
  isLt : val.toNat < n


attribute [coe] Idx.val

theorem Idx.eq_of_val_eq {n} : ∀ {i j : Idx n}, Eq i.val j.val → Eq i j
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem Idx.val_eq_of_eq {n} {i j : Idx n} (h : Eq i j) : Eq i.val j.val :=
  h ▸ rfl

theorem Idx.val_inj {n} {i j : Idx n} : i.val = j.val ↔ i = j :=
  ⟨Idx.eq_of_val_eq, Idx.val_eq_of_eq⟩

@[ext]
theorem Idx.ext {n} {i j : Idx n} (h : i.val = j.val) : i = j :=
  Idx.eq_of_val_eq h

instance {n} : LT (Idx n) where
  lt a b := a.val < b.val

instance {n} : LE (Idx n) where
  le a b := a.val ≤ b.val

instance : BEq (Idx n) where
  beq a b := a.val == b.val

instance {n} : DecidableEq (Idx n) := fun i j =>
  if h : i.val = j.val then
    .isTrue (Idx.eq_of_val_eq h)
  else
    .isFalse (fun hij => h (Idx.val_eq_of_eq hij))

instance Idx.decLt {n} (a b : Idx n) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (a.val < b.val))

instance Idx.decLe {n} (a b : Idx n) : Decidable (LE.le a b) :=
  inferInstanceAs (Decidable (a.val ≤ b.val))

/-- Numeric literals for `Idx (n+1)`, reduced modulo `n+1` (mirroring `Fin.instOfNat`). -/
instance instOfNatIdx {n : Nat} (i : Nat) : OfNat (Idx (n + 1)) i where
  ofNat := ⟨(i % (n + 1)).toUInt64, by
    calc ((i % (n + 1)).toUInt64).toNat
        = (i % (n + 1)) % 2 ^ 64 := UInt64.toNat_ofNat'
      _ ≤ i % (n + 1)            := Nat.mod_le _ _
      _ < n + 1                  := Nat.mod_lt _ (Nat.succ_pos n)⟩

namespace Idx

instance coeToUSize : CoeOut (Idx n) UInt64 :=
  ⟨fun v => v.val⟩

instance coeToNat : CoeOut (Idx n) Nat :=
  ⟨fun v => v.val.toNat⟩

/-- The index `i : Idx n` as an element of `Fin n`. -/
def toFin (i : Idx n) : Fin n := ⟨i.val.toNat, i.isLt⟩

/-- An element of `Fin n` as an index `Idx n`. The underlying `UInt64` is `i.val` reduced modulo
`2 ^ 64`; this is a faithful encoding precisely when `n ≤ 2 ^ 64`. -/
def _root_.Fin.toIdx (i : Fin n) : Idx n := ⟨i.1.toUInt64, by
  calc (i.1.toUInt64).toNat
      = i.1 % 2 ^ 64 := UInt64.toNat_ofNat'
    _ ≤ i.1          := Nat.mod_le _ _
    _ < n            := i.2⟩

@[simp]
theorem toFin_val (i : Idx n) : (i.toFin).val = i.val.toNat := rfl

@[simp]
theorem val_toIdx (i : Fin n) : (Fin.toIdx i).val = i.1.toUInt64 := rfl

@[simp]
theorem toIdx_toFin (i : Idx n) : (i.toFin).toIdx = i := by
  apply Idx.ext
  change (i.val.toNat).toUInt64 = i.val
  exact UInt64.ofNat_toNat

theorem toFin_toIdx (i : Fin n) (h : n < 2 ^ 64) : (Fin.toIdx i).toFin = i := by
  apply Fin.ext
  change ((i.1.toUInt64).toNat) = i.1
  rw [show (i.1.toUInt64) = UInt64.ofNat i.1 from rfl, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (i.2.trans h)

/-- The underlying `Nat` of `Fin.toIdx i` is `i` itself, provided `n` fits in a `UInt64`. -/
theorem toNat_toIdx_of_lt (i : Fin n) (h : n < 2 ^ 64) : (Fin.toIdx i).val.toNat = i.1 :=
  congrArg Fin.val (Idx.toFin_toIdx i h)

/-- `Idx n` is in bijection with `Fin n` whenever `n` fits in a `UInt64`. -/
def equivFin (h : n < 2 ^ 64) : Idx n ≃ Fin n where
  toFun := Idx.toFin
  invFun := Fin.toIdx
  left_inv := Idx.toIdx_toFin
  right_inv := fun i => Idx.toFin_toIdx i h

/--
From the empty type `Idx 0`, any desired result `α` can be derived. This is similar to `Empty.elim`.
-/
def elim0.{u} {α : Sort u} : Idx 0 → α
  | ⟨_, h⟩ => absurd h (by omega)

end Idx

instance : IsEmpty (Idx 0) := ⟨fun i => absurd i.isLt (by omega)⟩

instance : Subsingleton (Idx 1) :=
  ⟨fun a b => Idx.ext (UInt64.toNat_inj.mp (by have := a.isLt; have := b.isLt; omega))⟩

/-- `UInt64` is in computable bijection with `Fin UInt64.size`. -/
def _root_.UInt64.equivFin : UInt64 ≃ Fin UInt64.size where
  toFun := UInt64.toFin
  invFun := UInt64.ofFin
  left_inv := UInt64.ofFin_toFin
  right_inv := UInt64.toFin_ofFin

/-- Reducing a `UInt64` modulo a positive `Nat` always lands below that `Nat`. This is the
key totality fact for clamping out-of-range decoded indices back in range. -/
theorem UInt64.toNat_mod_toUInt64_lt (x : UInt64) {k : Nat} (hk : 0 < k) :
    (x % k.toUInt64).toNat < k := by
  rw [UInt64.toNat_mod, show (k.toUInt64).toNat = k % 2 ^ 64 from UInt64.toNat_ofNat']
  rcases Nat.eq_zero_or_pos (k % 2 ^ 64) with h0 | hpos
  · rw [h0, Nat.mod_zero]
    exact lt_of_lt_of_le (UInt64.toNat_lt x) (by omega)
  · exact lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.mod_le _ _)

/-- A `Nat` that fits in a `UInt64` round-trips through `Nat.toUInt64`. -/
theorem UInt64.toNat_toUInt64_of_lt {k : Nat} (h : k < 2 ^ 64) : (k.toUInt64).toNat = k := by
  rw [show k.toUInt64 = UInt64.ofNat k from rfl, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- The exact `UInt64` Euclidean identity: `b * (x / b) + x % b = x` (no overflow occurs because
both summands are bounded by `x`). -/
theorem UInt64.div_add_mod' (x b : UInt64) : b * (x / b) + x % b = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod]
  have key := Nat.div_add_mod x.toNat b.toNat
  have hlt := UInt64.toNat_lt x
  rw [Nat.mod_eq_of_lt (by omega : b.toNat * (x.toNat / b.toNat) < 2 ^ 64), key,
      Nat.mod_eq_of_lt hlt]

/-- Reducing `x` modulo `k` is the identity when `x < k ≤ 2 ^ 64`. -/
theorem UInt64.mod_toUInt64_eq_self {x : UInt64} {k : Nat} (hk : k < 2 ^ 64) (hx : x.toNat < k) :
    x % k.toUInt64 = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, UInt64.toNat_toUInt64_of_lt hk, Nat.mod_eq_of_lt hx]

/-- The "row-major" combined index `nJ * a + b` (computed natively in `UInt64`) has the expected
`Nat` value when the product `nI * nJ` fits in a `UInt64`. -/
theorem Idx.toNat_merge {nI nJ : Nat} (a : Idx nI) (b : Idx nJ) (h : nI * nJ < 2 ^ 64) :
    (nJ.toUInt64 * a.val + b.val).toNat = nJ * a.val.toNat + b.val.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hnI : 0 < nI := by omega
  have hnJ : 0 < nJ := by omega
  have hle : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ hnI
  have hnJlt : nJ < 2 ^ 64 := by omega
  have hmul : nJ * a.val.toNat < nI * nJ := by
    rw [Nat.mul_comm nI nJ]; exact Nat.mul_lt_mul_of_pos_left ha hnJ
  have hsum : nJ * a.val.toNat + b.val.toNat < nI * nJ := by
    rw [Nat.mul_comm nI nJ]
    calc nJ * a.val.toNat + b.val.toNat
        < nJ * a.val.toNat + nJ := by omega
      _ = nJ * (a.val.toNat + 1)  := by rw [Nat.mul_succ]
      _ ≤ nJ * nI                 := by gcongr; omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_toUInt64_of_lt hnJlt,
      Nat.mod_eq_of_lt (by omega : nJ * a.val.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : nJ * a.val.toNat + b.val.toNat < 2 ^ 64)]

/-- Recovering the first component of a combined index by division. -/
theorem Idx.merge_div {nI nJ : Nat} (a : Idx nI) (b : Idx nJ) (h : nI * nJ < 2 ^ 64) :
    (nJ.toUInt64 * a.val + b.val) / nJ.toUInt64 = a.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hnJ : 0 < nJ := by omega
  have hnJlt : nJ < 2 ^ 64 := by
    have hle : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ (by omega); omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, Idx.toNat_merge a b h, UInt64.toNat_toUInt64_of_lt hnJlt,
      Nat.mul_add_div hnJ, Nat.div_eq_of_lt hb, Nat.add_zero]

/-- Recovering the second component of a combined index by remainder. -/
theorem Idx.merge_mod {nI nJ : Nat} (a : Idx nI) (b : Idx nJ) (h : nI * nJ < 2 ^ 64) :
    (nJ.toUInt64 * a.val + b.val) % nJ.toUInt64 = b.val := by
  have ha := a.isLt
  have hb := b.isLt
  have hnJlt : nJ < 2 ^ 64 := by
    have hle : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ (by omega); omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, Idx.toNat_merge a b h, UInt64.toNat_toUInt64_of_lt hnJlt,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

theorem Nat.pos_left_of_mul_pos {a b : Nat} (h : 0 < a * b) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0, Nat.zero_mul] at h; exact absurd h (lt_irrefl 0)
  · exact h0

theorem Nat.pos_right_of_mul_pos {a b : Nat} (h : 0 < a * b) : 0 < b := by
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · rw [h0, Nat.mul_zero] at h; exact absurd h (lt_irrefl 0)
  · exact h0

/-! ### Product encode / decode

The row-major pairing of indices, computed natively in `UInt64`. These are total for every `nI`,
`nJ`; the decode clamps with `%` so it produces in-range components even when `nI * nJ` overflows
(in which case the round-trip laws are not claimed). -/

/-- Combine indices `a : Idx nI`, `b : Idx nJ` into `Idx (nI * nJ)` as `nJ * a + b`. -/
@[inline]
def Idx.merge {nI nJ : Nat} (a : Idx nI) (b : Idx nJ) : Idx (nI * nJ) :=
  ⟨nJ.toUInt64 * a.val + b.val, by
    rcases lt_or_ge (nI * nJ) (2 ^ 64) with hlt | hge
    · rw [Idx.toNat_merge a b hlt]
      have ha := a.isLt
      have hb := b.isLt
      have hnJ : 0 < nJ := by omega
      calc nJ * a.val.toNat + b.val.toNat
          < nJ * a.val.toNat + nJ := by omega
        _ = nJ * (a.val.toNat + 1)  := by rw [Nat.mul_succ]
        _ ≤ nJ * nI                 := by gcongr; omega
        _ = nI * nJ                 := Nat.mul_comm _ _
    · exact lt_of_lt_of_le (UInt64.toNat_lt _) hge⟩

/-- First (row) component of a combined index, clamped into range. -/
@[inline]
def Idx.divIdx (nI nJ : Nat) (i : Idx (nI * nJ)) : Idx nI :=
  ⟨(i.val / nJ.toUInt64) % nI.toUInt64, by
    have hpos : 0 < nI * nJ := by have := i.isLt; omega
    exact UInt64.toNat_mod_toUInt64_lt _ (Nat.pos_left_of_mul_pos hpos)⟩

/-- Second (column) component of a combined index. -/
@[inline]
def Idx.modIdx (nI nJ : Nat) (i : Idx (nI * nJ)) : Idx nJ :=
  ⟨i.val % nJ.toUInt64, by
    have hpos : 0 < nI * nJ := by have := i.isLt; omega
    exact UInt64.toNat_mod_toUInt64_lt _ (Nat.pos_right_of_mul_pos hpos)⟩

theorem Idx.divIdx_merge {nI nJ : Nat} (a : Idx nI) (b : Idx nJ) (h : nI * nJ < 2 ^ 64) :
    Idx.divIdx nI nJ (Idx.merge a b) = a := by
  have hb := b.isLt
  have hnJ : 0 < nJ := by omega
  have hnIlt : nI < 2 ^ 64 := by
    have : nI ≤ nI * nJ := Nat.le_mul_of_pos_right nI hnJ; omega
  apply Idx.ext
  change ((Idx.merge a b).val / nJ.toUInt64) % nI.toUInt64 = a.val
  rw [show (Idx.merge a b).val = nJ.toUInt64 * a.val + b.val from rfl, Idx.merge_div a b h,
      UInt64.mod_toUInt64_eq_self hnIlt a.isLt]

theorem Idx.modIdx_merge {nI nJ : Nat} (a : Idx nI) (b : Idx nJ) (h : nI * nJ < 2 ^ 64) :
    Idx.modIdx nI nJ (Idx.merge a b) = b := by
  apply Idx.ext
  change ((Idx.merge a b).val) % nJ.toUInt64 = b.val
  rw [show (Idx.merge a b).val = nJ.toUInt64 * a.val + b.val from rfl, Idx.merge_mod a b h]

theorem Idx.merge_divIdx_modIdx {nI nJ : Nat} (i : Idx (nI * nJ)) (h : nI * nJ < 2 ^ 64) :
    Idx.merge (Idx.divIdx nI nJ i) (Idx.modIdx nI nJ i) = i := by
  have hpos : 0 < nI * nJ := by have := i.isLt; omega
  have hnI : 0 < nI := Nat.pos_left_of_mul_pos hpos
  have hnJ : 0 < nJ := Nat.pos_right_of_mul_pos hpos
  have hnJlt : nJ < 2 ^ 64 := by have : nJ ≤ nI * nJ := Nat.le_mul_of_pos_left nJ hnI; omega
  have hnIlt : nI < 2 ^ 64 := by have : nI ≤ nI * nJ := Nat.le_mul_of_pos_right nI hnJ; omega
  have hx : (i.val / nJ.toUInt64).toNat < nI := by
    rw [UInt64.toNat_div, UInt64.toNat_toUInt64_of_lt hnJlt]
    exact (Nat.div_lt_iff_lt_mul hnJ).mpr i.isLt
  apply Idx.ext
  change nJ.toUInt64 * ((i.val / nJ.toUInt64) % nI.toUInt64) + (i.val % nJ.toUInt64) = i.val
  rw [UInt64.mod_toUInt64_eq_self hnIlt hx, UInt64.div_add_mod']

/-! ### Sum encode / decode

The disjoint-union pairing: `inl` keeps the index, `inr` shifts by `m`. Decoding branches on the
`Nat` test `i < m` (so the empty-summand branch is provably unreachable) and clamps the right
part. -/

/-- Embed `Idx m` into `Idx (m + n)` on the left. -/
@[inline]
def Idx.inl (m n : Nat) (a : Idx m) : Idx (m + n) :=
  ⟨a.val, by have := a.isLt; omega⟩

/-- Embed `Idx n` into `Idx (m + n)` on the right, shifted by `m`. -/
@[inline]
def Idx.inr (m n : Nat) (b : Idx n) : Idx (m + n) :=
  ⟨m.toUInt64 + b.val, by
    rcases lt_or_ge (m + n) (2 ^ 64) with hlt | hge
    · have hb := b.isLt
      have hmlt : m < 2 ^ 64 := by omega
      rw [UInt64.toNat_add, UInt64.toNat_toUInt64_of_lt hmlt, Nat.mod_eq_of_lt (by omega)]
      omega
    · exact lt_of_lt_of_le (UInt64.toNat_lt _) hge⟩

theorem Idx.val_inl (m n : Nat) (a : Idx m) : (Idx.inl m n a).val = a.val := rfl

theorem Idx.toNat_inr (m n : Nat) (b : Idx n) (h : m + n < 2 ^ 64) :
    (Idx.inr m n b).val.toNat = m + b.val.toNat := by
  have hb := b.isLt
  have hmlt : m < 2 ^ 64 := by omega
  change (m.toUInt64 + b.val).toNat = m + b.val.toNat
  rw [UInt64.toNat_add, UInt64.toNat_toUInt64_of_lt hmlt, Nat.mod_eq_of_lt (by omega)]

theorem Idx.sub_inr (m n : Nat) (b : Idx n) (h : m + n < 2 ^ 64) :
    (Idx.inr m n b).val - m.toUInt64 = b.val := by
  have hb := b.isLt
  have hmlt : m < 2 ^ 64 := by omega
  have hbb := UInt64.toNat_lt b.val
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub, Idx.toNat_inr m n b h, UInt64.toNat_toUInt64_of_lt hmlt]
  omega

/-- Encode an `Idx m ⊕ Idx n` as an `Idx (m + n)`. -/
@[inline]
def Idx.sumEncode (m n : Nat) : Idx m ⊕ Idx n → Idx (m + n)
  | Sum.inl a => Idx.inl m n a
  | Sum.inr b => Idx.inr m n b

/-- Decode an `Idx (m + n)` into `Idx m ⊕ Idx n`, clamping the right part for totality. -/
@[inline]
def Idx.sumDecode (m n : Nat) (i : Idx (m + n)) : Idx m ⊕ Idx n :=
  if h : i.val.toNat < m then
    Sum.inl ⟨i.val, h⟩
  else
    Sum.inr ⟨(i.val - m.toUInt64) % n.toUInt64, by
      have h1 := i.isLt
      exact UInt64.toNat_mod_toUInt64_lt _ (by omega)⟩

theorem Idx.sumDecode_encode (m n : Nat) (h : m + n < 2 ^ 64) (x : Idx m ⊕ Idx n) :
    Idx.sumDecode m n (Idx.sumEncode m n x) = x := by
  have hmlt : m < 2 ^ 64 := by omega
  have hnlt : n < 2 ^ 64 := by omega
  cases x with
  | inl a =>
    have hga : (Idx.inl m n a).val.toNat < m := a.isLt
    change Idx.sumDecode m n (Idx.inl m n a) = Sum.inl a
    rw [Idx.sumDecode, dif_pos hga]
    exact congrArg Sum.inl (Idx.ext rfl)
  | inr b =>
    have hgb : ¬ (Idx.inr m n b).val.toNat < m := by rw [Idx.toNat_inr m n b h]; omega
    change Idx.sumDecode m n (Idx.inr m n b) = Sum.inr b
    rw [Idx.sumDecode, dif_neg hgb]
    refine congrArg Sum.inr (Idx.ext ?_)
    change ((Idx.inr m n b).val - m.toUInt64) % n.toUInt64 = b.val
    rw [Idx.sub_inr m n b h, UInt64.mod_toUInt64_eq_self hnlt b.isLt]

theorem Idx.sumEncode_decode (m n : Nat) (h : m + n < 2 ^ 64) (i : Idx (m + n)) :
    Idx.sumEncode m n (Idx.sumDecode m n i) = i := by
  have hmlt : m < 2 ^ 64 := by omega
  have hnlt : n < 2 ^ 64 := by omega
  rw [Idx.sumDecode]
  by_cases hc : i.val.toNat < m
  · rw [dif_pos hc]
    apply Idx.ext
    change (Idx.inl m n ⟨i.val, hc⟩).val = i.val
    rfl
  · rw [dif_neg hc]
    have h2 : m ≤ i.val.toNat := Nat.le_of_not_lt hc
    have hsublt : (i.val - m.toUInt64).toNat < n := by
      have hle : m.toUInt64 ≤ i.val := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_toUInt64_of_lt hmlt]; exact h2
      rw [UInt64.toNat_sub, UInt64.toNat_toUInt64_of_lt hmlt]
      have := i.isLt
      omega
    apply Idx.ext
    change m.toUInt64 + ((i.val - m.toUInt64) % n.toUInt64) = i.val
    rw [UInt64.mod_toUInt64_eq_self hnlt hsublt]
    apply UInt64.toNat_inj.mp
    have hle : m ≤ i.val.toNat := h2
    have hbb := UInt64.toNat_lt i.val
    rw [UInt64.toNat_add, UInt64.toNat_toUInt64_of_lt hmlt, UInt64.toNat_sub,
        UInt64.toNat_toUInt64_of_lt hmlt]
    omega

end NumLean
