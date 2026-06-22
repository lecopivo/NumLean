import Mathlib.Data.FinEnum

namespace NumLean

inductive NatPrecision where
  | single | double | inf

def Precision.withinPrec (p : NatPrecision) (n : Nat) : Prop :=
  match p with
  | .single => n < 2 ^ 32
  | .double => n < 2 ^ 64
  | .inf => True

def UIntP (p : NatPrecision) : Type :=
  match p with
  | .single => UInt32
  | .double => UInt64
  | .inf => Nat

def UIntP.toNat {p} (n : UIntP p) : Nat :=
  match p with
  | .single => UInt32.toNat n
  | .double => UInt64.toNat n
  | .inf => n

def IntP (p : NatPrecision) : Type :=
  match p with
  | .single => Int32
  | .double => Int64
  | .inf => Int

structure IdxP (n : Nat) (p : NatPrecision := .double) where
  val : UIntP p
  isLt: val.toNat < n

def UIntP.ofNat (p : NatPrecision) (n : Nat) : UIntP p :=
  match p with
  | .single => n.toUInt32
  | .double => n.toUInt64
  | .inf    => n

@[simp] theorem UIntP.toNat_single (n : UInt32) : (n : UIntP .single).toNat = n.toNat := rfl
@[simp] theorem UIntP.toNat_double (n : UInt64) : (n : UIntP .double).toNat = n.toNat := rfl
@[simp] theorem UIntP.toNat_inf   (n : Nat)    : UIntP.toNat (p:=.inf) (n : UIntP .inf) = n  := rfl
@[simp] theorem UIntP.ofNat_single (n : Nat) : UIntP.ofNat .single n = n.toUInt32 := rfl
@[simp] theorem UIntP.ofNat_double (n : Nat) : UIntP.ofNat .double n = n.toUInt64 := rfl
@[simp] theorem UIntP.ofNat_inf    (n : Nat) : UIntP.ofNat .inf    n = n          := rfl

theorem UIntP.toNat_ofNat_le (p : NatPrecision) (n : Nat) : (UIntP.ofNat p n).toNat ≤ n := by
  match p with
  | .single =>
    change UInt32.toNat n.toUInt32 ≤ n
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_le _ _
  | .double =>
    change UInt64.toNat n.toUInt64 ≤ n
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  | .inf => exact le_refl n

theorem UIntP.toNat_ofNat_eq {p : NatPrecision} {n k : Nat}
    (hk : k < n) (hn : Precision.withinPrec p n) : (UIntP.ofNat p k).toNat = k := by
  match p with
  | .single =>
    change UInt32.toNat k.toUInt32 = k
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (hk.trans hn)
  | .double =>
    change UInt64.toNat k.toUInt64 = k
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (hk.trans hn)
  | .inf => rfl

theorem UIntP.toNat_inj {p} {a b : UIntP p} : a.toNat = b.toNat ↔ a = b := by
  match p with
  | .single => exact UInt32.toNat_inj
  | .double => exact UInt64.toNat_inj
  | .inf    => exact Iff.rfl

theorem UIntP.ofNat_toNat {p} (v : UIntP p) : UIntP.ofNat p v.toNat = v := by
  match p with
  | .single =>
    change (UInt32.toNat v).toUInt32 = v
    exact UInt32.ofNat_toNat
  | .double =>
    change (UInt64.toNat v).toUInt64 = v
    exact UInt64.ofNat_toNat
  | .inf => rfl

instance {p} : Add (UIntP p) :=
  match p with
  | .single => inferInstanceAs (Add UInt32)
  | .double => inferInstanceAs (Add UInt64)
  | .inf    => inferInstanceAs (Add Nat)

instance {p} : Sub (UIntP p) :=
  match p with
  | .single => inferInstanceAs (Sub UInt32)
  | .double => inferInstanceAs (Sub UInt64)
  | .inf    => inferInstanceAs (Sub Nat)

instance {p} : Mul (UIntP p) :=
  match p with
  | .single => inferInstanceAs (Mul UInt32)
  | .double => inferInstanceAs (Mul UInt64)
  | .inf    => inferInstanceAs (Mul Nat)

instance {p} : Div (UIntP p) :=
  match p with
  | .single => inferInstanceAs (Div UInt32)
  | .double => inferInstanceAs (Div UInt64)
  | .inf    => inferInstanceAs (Div Nat)

instance {p} : Mod (UIntP p) :=
  match p with
  | .single => inferInstanceAs (Mod UInt32)
  | .double => inferInstanceAs (Mod UInt64)
  | .inf    => inferInstanceAs (Mod Nat)

instance {p} : DecidableEq (UIntP p) :=
  match p with
  | .single => inferInstanceAs (DecidableEq UInt32)
  | .double => inferInstanceAs (DecidableEq UInt64)
  | .inf    => inferInstanceAs (DecidableEq Nat)

instance {p} : LT (UIntP p) :=
  match p with
  | .single => inferInstanceAs (LT UInt32)
  | .double => inferInstanceAs (LT UInt64)
  | .inf    => inferInstanceAs (LT Nat)

instance {p} : LE (UIntP p) :=
  match p with
  | .single => inferInstanceAs (LE UInt32)
  | .double => inferInstanceAs (LE UInt64)
  | .inf    => inferInstanceAs (LE Nat)

instance {p} : BEq (UIntP p) :=
  match p with
  | .single => inferInstanceAs (BEq UInt32)
  | .double => inferInstanceAs (BEq UInt64)
  | .inf    => inferInstanceAs (BEq Nat)

-- instance {p} (a b : UIntP p) : Decidable (a < b) :=
--   match p with
--   | .single => inferInstanceAs (Decidable ((a : UInt32) < (b : UInt32)))
--   | .double => inferInstanceAs (Decidable ((a : UInt64) < (b : UInt64)))
--   | .inf    => inferInstanceAs (Decidable ((a : Nat) < (b : Nat)))

-- instance {p} (a b : UIntP p) : Decidable (a ≤ b) :=
--   match p with
--   | .single => inferInstanceAs (Decidable ((a : UInt32) ≤ (b : UInt32)))
--   | .double => inferInstanceAs (Decidable ((a : UInt64) ≤ (b : UInt64)))
--   | .inf    => inferInstanceAs (Decidable ((a : Nat) ≤ (b : Nat)))

-- attribute [coe] IdxP.val

-- theorem IdxP.eq_of_val_eq {n p} : ∀ {i j : IdxP n p}, Eq i.val j.val → Eq i j
--   | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

-- theorem IdxP.val_eq_of_eq {n p} {i j : IdxP n p} (h : Eq i j) : Eq i.val j.val :=
--   h ▸ rfl

-- theorem IdxP.val_inj {n p} {i j : IdxP n p} : i.val = j.val ↔ i = j :=
--   ⟨IdxP.eq_of_val_eq, IdxP.val_eq_of_eq⟩

-- @[ext]
-- theorem IdxP.ext {n p} {i j : IdxP n p} (h : i.val = j.val) : i = j :=
--   IdxP.eq_of_val_eq h

-- instance {n p} : LT (IdxP n p) where
--   lt a b := a.val < b.val

-- instance {n p} : LE (IdxP n p) where
--   le a b := a.val ≤ b.val

-- instance {n p} : BEq (IdxP n p) where
--   beq a b := a.val == b.val

-- instance {n p} : DecidableEq (IdxP n p) := fun i j =>
--   if h : i.val = j.val then
--     .isTrue (IdxP.eq_of_val_eq h)
--   else
--     .isFalse (fun hij => h (IdxP.val_eq_of_eq hij))

-- instance IdxP.decLt {n p} (a b : IdxP n p) : Decidable (LT.lt a b) :=
--   inferInstanceAs (Decidable (a.val < b.val))

-- instance IdxP.decLe {n p} (a b : IdxP n p) : Decidable (LE.le a b) :=
--   inferInstanceAs (Decidable (a.val ≤ b.val))

-- instance instOfNatIdxP {n : Nat} {p : NatPrecision} (i : Nat) : OfNat (IdxP (n + 1) p) i where
--   ofNat := ⟨UIntP.ofNat p (i % (n + 1)), by
--     have hlt : i % (n + 1) < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
--     exact lt_of_le_of_lt (UIntP.toNat_ofNat_le p _) hlt⟩

-- namespace IdxP

-- instance coeToNat {n p} : CoeOut (IdxP n p) Nat :=
--   ⟨fun v => v.val.toNat⟩

-- def toFin {n p} (i : IdxP n p) : Fin n := ⟨i.val.toNat, i.isLt⟩

-- def _root_.Fin.toIdxP (p : NatPrecision) {n} (i : Fin n) : IdxP n p :=
--   ⟨UIntP.ofNat p i.1, lt_of_le_of_lt (UIntP.toNat_ofNat_le p _) i.2⟩

-- @[simp]
-- theorem toFin_val {n p} (i : IdxP n p) : (i.toFin).val = i.val.toNat := rfl

-- @[simp]
-- theorem val_toIdxP (p : NatPrecision) {n} (i : Fin n) :
--     (Fin.toIdxP p i).val = UIntP.ofNat p i.1 := rfl

-- @[simp]
-- theorem toIdxP_toFin {n p} (i : IdxP n p) : Fin.toIdxP p i.toFin = i := by
--   apply IdxP.ext
--   change UIntP.ofNat p i.val.toNat = i.val
--   exact UIntP.ofNat_toNat i.val

-- theorem toFin_toIdxP (p : NatPrecision) {n} (i : Fin n) (h : Precision.withinPrec p n) :
--     (Fin.toIdxP p i).toFin = i := by
--   apply Fin.ext
--   change (UIntP.ofNat p i.1).toNat = i.1
--   exact UIntP.toNat_ofNat_eq i.2 h

-- def equivFin {n p} (h : Precision.withinPrec p n) : IdxP n p ≃ Fin n where
--   toFun    := IdxP.toFin
--   invFun   := Fin.toIdxP p
--   left_inv := IdxP.toIdxP_toFin
--   right_inv := fun i => IdxP.toFin_toIdxP p i h

-- def elim0.{u} {p} {α : Sort u} : IdxP 0 p → α
--   | ⟨_, h⟩ => absurd h (by omega)

-- end IdxP

-- instance {p} : IsEmpty (IdxP 0 p) := ⟨fun i => absurd i.isLt (by omega)⟩

-- instance {p} : Subsingleton (IdxP 1 p) :=
--   ⟨fun a b => IdxP.ext (UIntP.toNat_inj.mp (by have := a.isLt; have := b.isLt; omega))⟩

-- instance instFintypeIdxP {n p} : Fintype (IdxP n p) :=
--   Fintype.ofEquiv {v : UIntP p // v.toNat < n}
--     ⟨fun v => ⟨v.1, v.2⟩, fun i => ⟨i.val, i.isLt⟩, fun _ => rfl, fun _ => rfl⟩

-- theorem UIntP.toNat_mod_toUIntP_lt {p} (x : UIntP p) {k : Nat} (hk : 0 < k) :
--     (x % UIntP.ofNat p k).toNat < k := by
--   match p with
--   | .single =>
--     simp only [UIntP.ofNat_single, UIntP.toNat_single]
--     rw [UInt32.toNat_mod, show (k.toUInt32).toNat = k % 2 ^ 32 from UInt32.toNat_ofNat']
--     rcases Nat.eq_zero_or_pos (k % 2 ^ 32) with h0 | hpos
--     · rw [h0, Nat.mod_zero]; exact lt_of_lt_of_le (UInt32.toNat_lt x) (by omega)
--     · exact lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.mod_le _ _)
--   | .double =>
--     simp only [UIntP.ofNat_double, UIntP.toNat_double]
--     rw [UInt64.toNat_mod, show (k.toUInt64).toNat = k % 2 ^ 64 from UInt64.toNat_ofNat']
--     rcases Nat.eq_zero_or_pos (k % 2 ^ 64) with h0 | hpos
--     · rw [h0, Nat.mod_zero]; exact lt_of_lt_of_le (UInt64.toNat_lt x) (by omega)
--     · exact lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.mod_le _ _)
--   | .inf => exact Nat.mod_lt _ hk

-- theorem UIntP.div_add_mod' {p} (x b : UIntP p) : b * (x / b) + x % b = x := by
--   match p with
--   | .single =>
--     apply UIntP.toNat_inj.mp
--     simp only [UIntP.toNat_single]
--     rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_div, UInt32.toNat_mod]
--     have key := Nat.div_add_mod (UInt32.toNat x) (UInt32.toNat b)
--     have hlt  := UInt32.toNat_lt x
--     omega
--   | .double =>
--     apply UIntP.toNat_inj.mp
--     simp only [UIntP.toNat_double]
--     rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod]
--     have key := Nat.div_add_mod (UInt64.toNat x) (UInt64.toNat b)
--     have hlt  := UInt64.toNat_lt x
--     omega
--   | .inf => exact Nat.div_add_mod x b

-- theorem UIntP.mod_toUIntP_eq_self {p} {x : UIntP p} {k : Nat}
--     (hk : Precision.withinPrec p k) (hx : x.toNat < k) : x % UIntP.ofNat p k = x := by
--   match p with
--   | .single =>
--     apply UIntP.toNat_inj.mp
--     simp only [UIntP.ofNat_single, UIntP.toNat_single]
--     rw [UInt32.toNat_mod, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hk]
--     exact Nat.mod_eq_of_lt hx
--   | .double =>
--     apply UIntP.toNat_inj.mp
--     simp only [UIntP.ofNat_double, UIntP.toNat_double]
--     rw [UInt64.toNat_mod, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hk]
--     exact Nat.mod_eq_of_lt hx
--   | .inf => exact Nat.mod_eq_of_lt hx

-- /-! ### Product encode / decode -/

-- theorem IdxP.toNat_merge {nI nJ : Nat} {p} (a : IdxP nI p) (b : IdxP nJ p)
--     (h : Precision.withinPrec p (nI * nJ)) :
--     (UIntP.ofNat p nJ * a.val + b.val).toNat = nJ * a.val.toNat + b.val.toNat := by
--   have ha := a.isLt; have hb := b.isLt
--   match p with
--   | .inf => rfl
--   | .single =>
--     simp only [UIntP.ofNat_single, UIntP.toNat_single] at *
--     have hnI : 0 < nI := by omega
--     have hnJ : 0 < nJ := by omega
--     have hnJlt : nJ < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ hnI) h
--     have hmul : nJ * UInt32.toNat a.val < nI * nJ := by
--       rw [Nat.mul_comm nI nJ]; exact Nat.mul_lt_mul_of_pos_left ha hnJ
--     have hsum : nJ * UInt32.toNat a.val + UInt32.toNat b.val < nI * nJ := by
--       rw [Nat.mul_comm nI nJ]
--       calc nJ * UInt32.toNat a.val + UInt32.toNat b.val
--           < nJ * UInt32.toNat a.val + nJ := by omega
--         _ = nJ * (UInt32.toNat a.val + 1) := by rw [Nat.mul_succ]
--         _ ≤ nJ * nI               := by gcongr; omega
--     rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hnJlt]
--     omega
--   | .double =>
--     simp only [UIntP.ofNat_double, UIntP.toNat_double] at *
--     have hnI : 0 < nI := by omega
--     have hnJ : 0 < nJ := by omega
--     have hnJlt : nJ < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ hnI) h
--     have hmul : nJ * UInt64.toNat a.val < nI * nJ := by
--       rw [Nat.mul_comm nI nJ]; exact Nat.mul_lt_mul_of_pos_left ha hnJ
--     have hsum : nJ * UInt64.toNat a.val + UInt64.toNat b.val < nI * nJ := by
--       rw [Nat.mul_comm nI nJ]
--       calc nJ * UInt64.toNat a.val + UInt64.toNat b.val
--           < nJ * UInt64.toNat a.val + nJ := by omega
--         _ = nJ * (UInt64.toNat a.val + 1) := by rw [Nat.mul_succ]
--         _ ≤ nJ * nI               := by gcongr; omega
--     rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hnJlt]
--     omega

-- theorem IdxP.merge_div {nI nJ : Nat} {p} (a : IdxP nI p) (b : IdxP nJ p)
--     (h : Precision.withinPrec p (nI * nJ)) :
--     (UIntP.ofNat p nJ * a.val + b.val) / UIntP.ofNat p nJ = a.val := by
--   have ha := a.isLt; have hb := b.isLt
--   apply UIntP.toNat_inj.mp
--   match p with
--   | .inf =>
--     simp only [UIntP.ofNat_inf, UIntP.toNat_inf]
--     have hnJ : 0 < nJ := by omega
--     rw [Nat.mul_add_div hnJ, Nat.div_eq_of_lt hb, Nat.add_zero]
--   | .single =>
--     have hnJ : 0 < nJ := by omega
--     have hnJlt : nJ < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ (by omega)) h
--     have hmerge := IdxP.toNat_merge a b h
--     simp only [UIntP.ofNat_single, UIntP.toNat_single] at hmerge ha hb ⊢
--     rw [UInt32.toNat_div, hmerge, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hnJlt,
--         Nat.mul_add_div hnJ, Nat.div_eq_of_lt hb, Nat.add_zero]
--   | .double =>
--     have hnJ : 0 < nJ := by omega
--     have hnJlt : nJ < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ (by omega)) h
--     have hmerge := IdxP.toNat_merge a b h
--     simp only [UIntP.ofNat_double, UIntP.toNat_double] at hmerge ha hb ⊢
--     rw [UInt64.toNat_div, hmerge, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hnJlt,
--         Nat.mul_add_div hnJ, Nat.div_eq_of_lt hb, Nat.add_zero]

-- theorem IdxP.merge_mod {nI nJ : Nat} {p} (a : IdxP nI p) (b : IdxP nJ p)
--     (h : Precision.withinPrec p (nI * nJ)) :
--     (UIntP.ofNat p nJ * a.val + b.val) % UIntP.ofNat p nJ = b.val := by
--   have hb := b.isLt
--   apply UIntP.toNat_inj.mp
--   match p with
--   | .inf =>
--     simp only [UIntP.ofNat_inf, UIntP.toNat_inf]
--     have hnJ : 0 < nJ := by omega
--     rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
--   | .single =>
--     have hnJlt : nJ < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ (by omega)) h
--     have hmerge := IdxP.toNat_merge a b h
--     simp only [UIntP.ofNat_single, UIntP.toNat_single] at hmerge hb ⊢
--     rw [UInt32.toNat_mod, hmerge, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hnJlt,
--         Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
--   | .double =>
--     have hnJlt : nJ < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ (by omega)) h
--     have hmerge := IdxP.toNat_merge a b h
--     simp only [UIntP.ofNat_double, UIntP.toNat_double] at hmerge hb ⊢
--     rw [UInt64.toNat_mod, hmerge, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hnJlt,
--         Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

-- @[inline]
-- def IdxP.merge {nI nJ : Nat} {p} (a : IdxP nI p) (b : IdxP nJ p) : IdxP (nI * nJ) p :=
--   ⟨UIntP.ofNat p nJ * a.val + b.val, by
--     have hpos : 0 < nI * nJ := Nat.mul_pos (by have := a.isLt; omega) (by have := b.isLt; omega)
--     match p with
--     | .inf =>
--       simp only [UIntP.ofNat_inf, UIntP.toNat_inf]
--       have ha := a.isLt; have hb := b.isLt; have hnJ : 0 < nJ := by omega
--       calc nJ * a.val + b.val
--           < nJ * a.val + nJ := by omega
--         _ = nJ * (a.val + 1) := by ring
--         _ ≤ nJ * nI          := by gcongr; omega
--         _ = nI * nJ          := Nat.mul_comm _ _
--     | .single =>
--       simp only [UIntP.toNat_single]
--       have ha := a.isLt; have hb := b.isLt
--       simp only [UIntP.toNat_single] at ha hb
--       rcases lt_or_ge (nI * nJ) (2 ^ 32) with hlt | hge
--       · have hmerge := IdxP.toNat_merge a b (by simpa using hlt)
--         simp only [UIntP.toNat_single] at hmerge
--         rw [hmerge]
--         have hnJ : 0 < nJ := by omega
--         calc nJ * UInt32.toNat a.val + UInt32.toNat b.val
--             < nJ * UInt32.toNat a.val + nJ := by omega
--           _ = nJ * (UInt32.toNat a.val + 1) := by rw [Nat.mul_succ]
--           _ ≤ nJ * nI               := by gcongr; omega
--           _ = nI * nJ               := Nat.mul_comm _ _
--       · exact lt_of_lt_of_le (UInt32.toNat_lt _) hge
--     | .double =>
--       simp only [UIntP.toNat_double]
--       have ha := a.isLt; have hb := b.isLt
--       simp only [UIntP.toNat_double] at ha hb
--       rcases lt_or_ge (nI * nJ) (2 ^ 64) with hlt | hge
--       · have hmerge := IdxP.toNat_merge a b (by simpa using hlt)
--         simp only [UIntP.toNat_double] at hmerge
--         rw [hmerge]
--         have hnJ : 0 < nJ := by omega
--         calc nJ * UInt64.toNat a.val + UInt64.toNat b.val
--             < nJ * UInt64.toNat a.val + nJ := by omega
--           _ = nJ * (UInt64.toNat a.val + 1) := by rw [Nat.mul_succ]
--           _ ≤ nJ * nI               := by gcongr; omega
--           _ = nI * nJ               := Nat.mul_comm _ _
--       · exact lt_of_lt_of_le (UInt64.toNat_lt _) hge⟩

-- @[inline]
-- def IdxP.divIdx {p} (nI nJ : Nat) (i : IdxP (nI * nJ) p) : IdxP nI p :=
--   ⟨(i.val / UIntP.ofNat p nJ) % UIntP.ofNat p nI, by
--     have hpos : 0 < nI * nJ := by have := i.isLt; omega
--     have hnI : 0 < nI := Nat.pos_of_mul_pos_right hpos
--     exact UIntP.toNat_mod_toUIntP_lt _ hnI⟩

-- @[inline]
-- def IdxP.modIdx {p} (nI nJ : Nat) (i : IdxP (nI * nJ) p) : IdxP nJ p :=
--   ⟨i.val % UIntP.ofNat p nJ, by
--     have hpos : 0 < nI * nJ := by have := i.isLt; omega
--     have hnJ : 0 < nJ := Nat.pos_of_mul_pos_left hpos
--     exact UIntP.toNat_mod_toUIntP_lt _ hnJ⟩

-- theorem IdxP.divIdx_merge {nI nJ : Nat} {p} (a : IdxP nI p) (b : IdxP nJ p)
--     (h : Precision.withinPrec p (nI * nJ)) :
--     IdxP.divIdx nI nJ (IdxP.merge a b) = a := by
--   have ha := a.isLt; have hb := b.isLt
--   have hnJ : 0 < nJ := by omega
--   have hnI : 0 < nI := by omega
--   have hnIfit : Precision.withinPrec p nI := by
--     match p with
--     | .inf => trivial
--     | .single => exact lt_of_le_of_lt (Nat.le_mul_of_pos_right nI hnJ) h
--     | .double => exact lt_of_le_of_lt (Nat.le_mul_of_pos_right nI hnJ) h
--   apply IdxP.ext
--   change (IdxP.merge a b).val / UIntP.ofNat p nJ % UIntP.ofNat p nI = a.val
--   rw [show (IdxP.merge a b).val = UIntP.ofNat p nJ * a.val + b.val from rfl,
--       IdxP.merge_div a b h, UIntP.mod_toUIntP_eq_self hnIfit a.isLt]

-- theorem IdxP.modIdx_merge {nI nJ : Nat} {p} (a : IdxP nI p) (b : IdxP nJ p)
--     (h : Precision.withinPrec p (nI * nJ)) :
--     IdxP.modIdx nI nJ (IdxP.merge a b) = b := by
--   apply IdxP.ext
--   change (IdxP.merge a b).val % UIntP.ofNat p nJ = b.val
--   rw [show (IdxP.merge a b).val = UIntP.ofNat p nJ * a.val + b.val from rfl,
--       IdxP.merge_mod a b h]

-- theorem IdxP.merge_divIdx_modIdx {nI nJ : Nat} {p} (i : IdxP (nI * nJ) p)
--     (h : Precision.withinPrec p (nI * nJ)) :
--     IdxP.merge (IdxP.divIdx nI nJ i) (IdxP.modIdx nI nJ i) = i := by
--   have hpos : 0 < nI * nJ := by have := i.isLt; omega
--   have hnI : 0 < nI := Nat.pos_of_mul_pos_right hpos
--   have hnJ : 0 < nJ := Nat.pos_of_mul_pos_left hpos
--   have hnJfit : Precision.withinPrec p nJ := by
--     match p with
--     | .inf => trivial
--     | .single => exact lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ hnI) h
--     | .double => exact lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ hnI) h
--   have hnIfit : Precision.withinPrec p nI := by
--     match p with
--     | .inf => trivial
--     | .single => exact lt_of_le_of_lt (Nat.le_mul_of_pos_right nI hnJ) h
--     | .double => exact lt_of_le_of_lt (Nat.le_mul_of_pos_right nI hnJ) h
--   apply IdxP.ext
--   change UIntP.ofNat p nJ * ((i.val / UIntP.ofNat p nJ) % UIntP.ofNat p nI) +
--       (i.val % UIntP.ofNat p nJ) = i.val
--   have hdiv_lt : (i.val / UIntP.ofNat p nJ).toNat < nI := by
--     match p with
--     | .inf =>
--       simp only [UIntP.ofNat_inf, UIntP.toNat_inf]
--       exact Nat.div_lt_iff_lt_mul hnJ |>.mpr i.isLt
--     | .single =>
--       simp only [UIntP.ofNat_single, UIntP.toNat_single]
--       have hnJlt : nJ < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ hnI) h
--       rw [UInt32.toNat_div, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hnJlt]
--       exact (Nat.div_lt_iff_lt_mul hnJ).mpr i.isLt
--     | .double =>
--       simp only [UIntP.ofNat_double, UIntP.toNat_double]
--       have hnJlt : nJ < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_left nJ hnI) h
--       rw [UInt64.toNat_div, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hnJlt]
--       exact (Nat.div_lt_iff_lt_mul hnJ).mpr i.isLt
--   rw [UIntP.mod_toUIntP_eq_self hnIfit hdiv_lt, UIntP.div_add_mod']

-- /-! ### Sum encode / decode -/

-- theorem UIntP.le_iff_toNat_le {p} {a b : UIntP p} : a ≤ b ↔ a.toNat ≤ b.toNat := by
--   match p with
--   | .single => exact UInt32.le_iff_toNat_le
--   | .double => exact UInt64.le_iff_toNat_le
--   | .inf    => exact Iff.rfl

-- theorem UIntP.toNat_sub_of_le {p} {a b : UIntP p} (h : b ≤ a) :
--     (a - b).toNat = a.toNat - b.toNat := by
--   have hle : b.toNat ≤ a.toNat := UIntP.le_iff_toNat_le.mp h
--   match p with
--   | .single =>
--     simp only [UIntP.toNat_single] at hle ⊢
--     rw [UInt32.toNat_sub]
--     have := UInt32.toNat_lt a
--     omega
--   | .double =>
--     simp only [UIntP.toNat_double] at hle ⊢
--     rw [UInt64.toNat_sub]
--     have := UInt64.toNat_lt a
--     omega
--   | .inf => rfl

-- theorem UIntP.add_sub_of_le {p} {a b : UIntP p} (h : b ≤ a) : b + (a - b) = a := by
--   apply UIntP.toNat_inj.mp
--   have hle : b.toNat ≤ a.toNat := UIntP.le_iff_toNat_le.mp h
--   match p with
--   | .single =>
--     simp only [UIntP.toNat_single] at hle ⊢
--     rw [UInt32.toNat_add, UInt32.toNat_sub]
--     have := UInt32.toNat_lt a
--     omega
--   | .double =>
--     simp only [UIntP.toNat_double] at hle ⊢
--     rw [UInt64.toNat_add, UInt64.toNat_sub]
--     have := UInt64.toNat_lt a
--     omega
--   | .inf =>
--     simp only [UIntP.toNat_inf] at hle ⊢
--     omega

-- @[inline]
-- def IdxP.inl {p} (m n : Nat) (a : IdxP m p) : IdxP (m + n) p :=
--   ⟨a.val, by have := a.isLt; omega⟩

-- @[inline]
-- def IdxP.inr {p} (m n : Nat) (b : IdxP n p) : IdxP (m + n) p :=
--   ⟨UIntP.ofNat p m + b.val, by
--     have hb := b.isLt
--     match p with
--     | .inf =>
--       simp only [UIntP.ofNat_inf, UIntP.toNat_inf] at *
--       omega
--     | .single =>
--       simp only [UIntP.ofNat_single, UIntP.toNat_single] at *
--       rcases lt_or_ge (m + n) (2 ^ 32) with hlt | hge
--       · rw [UInt32.toNat_add, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
--         omega
--       · exact lt_of_lt_of_le (UInt32.toNat_lt _) hge
--     | .double =>
--       simp only [UIntP.ofNat_double, UIntP.toNat_double] at *
--       rcases lt_or_ge (m + n) (2 ^ 64) with hlt | hge
--       · rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
--         omega
--       · exact lt_of_lt_of_le (UInt64.toNat_lt _) hge⟩

-- theorem IdxP.val_inl {p} (m n : Nat) (a : IdxP m p) : (IdxP.inl m n a).val = a.val := rfl

-- theorem IdxP.toNat_inr {p} (m n : Nat) (b : IdxP n p) (h : Precision.withinPrec p (m + n)) :
--     (IdxP.inr m n b).val.toNat = m + b.val.toNat := by
--   have hb := b.isLt
--   match p with
--   | .inf => rfl
--   | .single =>
--     have h32 : m + n < 2^32 := h
--     simp only [UIntP.ofNat_single, UIntP.toNat_single] at hb ⊢
--     rw [UInt32.toNat_add, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
--         Nat.mod_eq_of_lt (by omega)]
--   | .double =>
--     have h64 : m + n < 2^64 := h
--     simp only [UIntP.ofNat_double, UIntP.toNat_double] at hb ⊢
--     rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
--         Nat.mod_eq_of_lt (by omega)]

-- theorem IdxP.sub_inr {p} (m n : Nat) (b : IdxP n p) (h : Precision.withinPrec p (m + n)) :
--     (IdxP.inr m n b).val - UIntP.ofNat p m = b.val := by
--   have hb := b.isLt
--   have hn_pos : 0 < n := by omega
--   have hm_eq : (UIntP.ofNat p m).toNat = m :=
--     UIntP.toNat_ofNat_eq (by omega) h
--   apply UIntP.toNat_inj.mp
--   have hle : UIntP.ofNat p m ≤ (IdxP.inr m n b).val := by
--     rw [UIntP.le_iff_toNat_le, IdxP.toNat_inr m n b h, hm_eq]; omega
--   rw [UIntP.toNat_sub_of_le hle, IdxP.toNat_inr m n b h, hm_eq]
--   omega

-- @[inline]
-- def IdxP.sumEncode {p} (m n : Nat) : IdxP m p ⊕ IdxP n p → IdxP (m + n) p
--   | Sum.inl a => IdxP.inl m n a
--   | Sum.inr b => IdxP.inr m n b

-- @[inline]
-- def IdxP.sumDecode {p} (m n : Nat) (i : IdxP (m + n) p) : IdxP m p ⊕ IdxP n p :=
--   if h : i.val.toNat < m then
--     Sum.inl ⟨i.val, h⟩
--   else
--     Sum.inr ⟨(i.val - UIntP.ofNat p m) % UIntP.ofNat p n, by
--       have h1 := i.isLt
--       exact UIntP.toNat_mod_toUIntP_lt _ (by omega)⟩

-- theorem IdxP.sumDecode_encode {p} (m n : Nat) (h : Precision.withinPrec p (m + n))
--     (x : IdxP m p ⊕ IdxP n p) :
--     IdxP.sumDecode m n (IdxP.sumEncode m n x) = x := by
--   have hnfit : Precision.withinPrec p n := by
--     match p with
--     | .inf => trivial
--     | .single => exact lt_of_le_of_lt (Nat.le_add_left n m) h
--     | .double => exact lt_of_le_of_lt (Nat.le_add_left n m) h
--   cases x with
--   | inl a =>
--     have hga : (IdxP.inl m n a).val.toNat < m := a.isLt
--     change IdxP.sumDecode m n (IdxP.inl m n a) = Sum.inl a
--     rw [IdxP.sumDecode, dif_pos hga]
--     exact congrArg Sum.inl (IdxP.ext rfl)
--   | inr b =>
--     have hgb : ¬ (IdxP.inr m n b).val.toNat < m := by
--       rw [IdxP.toNat_inr m n b h]; omega
--     change IdxP.sumDecode m n (IdxP.inr m n b) = Sum.inr b
--     rw [IdxP.sumDecode, dif_neg hgb]
--     refine congrArg Sum.inr (IdxP.ext ?_)
--     change ((IdxP.inr m n b).val - UIntP.ofNat p m) % UIntP.ofNat p n = b.val
--     rw [IdxP.sub_inr m n b h, UIntP.mod_toUIntP_eq_self hnfit b.isLt]

-- theorem IdxP.sumEncode_decode {p} (m n : Nat) (h : Precision.withinPrec p (m + n))
--     (i : IdxP (m + n) p) :
--     IdxP.sumEncode m n (IdxP.sumDecode m n i) = i := by
--   have hnfit : Precision.withinPrec p n := by
--     match p with
--     | .inf => trivial
--     | .single => exact lt_of_le_of_lt (Nat.le_add_left n m) h
--     | .double => exact lt_of_le_of_lt (Nat.le_add_left n m) h
--   rw [IdxP.sumDecode]
--   by_cases hc : i.val.toNat < m
--   · rw [dif_pos hc]; apply IdxP.ext; rfl
--   · rw [dif_neg hc]
--     have h2 : m ≤ i.val.toNat := Nat.le_of_not_lt hc
--     have hm_eq : (UIntP.ofNat p m).toNat = m :=
--       UIntP.toNat_ofNat_eq (Nat.lt_of_le_of_lt h2 i.isLt) h
--     have hle : UIntP.ofNat p m ≤ i.val := by
--       rw [UIntP.le_iff_toNat_le, hm_eq]; exact h2
--     have hsublt : (i.val - UIntP.ofNat p m).toNat < n := by
--       rw [UIntP.toNat_sub_of_le hle, hm_eq]; have := i.isLt; omega
--     apply IdxP.ext
--     change UIntP.ofNat p m + ((i.val - UIntP.ofNat p m) % UIntP.ofNat p n) = i.val
--     rw [UIntP.mod_toUIntP_eq_self hnfit hsublt]
--     exact UIntP.add_sub_of_le hle

end NumLean
