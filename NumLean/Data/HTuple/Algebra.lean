import NumLean.Data.HTuple.Ops

namespace NumLean

namespace HTuple

variable {α : Type u}
variable {R : Type v}

/-- Extensionality for hierarchical tuples. -/
theorem ext {p : Profile} {x y : HTuple α p} (h : ∀ i : Index p, x.get i = y.get i) : x = y := by
  induction p with
  | leaf =>
      cases x with | leaf xv =>
      cases y with | leaf yv =>
      have := h Index.leaf
      simp at this
      simp [this]
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      have h₀ : x₀ = y₀ := hp fun i => h (.left i)
      have h₁ : x₁ = y₁ := hq fun i => h (.right i)
      simp [h₀, h₁]

@[simp]
theorem get_zero [Zero α] {p : Profile} (i : Index p) : (0 : HTuple α p).get i = 0 := by
  induction p with
  | leaf => cases i; rfl
  | prod p q hp hq => cases i <;> simp [hp, hq]

@[simp]
theorem get_add [Add α] {p : Profile} (x y : HTuple α p) (i : Index p) :
    (x + y).get i = x.get i + y.get i := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases y with | leaf y =>
      cases i
      rfl
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      cases i <;> simp [hp, hq]

@[simp]
theorem get_neg [Neg α] {p : Profile} (x : HTuple α p) (i : Index p) :
    (-x).get i = -x.get i := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases i
      rfl
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases i <;> simp [hp, hq]

@[simp]
theorem get_sub [Sub α] {p : Profile} (x y : HTuple α p) (i : Index p) :
    (x - y).get i = x.get i - y.get i := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases y with | leaf y =>
      cases i
      rfl
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases y with | prod y₀ y₁ =>
      cases i <;> simp [hp, hq]

@[simp]
theorem get_smul [SMul R α] {p : Profile} (r : R) (x : HTuple α p) (i : Index p) :
    (r • x).get i = r • x.get i := by
  induction p with
  | leaf =>
      cases x with | leaf x =>
      cases i
      rfl
  | prod p q hp hq =>
      cases x with | prod x₀ x₁ =>
      cases i with
      | left i => exact hp x₀ i
      | right i => exact hq x₁ i

/-- Pointwise additive commutative monoid structure on hierarchical tuples. -/
instance instAddCommMonoid [AddCommMonoid α] {p : Profile} : AddCommMonoid (HTuple α p) where
  zero := (0 : HTuple α p)
  add := (· + ·)
  nsmul := (· • ·)
  add_assoc := by
    intro a b c
    apply ext
    intro i
    simp [add_assoc]
  zero_add := by
    intro a
    apply ext
    intro i
    simp
  add_zero := by
    intro a
    apply ext
    intro i
    simp
  nsmul_zero := by
    intro a
    apply ext
    intro i
    simp
  nsmul_succ := by
    intro n a
    apply ext
    intro i
    simp [succ_nsmul]
  add_comm := by
    intro a b
    apply ext
    intro i
    simp [add_comm]

/-- Pointwise additive commutative group structure on hierarchical tuples. -/
instance instAddCommGroup [AddCommGroup α] {p : Profile} : AddCommGroup (HTuple α p) where
  zero := (0 : HTuple α p)
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := (· • ·)
  zsmul := (· • ·)
  add_assoc := by
    intro a b c
    apply ext
    intro i
    simp [add_assoc]
  zero_add := by
    intro a
    apply ext
    intro i
    simp
  add_zero := by
    intro a
    apply ext
    intro i
    simp
  nsmul_zero := by
    intro a
    apply ext
    intro i
    simp
  nsmul_succ := by
    intro n a
    apply ext
    intro i
    simp [succ_nsmul]
  neg_add_cancel := by
    intro a
    apply ext
    intro i
    simp
  sub_eq_add_neg := by
    intro a b
    apply ext
    intro i
    simp [sub_eq_add_neg]
  zsmul_zero' := by
    intro a
    apply ext
    intro i
    simp
  zsmul_succ' := by
    intro n a
    apply ext
    intro i
    simpa [add_comm] using SubNegMonoid.zsmul_succ' n (a.get i)
  zsmul_neg' := by
    intro n a
    apply ext
    intro i
    simpa using SubNegMonoid.zsmul_neg' n (a.get i)
  add_comm := by
    intro a b
    apply ext
    intro i
    simp [add_comm]

/-- Pointwise module structure on hierarchical tuples. -/
instance instModule [Semiring R] [AddCommMonoid α] [Module R α] {p : Profile} :
    Module R (HTuple α p) where
  smul := (· • ·)
  one_smul := by
    intro a
    apply ext
    intro i
    simp
  mul_smul := by
    intro r s a
    apply ext
    intro i
    simp [mul_smul]
  smul_zero := by
    intro r
    apply ext
    intro i
    simp
  smul_add := by
    intro r a b
    apply ext
    intro i
    simp [smul_add]
  add_smul := by
    intro r s a
    apply ext
    intro i
    simp [add_smul]
  zero_smul := by
    intro a
    apply ext
    intro i
    simp

end HTuple

end NumLean
