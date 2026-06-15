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
theorem get_one [One α] {p : Profile} (i : Index p) : (1 : HTuple α p).get i = 1 := by
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
theorem get_mul [Mul α] {p : Profile} (x y : HTuple α p) (i : Index p) :
    (x * y).get i = x.get i * y.get i := by
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

/-- Pointwise semigroup structure on hierarchical tuples. -/
instance instSemigroup [Semigroup α] {p : Profile} : Semigroup (HTuple α p) where
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    apply ext
    intro i
    simp [mul_assoc]

/-- Pointwise commutative semigroup structure on hierarchical tuples. -/
instance instCommSemigroup [CommSemigroup α] {p : Profile} : CommSemigroup (HTuple α p) where
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    apply ext
    intro i
    simp [mul_assoc]
  mul_comm := by
    intro a b
    apply ext
    intro i
    simp [mul_comm]

/-- Pointwise multiplicative monoid structure on hierarchical tuples. -/
instance instMonoid [Monoid α] {p : Profile} : Monoid (HTuple α p) where
  one := (1 : HTuple α p)
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    apply ext
    intro i
    simp [mul_assoc]
  one_mul := by
    intro a
    apply ext
    intro i
    simp
  mul_one := by
    intro a
    apply ext
    intro i
    simp

/-- Pointwise commutative monoid structure on hierarchical tuples. -/
instance instCommMonoid [CommMonoid α] {p : Profile} : CommMonoid (HTuple α p) where
  one := (1 : HTuple α p)
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    apply ext
    intro i
    simp [mul_assoc]
  one_mul := by
    intro a
    apply ext
    intro i
    simp
  mul_one := by
    intro a
    apply ext
    intro i
    simp
  mul_comm := by
    intro a b
    apply ext
    intro i
    simp [mul_comm]

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

/-- Pointwise semiring structure on hierarchical tuples. -/
instance instSemiring [Semiring α] {p : Profile} : Semiring (HTuple α p) where
  zero := (0 : HTuple α p)
  one := (1 : HTuple α p)
  add := (· + ·)
  mul := (· * ·)
  nsmul := (· • ·)
  npow := fun n a => HTuple.ofFn fun i => (a.get i) ^ n
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
  mul_assoc := by
    intro a b c
    apply ext
    intro i
    simp [mul_assoc]
  one_mul := by
    intro a
    apply ext
    intro i
    simp
  mul_one := by
    intro a
    apply ext
    intro i
    simp
  left_distrib := by
    intro a b c
    apply ext
    intro i
    simp [left_distrib]
  right_distrib := by
    intro a b c
    apply ext
    intro i
    simp [right_distrib]
  zero_mul := by
    intro a
    apply ext
    intro i
    simp
  mul_zero := by
    intro a
    apply ext
    intro i
    simp
  natCast := fun n => HTuple.ofFn fun _ => n
  natCast_zero := by
    apply ext
    intro i
    simp
  natCast_succ := by
    intro n
    apply ext
    intro i
    simp [Nat.cast_succ]
  npow_zero := by
    intro a
    apply ext
    intro i
    simp
  npow_succ := by
    intro n a
    apply ext
    intro i
    simp [pow_succ]

/-- Pointwise commutative semiring structure on hierarchical tuples. -/
instance instCommSemiring [CommSemiring α] {p : Profile} : CommSemiring (HTuple α p) where
  mul_comm := by
    intro a b
    apply ext
    intro i
    simp [mul_comm]

/-- Scaling the right argument of an inner product scales the resulting inner product. -/
theorem inner_smul_right {I : Type u} {D : Type v} [AddCommGroup D] [Semiring I] [Module I D]
    {p : Profile} (idx : HTuple I p) (stride : HTuple D p) (n : Nat) :
    HTuple.inner idx (n • stride) = n • HTuple.inner idx stride := by
  induction p with
  | leaf =>
      cases idx with | leaf i =>
      cases stride with | leaf s =>
      simp [HTuple.inner, HTuple.innerWith]
      induction n with
      | zero => simp
      | succ n ih => simp [succ_nsmul, smul_add, ih]
  | prod p q hp hq =>
      cases idx with | prod idx₀ idx₁ =>
      cases stride with | prod stride₀ stride₁ =>
      calc
        HTuple.inner (HTuple.prod idx₀ idx₁) (n • HTuple.prod stride₀ stride₁)
            = HTuple.inner idx₀ (n • stride₀) + HTuple.inner idx₁ (n • stride₁) := by
              rfl
        _ = n • HTuple.inner idx₀ stride₀ + n • HTuple.inner idx₁ stride₁ := by
              rw [hp idx₀ stride₀, hq idx₁ stride₁]
        _ = n • HTuple.inner (HTuple.prod idx₀ idx₁) (HTuple.prod stride₀ stride₁) := by
              simp [HTuple.inner, HTuple.innerWith]

end HTuple

end NumLean
