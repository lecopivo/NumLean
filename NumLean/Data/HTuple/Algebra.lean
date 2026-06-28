module

public import NumLean.Data.HTuple.Ops

@[expose] public section

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
  mul_assoc := by
    intro a b c
    apply ext
    intro i
    simp [mul_assoc]

/-- Pointwise commutative semigroup structure on hierarchical tuples. -/
instance instCommSemigroup [CommSemigroup α] {p : Profile} : CommSemigroup (HTuple α p) where
  mul_comm := by
    intro a b
    apply ext
    intro i
    simp [mul_comm]

/-- Pointwise natural powers on hierarchical tuples. -/
def npow [Pow α Nat] {p : Profile} (n : Nat) (a : HTuple α p) : HTuple α p :=
  a.map (fun x => x ^ n)

/-- Pointwise multiplicative monoid structure on hierarchical tuples. -/
instance instMonoid [Monoid α] {p : Profile} : Monoid (HTuple α p) where
  npow := HTuple.npow
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
  npow_zero := by
    intro a
    apply ext
    intro i
    simp [HTuple.npow]
  npow_succ := by
    intro n a
    apply ext
    intro i
    simp [HTuple.npow, pow_succ]

/-- Pointwise commutative monoid structure on hierarchical tuples. -/
instance instCommMonoid [CommMonoid α] {p : Profile} : CommMonoid (HTuple α p) where
  mul_comm := by
    intro a b
    apply ext
    intro i
    simp [mul_comm]

/-- Pointwise additive commutative monoid structure on hierarchical tuples. -/
instance instAddCommMonoid [AddCommMonoid α] {p : Profile} : AddCommMonoid (HTuple α p) where
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
  neg := Neg.neg
  sub := Sub.sub
  nsmul := (· • ·)
  zsmul := (· • ·)
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

instance instIsScalarTower [SMul R S] [SMul S α] [SMul R α] [IsScalarTower R S α]
    {p : Profile} : IsScalarTower R S (HTuple α p) where
  smul_assoc r s a := by
    apply ext
    intro i
    simp [smul_assoc]

/-- Pointwise semiring structure on hierarchical tuples. -/
instance instSemiring [Semiring α] {p : Profile} : Semiring (HTuple α p) where
  zero := (0 : HTuple α p)
  one := (1 : HTuple α p)
  add := (· + ·)
  mul := (· * ·)
  nsmul := (· • ·)
  npow := HTuple.npow
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
    simp [HTuple.npow]
  npow_succ := by
    intro n a
    apply ext
    intro i
    simp [HTuple.npow, pow_succ]

@[simp]
theorem natCast_eq_toScalar (n : Nat) : (n.cast : HTuple ℕ .leaf).toScalar = n := by rfl

@[simp, norm_cast]
theorem coe_natCast_leaf (n : Nat) : ((n : HTuple Nat .leaf) : Nat) = n := rfl

@[simp]
theorem natCast_leaf (n : Nat) : (n : HTuple Nat .leaf) = .leaf n := rfl

/-- Pointwise commutative semiring structure on hierarchical tuples. -/
instance instCommSemiring [CommSemiring α] {p : Profile} : CommSemiring (HTuple α p) where
  mul_comm := by
    intro a b
    apply ext
    intro i
    simp [mul_comm]

/-- Refined module structure: a coarse scalar tuple acts on every leaf of each refined subtree. -/
instance instModuleRefined {α : Type u} {β : Type v} [Semiring α] [AddCommMonoid β] [Module α β]
    {p q : Profile} [h : q.Refines p] : Module (HTuple α p) (HTuple β q) where
  one_smul := by
    intro b
    induction h with
    | leaf q =>
        apply ext
        intro i
        simp
    | prod h₁ h₂ ih₁ ih₂ =>
        cases b with | prod b₁ b₂ =>
        simp [ih₁, ih₂]
  mul_smul := by
    intro x y b
    induction h with
    | leaf q =>
        cases x with | leaf x =>
        cases y with | leaf y =>
        apply ext
        intro i
        simp [mul_smul]
    | prod h₁ h₂ ih₁ ih₂ =>
        cases x with | prod x₁ x₂ =>
        cases y with | prod y₁ y₂ =>
        cases b with | prod b₁ b₂ =>
        simp [ih₁, ih₂]
  smul_zero := by
    intro x
    induction h with
    | leaf q =>
        cases x with | leaf x =>
        apply ext
        intro i
        simp
    | prod h₁ h₂ ih₁ ih₂ =>
        cases x with | prod x₁ x₂ =>
        simp [ih₁, ih₂]
  smul_add := by
    intro x b c
    induction h with
    | leaf q =>
        cases x with | leaf x =>
        apply ext
        intro i
        simp [smul_add]
    | prod h₁ h₂ ih₁ ih₂ =>
        cases x with | prod x₁ x₂ =>
        cases b with | prod b₁ b₂ =>
        cases c with | prod c₁ c₂ =>
        simp [ih₁, ih₂]
  add_smul := by
    intro x y b
    induction h with
    | leaf q =>
        cases x with | leaf x =>
        cases y with | leaf y =>
        apply ext
        intro i
        simp [add_smul]
    | prod h₁ h₂ ih₁ ih₂ =>
        cases x with | prod x₁ x₂ =>
        cases y with | prod y₁ y₂ =>
        cases b with | prod b₁ b₂ =>
        simp [ih₁, ih₂]
  zero_smul := by
    intro b
    induction h with
    | leaf q =>
        apply ext
        intro i
        simp
    | prod h₁ h₂ ih₁ ih₂ =>
        cases b with | prod b₁ b₂ =>
        simp [ih₁, ih₂]

/-- Scaling the right argument of an inner product scales the resulting inner product. -/
theorem inner_smul_right {R : Type u} {S : Type v} {D : Type w}
    [Semiring R] [Monoid S] [AddCommMonoid D] [Module R D] [DistribSMul S D]
    [SMulCommClass R S D]
    {p : Profile} (idx : HTuple R p) (stride : HTuple D p) (s : S) :
    HTuple.inner idx (s • stride) = s • HTuple.inner idx stride := by
  induction p with
  | leaf =>
      cases idx with | leaf i =>
      cases stride with | leaf stride =>
      simp [HTuple.inner, HTuple.innerWith, smul_comm]
  | prod p q hp hq =>
      cases idx with | prod idx₀ idx₁ =>
      cases stride with | prod stride₀ stride₁ =>
      calc
        HTuple.inner (HTuple.prod idx₀ idx₁) (s • HTuple.prod stride₀ stride₁)
            = HTuple.inner idx₀ (s • stride₀) + HTuple.inner idx₁ (s • stride₁) := by
              rfl
        _ = s • HTuple.inner idx₀ stride₀ + s • HTuple.inner idx₁ stride₁ := by
              rw [hp idx₀ stride₀, hq idx₁ stride₁]
        _ = s • HTuple.inner (HTuple.prod idx₀ idx₁) (HTuple.prod stride₀ stride₁) := by
              simp [HTuple.inner, HTuple.innerWith]

@[simp]
theorem inner_zero_left {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : Profile} (stride : HTuple D p) :
    HTuple.inner (0 : HTuple R p) stride = 0 := by
  induction p with
  | leaf =>
      cases stride with | leaf s =>
      simp [HTuple.inner, HTuple.innerWith]
  | prod p q hp hq =>
      cases stride with | prod stride₀ stride₁ =>
      change HTuple.inner (0 : HTuple R p) stride₀ + HTuple.inner (0 : HTuple R q) stride₁ = 0
      rw [hp stride₀, hq stride₁, zero_add]

@[simp]
theorem inner_zero_right {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : Profile} (idx : HTuple R p) :
    HTuple.inner idx (0 : HTuple D p) = 0 := by
  induction p with
  | leaf =>
      cases idx with | leaf idx => simp [HTuple.inner, HTuple.innerWith]
  | prod p q hp hq =>
      cases idx with | prod idx₀ idx₁ =>
      change HTuple.inner idx₀ (0 : HTuple D p) + HTuple.inner idx₁ (0 : HTuple D q) = 0
      rw [hp idx₀, hq idx₁, zero_add]

theorem inner_add_left {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : Profile} (idx idx' : HTuple R p) (stride : HTuple D p) :
    HTuple.inner (idx + idx') stride = HTuple.inner idx stride + HTuple.inner idx' stride := by
  induction p with
  | leaf =>
      cases idx with | leaf i =>
      cases idx' with | leaf j =>
      cases stride with | leaf s =>
      simpa [HTuple.inner, HTuple.innerWith] using add_smul i j s
  | prod p q hp hq =>
      cases idx with | prod idx₀ idx₁ =>
      cases idx' with | prod idx'₀ idx'₁ =>
      cases stride with | prod stride₀ stride₁ =>
      change HTuple.inner (idx₀ + idx'₀) stride₀ + HTuple.inner (idx₁ + idx'₁) stride₁ =
        (HTuple.inner idx₀ stride₀ + HTuple.inner idx₁ stride₁) +
          (HTuple.inner idx'₀ stride₀ + HTuple.inner idx'₁ stride₁)
      rw [hp idx₀ idx'₀ stride₀, hq idx₁ idx'₁ stride₁]
      ac_rfl

theorem inner_smul_left {R : Type u} {S : Type v} {D : Type w}
    [Semiring R] [Semiring S] [AddCommMonoid D]
    [Module R S] [Module S D] [Module R D] [IsScalarTower R S D]
    {p : Profile} (n : R) (idx : HTuple S p) (stride : HTuple D p) :
    HTuple.inner (n • idx) stride = n • HTuple.inner idx stride := by
  induction p with
  | leaf =>
      cases idx with | leaf i =>
      cases stride with | leaf s =>
      simp [HTuple.inner, HTuple.innerWith, smul_assoc]
  | prod p q hp hq =>
      cases idx with | prod idx₀ idx₁ =>
      cases stride with | prod stride₀ stride₁ =>
      change HTuple.inner (n • idx₀) stride₀ + HTuple.inner (n • idx₁) stride₁ =
        n • (HTuple.inner idx₀ stride₀ + HTuple.inner idx₁ stride₁)
      rw [hp idx₀ stride₀, hq idx₁ stride₁, smul_add]

theorem inner_map_inner {R : Type u} {S : Type v} {D : Type w}
    [Semiring R] [Semiring S] [AddCommMonoid D]
    [Module R S] [Module S D] [Module R D] [IsScalarTower R S D]
    {p q : Profile} (idx : HTuple R q) (strides : HTuple (HTuple S p) q)
    (stride : HTuple D p) :
    HTuple.inner idx (HTuple.map (fun coord => HTuple.inner coord stride) strides) =
      HTuple.inner (HTuple.inner idx strides) stride := by
  induction q with
  | leaf =>
      cases idx with | leaf i =>
      cases strides with | leaf coord =>
      simpa [HTuple.inner, HTuple.innerWith] using (inner_smul_left i coord stride).symm
  | prod q₀ q₁ h₀ h₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases strides with | prod strides₀ strides₁ =>
      change HTuple.inner idx₀ (HTuple.map (fun coord => HTuple.inner coord stride) strides₀) +
          HTuple.inner idx₁ (HTuple.map (fun coord => HTuple.inner coord stride) strides₁) =
        HTuple.inner (HTuple.inner idx₀ strides₀ + HTuple.inner idx₁ strides₁) stride
      rw [h₀ idx₀ strides₀, h₁ idx₁ strides₁]
      exact (inner_add_left (HTuple.inner idx₀ strides₀) (HTuple.inner idx₁ strides₁) stride).symm

theorem inner_map_prod_left {R : Type u} [Semiring R] {p q r : Profile}
    (idx : HTuple R r) (strides : HTuple (HTuple R p) r) :
    HTuple.inner idx (HTuple.map (fun x => HTuple.prod x (0 : HTuple R q)) strides) =
      HTuple.prod (HTuple.inner idx strides) 0 := by
  induction r with
  | leaf =>
      cases idx with | leaf i =>
      cases strides with | leaf stride =>
      change i • HTuple.prod stride (0 : HTuple R q) = HTuple.prod (i • stride) 0
      simp [HTuple.smul_prod]
  | prod r₀ r₁ h₀ h₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases strides with | prod strides₀ strides₁ =>
      change HTuple.inner idx₀ (HTuple.map (fun x => HTuple.prod x (0 : HTuple R q)) strides₀) +
          HTuple.inner idx₁ (HTuple.map (fun x => HTuple.prod x (0 : HTuple R q)) strides₁) =
        HTuple.prod (HTuple.inner idx₀ strides₀ + HTuple.inner idx₁ strides₁) 0
      rw [h₀ idx₀ strides₀, h₁ idx₁ strides₁]
      simp

theorem inner_map_prod_right {R : Type u} [Semiring R] {p q r : Profile}
    (idx : HTuple R r) (strides : HTuple (HTuple R q) r) :
    HTuple.inner idx (HTuple.map (fun x => HTuple.prod (0 : HTuple R p) x) strides) =
      HTuple.prod 0 (HTuple.inner idx strides) := by
  induction r with
  | leaf =>
      cases idx with | leaf i =>
      cases strides with | leaf stride =>
      change i • HTuple.prod (0 : HTuple R p) stride = HTuple.prod 0 (i • stride)
      simp [HTuple.smul_prod]
  | prod r₀ r₁ h₀ h₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases strides with | prod strides₀ strides₁ =>
      change HTuple.inner idx₀ (HTuple.map (fun x => HTuple.prod (0 : HTuple R p) x) strides₀) +
          HTuple.inner idx₁ (HTuple.map (fun x => HTuple.prod (0 : HTuple R p) x) strides₁) =
        HTuple.prod 0 (HTuple.inner idx₀ strides₀ + HTuple.inner idx₁ strides₁)
      rw [h₀ idx₀ strides₀, h₁ idx₁ strides₁]
      simp

theorem inner_map_prod_fst {R : Type u} {D : Type v} [Zero D] [Add D] [SMul R D]
    {p q r : Profile} (idx : HTuple R p)
    (strides : HTuple (HTuple D (.prod q r)) p) :
    HTuple.inner idx (HTuple.map HTuple.fst strides) = (HTuple.inner idx strides).fst := by
  induction p with
  | leaf =>
      cases idx with | leaf idx =>
      cases strides with | leaf stride =>
      cases stride with | prod stride₀ stride₁ =>
      rfl
  | prod p₀ p₁ hp₀ hp₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases strides with | prod strides₀ strides₁ =>
      change HTuple.inner idx₀ (HTuple.map HTuple.fst strides₀) +
          HTuple.inner idx₁ (HTuple.map HTuple.fst strides₁) =
        (HTuple.inner idx₀ strides₀ + HTuple.inner idx₁ strides₁).fst
      rw [hp₀ idx₀ strides₀, hp₁ idx₁ strides₁]
      cases HTuple.inner idx₀ strides₀ with | prod x₀ y₀ =>
      cases HTuple.inner idx₁ strides₁ with | prod x₁ y₁ =>
      rfl

theorem inner_map_prod_snd {R : Type u} {D : Type v} [Zero D] [Add D] [SMul R D]
    {p q r : Profile} (idx : HTuple R p)
    (strides : HTuple (HTuple D (.prod q r)) p) :
    HTuple.inner idx (HTuple.map HTuple.snd strides) = (HTuple.inner idx strides).snd := by
  induction p with
  | leaf =>
      cases idx with | leaf idx =>
      cases strides with | leaf stride =>
      cases stride with | prod stride₀ stride₁ =>
      rfl
  | prod p₀ p₁ hp₀ hp₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases strides with | prod strides₀ strides₁ =>
      change HTuple.inner idx₀ (HTuple.map HTuple.snd strides₀) +
          HTuple.inner idx₁ (HTuple.map HTuple.snd strides₁) =
        (HTuple.inner idx₀ strides₀ + HTuple.inner idx₁ strides₁).snd
      rw [hp₀ idx₀ strides₀, hp₁ idx₁ strides₁]
      cases HTuple.inner idx₀ strides₀ with | prod x₀ y₀ =>
      cases HTuple.inner idx₁ strides₁ with | prod x₁ y₁ =>
      rfl

theorem inner_map₂_prod {R : Type u} {D : Type v} [Zero D] [Add D] [SMul R D]
    {p q r : Profile} (idx : HTuple R p)
    (strides₀ : HTuple (HTuple D q) p) (strides₁ : HTuple (HTuple D r) p) :
    HTuple.inner idx (HTuple.map₂ (fun x y => HTuple.prod x y) strides₀ strides₁) =
      HTuple.prod (HTuple.inner idx strides₀) (HTuple.inner idx strides₁) := by
  induction p with
  | leaf =>
      cases idx with | leaf idx =>
      cases strides₀ with | leaf stride₀ =>
      cases strides₁ with | leaf stride₁ =>
      rfl
  | prod p₀ p₁ hp₀ hp₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases strides₀ with | prod strides₀₀ strides₀₁ =>
      cases strides₁ with | prod strides₁₀ strides₁₁ =>
      change HTuple.inner idx₀ (HTuple.map₂ (fun x y => HTuple.prod x y) strides₀₀ strides₁₀) +
          HTuple.inner idx₁ (HTuple.map₂ (fun x y => HTuple.prod x y) strides₀₁ strides₁₁) =
        HTuple.prod (HTuple.inner idx₀ strides₀₀ + HTuple.inner idx₁ strides₀₁)
          (HTuple.inner idx₀ strides₁₀ + HTuple.inner idx₁ strides₁₁)
      rw [hp₀ idx₀ strides₀₀ strides₁₀, hp₁ idx₁ strides₀₁ strides₁₁]
      rfl

theorem inner_map_leaf {R : Type u} {D : Type v} [Zero D] [Add D] [SMul R D]
    {p : Profile} (idx : HTuple R p) (stride : HTuple D p) :
    HTuple.inner idx (HTuple.map HTuple.leaf stride) = HTuple.leaf (HTuple.inner idx stride) := by
  induction p with
  | leaf =>
      cases idx with | leaf idx =>
      cases stride with | leaf stride =>
      rfl
  | prod p₀ p₁ hp₀ hp₁ =>
      cases idx with | prod idx₀ idx₁ =>
      cases stride with | prod stride₀ stride₁ =>
      change HTuple.inner idx₀ (HTuple.map HTuple.leaf stride₀) +
          HTuple.inner idx₁ (HTuple.map HTuple.leaf stride₁) =
        HTuple.leaf (HTuple.inner idx₀ stride₀ + HTuple.inner idx₁ stride₁)
      rw [hp₀ idx₀ stride₀, hp₁ idx₁ stride₁]
      rfl

@[simp]
theorem inner_basisTuple {R : Type u} [Semiring R] {p : Profile} (idx : HTuple R p) :
    HTuple.inner idx (HTuple.basisTuple p) = idx := by
  induction p with
  | leaf =>
      cases idx with | leaf i =>
      change i • (HTuple.leaf 1 : HTuple R .leaf) = HTuple.leaf i
      simp
  | prod p q hp hq =>
      cases idx with | prod idx₀ idx₁ =>
      change HTuple.inner idx₀
            (HTuple.map (fun x => HTuple.prod x (0 : HTuple R q)) (HTuple.basisTuple p)) +
          HTuple.inner idx₁
            (HTuple.map (fun x => HTuple.prod (0 : HTuple R p) x) (HTuple.basisTuple q)) =
        HTuple.prod idx₀ idx₁
      have hleft : HTuple.inner idx₀
            (HTuple.map (fun x => HTuple.prod x (0 : HTuple R q)) (HTuple.basisTuple p)) =
          HTuple.prod idx₀ 0 := by
        have h := inner_map_prod_left (q := q) idx₀ (HTuple.basisTuple p)
        rw [hp idx₀] at h
        exact h
      have hright : HTuple.inner idx₁
            (HTuple.map (fun x => HTuple.prod (0 : HTuple R p) x) (HTuple.basisTuple q)) =
          HTuple.prod 0 idx₁ := by
        have h := inner_map_prod_right (p := p) idx₁ (HTuple.basisTuple q)
        rw [hq idx₁] at h
        exact h
      rw [hleft, hright]
      simp

@[simp]
theorem map_inner_basisTuple {R : Type u} {D : Type v} [Semiring R] [AddCommMonoid D] [Module R D]
    {p : Profile} (stride : HTuple D p) :
    HTuple.map (fun coord : HTuple R p => HTuple.inner coord stride) (HTuple.basisTuple p) = stride := by
  induction p with
  | leaf =>
      cases stride with | leaf s =>
      simp [HTuple.inner, HTuple.innerWith, HTuple.basisTuple]
  | prod p q hp hq =>
      cases stride with | prod stride₀ stride₁ =>
      simp [HTuple.basisTuple]
      constructor
      · apply HTuple.ext
        intro i
        have hget : HTuple.inner ((HTuple.basisTuple (α := R) p).get i) stride₀ = stride₀.get i := by
          simpa using congrArg (fun x => x.get i) (hp stride₀)
        simp only [get_map]
        change HTuple.inner ((HTuple.basisTuple (α := R) p).get i) stride₀ +
            HTuple.inner (0 : HTuple R q) stride₁ = stride₀.get i
        rw [hget, inner_zero_left, add_zero]
      · apply HTuple.ext
        intro i
        have hget : HTuple.inner ((HTuple.basisTuple (α := R) q).get i) stride₁ = stride₁.get i := by
          simpa using congrArg (fun x => x.get i) (hq stride₁)
        simp only [get_map]
        change HTuple.inner (0 : HTuple R p) stride₀ +
            HTuple.inner ((HTuple.basisTuple (α := R) q).get i) stride₁ = stride₁.get i
        rw [hget, inner_zero_left, zero_add]

/-- Regression test: the inherited integer scalar action on `HTuple` is definitionally the
pointwise action supplied by its additive group structure. -/
example {α : Type u} [AddCommGroup α] {p : Profile} :
    (inferInstance : SMul Int (HTuple α p)) = SubNegMonoid.toZSMul := rfl

/-- Regression test: powers on `HTuple` use the shared pointwise `map` implementation. -/
example {α : Type u} [Monoid α] {p : Profile} :
    ((fun n (a : HTuple α p) => a ^ n) : Nat → HTuple α p → HTuple α p) = HTuple.npow := rfl

end HTuple

end NumLean
