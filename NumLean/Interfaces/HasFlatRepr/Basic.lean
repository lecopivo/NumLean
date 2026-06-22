import NumLean.Interfaces.VectorType.Basic
import NumLean.Tactic.TBounds

namespace NumLean

/-- Type `X` has a flat scalar representation stored in vector type `Ks`.

It combines the specification-level vector equivalence with operations for reading and writing
packed scalar storage. -/
class HasFlatRepr (X : Type u) (Ks : Nat → Type v) (nX : outParam Nat)
    {K : outParam (Type w)} [VectorType Ks K] where

  /-- Specification-level conversion to a fixed-size scalar vector. -/
  toVector : X → Vector K nX
  /-- Specification-level conversion from a fixed-size scalar vector. -/
  fromVector : Vector K nX → X

  left_inv : Function.LeftInverse fromVector toVector
  right_inv : Function.RightInverse fromVector toVector

  /-- Scalar coordinate projection of an `X`. -/
  getComp (x : X) (i : Nat) (h : i < nX) : K
  getComp_spec (x : X) (i : Nat) (h : i < nX) :
    getComp x i h = (toVector x)[i]

  setComp (x : X) (i : Nat) (xi : K) (h : i < nX) : X
  setComp_spec (x : X) (i : Nat) (xi : K) (h : i < nX) :
    setComp x i xi h = fromVector ((toVector x).set i xi h)

  /-- Read `X` from `ks` starting at scalar offset `off`. -/
  get {n : Nat} (ks : Ks n) (off : Nat) (h : off + nX ≤ n) : X
  getComp_get_eq_vector_get {n : Nat} (ks : Ks n) (off i : Nat)
      (hoff : off + nX ≤ n) (hi : i < nX) :
    getComp (get ks off hoff) i hi = VectorType.get ks (off + i) (by grind)

  /-- Write `x` into `ks` starting at scalar offset `off`. -/
  set {n : Nat} (ks : Ks n) (off : Nat) (x : X) (h : off + nX ≤ n) : Ks n
  vector_get_set_eq {n : Nat} (ks : Ks n) (off i : Nat) (x : X) (hoff : off + nX ≤ n)
      (hi : off ≤ i ∧ i < off + nX) :
    VectorType.get (set ks off x hoff) i (by grind) = getComp x (i - off) (by grind)
  vector_get_set_ne {n : Nat} (ks : Ks n) (off i : Nat) (x : X) (hoff : off + nX ≤ n)
      (hi : i < off ∨ off + nX ≤ i) (hi' : i < n) :
    VectorType.get (set ks off x hoff) i (by grind) = VectorType.get ks i hi'

  /-- Append `x` to the end of `ks` as one contiguous `X` block. -/
  push {n : Nat} (ks : Ks n) (x : X) : Ks (n + nX)
  vector_get_push_lt {n : Nat} (ks : Ks n) (x : X) (i : Nat) (hi : i < n) :
    VectorType.get (push ks x) i (by grind) = VectorType.get ks i hi
  vector_get_push_eq {n : Nat} (ks : Ks n) (x : X) (i : Nat) (hi : i < nX) :
    VectorType.get (push ks x) (n + i) (by grind) = getComp x i hi

  /-- Convert one `X` value to its flat scalar storage. -/
  toFlatVector : X → Ks nX
  get_toFlatVector_eq_getComp (x : X) (i : Nat) (h : i < nX) :
    VectorType.get (toFlatVector x) i h = getComp x i h

  replicate (n : Nat) (x : X) : Ks (n * nX)
  get_replicate (n : Nat) (x : X) (i j : Nat) (hi : i < n) (hj : j < nX) :
    VectorType.get (replicate n x) (i * nX + j) (by tbounds) = getComp x j hj

/-- The default flat vector representation for `X`. -/
class HasDefaultFlatRepr (X : Type u) (Ks : outParam (Nat → Type v)) (nX : outParam Nat)
    {K : outParam (Type w)} [VectorType Ks K]
    extends HasFlatRepr X Ks nX

namespace HasFlatRepr

variable {X : Type u} {Ks : Nat → Type v} {K : Type w} {nX : Nat}
  [VectorType Ks K] [HasFlatRepr X Ks nX]

attribute [simp]
  vector_get_set_eq
  vector_get_set_ne
  vector_get_push_lt
  vector_get_push_eq
  get_toFlatVector_eq_getComp
  get_replicate

@[simp]
theorem fromVector_toVector (x : X) :
    HasFlatRepr.fromVector (Ks := Ks) (HasFlatRepr.toVector (Ks := Ks) x) = x :=
  HasFlatRepr.left_inv x

@[simp]
theorem toVector_fromVector (x : Vector K nX) :
    HasFlatRepr.toVector (Ks := Ks) (X := X) (HasFlatRepr.fromVector (Ks := Ks) x) = x :=
  HasFlatRepr.right_inv x

theorem ext (x y : X)
    (h : ∀ (i : Nat), (hi : i < nX) →
      HasFlatRepr.getComp (Ks := Ks) x i hi = HasFlatRepr.getComp (Ks := Ks) y i hi) : x = y := by
  apply (HasFlatRepr.left_inv (Ks := Ks)).injective
  simp only [HasFlatRepr.getComp_spec] at h
  ext i hi
  exact h i hi

theorem vector_ext {n : Nat} (xs ys : Ks (n * nX))
    (h : ∀ (i j : Nat), (hi : i * nX + nX ≤ n * nX) → (hj : j < nX) →
      VectorType.get xs (i * nX + j) (by tbounds) =
        VectorType.get ys (i * nX + j) (by tbounds)) : xs = ys := by
  apply VectorType.ext
  intro k hk
  by_cases hnX : nX = 0
  · simp [hnX] at hk
  · have hnXpos : 0 < nX := Nat.pos_of_ne_zero hnX
    have hi : k / nX < n := by
      rw [Nat.div_lt_iff_lt_mul hnXpos]
      simpa [Nat.mul_comm] using hk
    have hj : k % nX < nX := Nat.mod_lt k hnXpos
    have hblock : (k / nX) * nX + nX ≤ n * nX := by
      tbounds
    simpa [Nat.div_add_mod, Nat.mul_comm] using h (k / nX) (k % nX) hblock hj

@[simp]
theorem getComp_setComp_eq (x : X) (i : Nat) (xi : K) (h : i < nX) :
    HasFlatRepr.getComp (Ks := Ks) (HasFlatRepr.setComp (Ks := Ks) x i xi h) i h = xi := by
  rw [HasFlatRepr.getComp_spec, HasFlatRepr.setComp_spec, HasFlatRepr.toVector_fromVector]
  exact Vector.getElem_set_self h

@[simp]
theorem getComp_setComp_neq (x : X) (i j : Nat) (xi : K) (hi : i < nX) (hj : j < nX)
    (h : i ≠ j) :
    HasFlatRepr.getComp (Ks := Ks) (HasFlatRepr.setComp (Ks := Ks) x i xi hi) j hj =
      HasFlatRepr.getComp (Ks := Ks) x j hj := by
  rw [HasFlatRepr.getComp_spec, HasFlatRepr.setComp_spec, HasFlatRepr.toVector_fromVector,
    HasFlatRepr.getComp_spec]
  rw [Vector.getElem_set hi hj]
  simp [h]

instance {R : Type u} {Rs : Nat → Type v} [VectorType Rs R] : HasFlatRepr R Rs 1 where
  toVector x := #v[x]
  fromVector x := x[0]
  left_inv := by intro _; simp
  right_inv := by intro _; simp; ext <;> grind
  getComp x _ _ := x
  getComp_spec := by intros; simp
  setComp _ _ x _ := x
  setComp_spec := by intros; simp; grind
  get xs i h := VectorType.get xs i h
  getComp_get_eq_vector_get := by
    intros _ _ _ i; intros
    have h : i = 0 := by grind
    simp [h]
  set xs off x h := VectorType.set xs off x (by grind)
  vector_get_set_eq := by
    intro n xs off i x hoff hi
    have hioff : i = off := by grind
    subst hioff
    rw [VectorType.get_spec, VectorType.set_spec]
    simp
  vector_get_set_ne := by
    intro n xs off i x hoff hi hi'
    have hne : off ≠ i := by
      intro h
      omega
    rw [VectorType.get_spec, VectorType.set_spec, VectorType.get_spec]
    rw [Vector.getElem_set]
    simp [hne]
  push xs x := VectorType.push xs x
  vector_get_push_lt := by
    intro n xs x i hi
    rw [VectorType.get_spec, VectorType.push_spec, VectorType.get_spec]
    exact Vector.getElem_push_lt hi
  vector_get_push_eq := by
    intro n xs x i hi
    have hi0 : i = 0 := by grind
    subst hi0
    simp only [Nat.add_zero, VectorType.get_push_eq]
  toFlatVector x := VectorType.fromVector #v[x]
  get_toFlatVector_eq_getComp := by
    intro x i h
    have hi0 : i = 0 := by grind
    subst hi0
    simp [VectorType.get_spec]
  replicate n x := VectorType.replicate (As := Rs) (n * 1) x
  get_replicate := by
    intros
    simp only [Nat.mul_one, VectorType.get_replicate]

@[simp]
theorem get_set_eq {n : Nat} (ks : Ks n) (off : Nat) (x : X) (hoff : off + nX ≤ n) :
    get (set ks off x hoff) off (by grind) = x := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro i hi
  rw [getComp_get_eq_vector_get, vector_get_set_eq]
  all_goals grind

@[simp]
theorem get_set_ne {n : Nat} (ks : Ks n) (off off' : Nat) (x : X) (hoff : off + nX ≤ n)
    (hoff' : off' + nX ≤ off ∨ off + nX ≤ off') (hoff'' : off' + nX ≤ n) :
    get (X := X) (set ks off x hoff) off' (by grind) = get ks off' hoff'' := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro i hi
  simp only [getComp_get_eq_vector_get]
  rw [vector_get_set_ne]
  all_goals grind

@[simp]
theorem get_push_eq {n : Nat} (ks : Ks n) (x : X) :
    get (X := X) (push ks x) n (by grind) = x := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro i hi
  rw [getComp_get_eq_vector_get, vector_get_push_eq]

@[simp]
theorem get_push_lt {n : Nat} (ks : Ks n) (off : Nat) (x : X) (hoff : off + nX ≤ n) :
    get (X := X) (push ks x) off (by grind) = get (X := X) ks off hoff := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro i hi
  rw [getComp_get_eq_vector_get, getComp_get_eq_vector_get]
  have hlt : off + i < n := by
    have := hoff
    grind
  rw [vector_get_push_lt (ks := ks) (x := x) (i := off + i) hlt]

@[simp]
theorem get_toFlatVector (x : X) :
    get (toFlatVector (Ks := Ks) x) 0 (by simp) = x := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro i hi
  rw [getComp_get_eq_vector_get]
  simp

@[simp]
theorem get_replicate_eq (n : Nat) (x : X) (i : Nat) (hi : i < n) :
    get (X := X) (replicate (Ks := Ks) n x) (i * nX) (by tbounds) = x := by
  apply HasFlatRepr.ext (Ks := Ks)
  intro j hj
  rw [getComp_get_eq_vector_get]
  exact get_replicate (X := X) (Ks := Ks) (K := K) n x i j hi hj

end HasFlatRepr

end NumLean
