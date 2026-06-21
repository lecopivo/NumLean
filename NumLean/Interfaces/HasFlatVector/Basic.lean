import NumLean.Interfaces.VectorType.Basic
import NumLean.Interfaces.FlatRepr.Basic

namespace NumLean

open FlatRepr in
/-- Type `X` can be stored in a vector `Ks n` whose scalar element type is `K`.

Please note that `Ks` is not an `outParam` this is provided by `HasDefaultFlatVector`. -/
class HasFlatVector (X : Type u) (Ks : Nat → Type v) (nX : outParam Nat)
    {K : outParam (Type w)} [VectorType Ks K]
    extends FlatRepr X K nX where

  /-- Read `X` from `ks` starting at scalar offset `off`. -/
  get {n : Nat} (ks : Ks n) (off : Nat) (h : off + nX ≤ n) : X
  getComp_get_eq_vector_get {n : Nat} (ks : Ks n) (off i : Nat)
    (hoff : off + nX ≤ n) (hi : i < nX) :
    getComp (get ks off hoff) i hi
    =
    VectorType.get ks (off + i) (by grind)

  -- /-- Read `X` from `ks` starting at `USize` scalar offset `off`. -/
  -- uget {n : Nat} (ks : Ks n) (off : USize) (h : off.toNat + nX ≤ n) : X

  /-- Write `x` into `ks` starting at scalar offset `off`. -/
  set {n : Nat} (ks : Ks n) (off : Nat) (x : X) (h : off + nX ≤ n) : Ks n
  vector_get_set_eq {n : Nat} (ks : Ks n) (off i : Nat) (x : X) (hoff : off + nX ≤ n)
    (hi : off ≤ i ∧ i < off + nX) :
    VectorType.get (set ks off x hoff) i (by grind)
    =
    getComp x (i - off) (by grind)
  vector_get_set_ne {n : Nat} (ks : Ks n) (off i : Nat) (x : X) (hoff : off + nX ≤ n)
    (hi : i < off ∨ off + nX ≤ i) (hi' : i < n)  :
    VectorType.get (set ks off x hoff) i (by grind)
    =
    VectorType.get ks i hi'

  -- /-- Write `x` into `ks` starting at `USize` scalar offset `off`. -/
  -- uset {n : Nat} (ks : Ks n) (off : USize) (x : X) (h : off.toNat + nX ≤ n) : Ks n

  /-- Append `x` to the end of `ks` as one contiguous `X` block. -/
  push {n : Nat} (ks : Ks n) (x : X) : Ks (n + nX)
  vector_get_push_lt {n : Nat} (ks : Ks n) (x : X) (i : Nat) (hi : i < n) :
    VectorType.get (push ks x) i (by grind) = VectorType.get ks i hi
  vector_get_push_eq {n : Nat} (ks : Ks n) (x : X) (i : Nat) (hi : i < nX) :
    VectorType.get (push ks x) (n + i) (by grind) =
      getComp x i hi

  -- for vectors, matrices, tensors this should be no-op
  toFlatVector : X → Ks nX
  get_toFlatVector_eq_getComp (x : X) (i : Nat) (h : i < nX) :
    VectorType.get (toFlatVector x) i h = getComp x i h

  replicate (n : Nat) (x :X) : Ks (n * nX)
  get_replicate (n : Nat) (x : X) (i j : Nat) (hi : i < n) (hj : j < nX) :
    VectorType.get (replicate n x) (i * nX + j) sorry = getComp x j hj

/-- The default flat vector type for `X`. -/
class HasDefaultFlatVector (X : Type u) (Ks : outParam (Nat → Type v)) (nX : outParam Nat)
    {K : outParam (Type w)} [VectorType Ks K]
    extends HasFlatVector X Ks nX

namespace HasFlatVector

variable {X : Type u} {Ks : Nat → Type v} {K : Type w} {nX : Nat}
  [VectorType Ks K] [HasFlatVector X Ks nX]

attribute [simp]
  vector_get_set_eq
  vector_get_set_ne
  vector_get_push_lt
  vector_get_push_eq
  get_toFlatVector_eq_getComp
  get_replicate

instance [VectorType Rs R] : HasFlatVector R Rs 1 where
  get xs i h := VectorType.get xs i h
  getComp_get_eq_vector_get := by
    intros _ _ _ i; intros;
    have h : i = 0 := by grind;
    simp [h, FlatRepr.getComp]
  set xs off x h := VectorType.set xs off x (by grind)
  vector_get_set_eq := by
    intro n xs off i x hoff hi
    have hioff : i = off := by grind
    subst hioff
    rw [VectorType.get_spec, VectorType.set_spec]
    simp [FlatRepr.getComp]
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
    simp only [Nat.add_zero, VectorType.get_push_eq, FlatRepr.getComp]
  toFlatVector x := VectorType.fromVector #v[x]
  get_toFlatVector_eq_getComp := by
    intro x i h
    have hi0 : i = 0 := by grind
    subst hi0
    simp [VectorType.get_spec, FlatRepr.getComp]
  replicate n x := VectorType.replicate (As := Rs) (n * 1) x
  get_replicate := by
    intros; simp only [Nat.mul_one, VectorType.get_replicate, FlatRepr.getComp]

@[simp]
theorem get_set_eq {n : Nat} (ks : Ks n) (off : Nat) (x : X) (hoff : off + nX ≤ n) :
    get (set ks off x hoff) off (by grind)
    =
    x := by
  apply FlatRepr.ext K; intro i hi
  rw[getComp_get_eq_vector_get, vector_get_set_eq]
  all_goals grind

@[simp]
theorem get_set_ne {n : Nat} (ks : Ks n) (off off' : Nat) (x : X) (hoff : off + nX ≤ n)
    (hoff' : off' + nX ≤ off ∨ off + nX ≤ off') (hoff'' : off' + nX ≤ n) :
    get (X:=X) (set ks off x hoff) off' (by grind)
    =
    get ks off' hoff'' := by
  apply FlatRepr.ext K; intro i hi
  simp only [getComp_get_eq_vector_get]
  rw[vector_get_set_ne]
  all_goals grind

@[simp]
theorem get_push_eq {n : Nat} (ks : Ks n) (x : X) :
    get (X := X) (push ks x) n (by grind) = x := by
  apply FlatRepr.ext K
  intro i hi
  rw [getComp_get_eq_vector_get, vector_get_push_eq]

@[simp]
theorem get_push_lt {n : Nat} (ks : Ks n) (off : Nat) (x : X)
    (hoff : off + nX ≤ n) :
    get (X := X) (push ks x) off (by grind) = get (X := X) ks off hoff := by
  apply FlatRepr.ext K
  intro i hi
  rw [getComp_get_eq_vector_get, getComp_get_eq_vector_get]
  have hlt : off + i < n := by
    have := hoff
    grind
  rw [vector_get_push_lt (ks := ks) (x := x) (i := off + i) hlt]

@[simp]
theorem get_toFlatVector (x : X) :
    get (toFlatVector (Ks := Ks) x) 0 (by simp) = x := by
  apply FlatRepr.ext (K := K)
  intro i hi
  rw [getComp_get_eq_vector_get]
  simp [Nat.zero_add]

@[simp]
theorem get_replicate_eq (n : Nat) (x : X) (i : Nat) (hi : i < n) :
    get (X := X) (replicate (Ks := Ks) n x) (i * nX) (by
      have hle := Nat.mul_le_mul_right nX (Nat.succ_le_of_lt hi)
      simpa [Nat.succ_mul] using hle) = x := by
  apply FlatRepr.ext (K := K)
  intro j hj
  rw [getComp_get_eq_vector_get]
  exact get_replicate (X := X) (Ks := Ks) (K := K) n x i j hi hj

end HasFlatVector

end NumLean
