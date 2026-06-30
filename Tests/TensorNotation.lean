module

public import NumLean.Data.Tensor.Notation
public import NumLean.Data.Tensor.SliceNotation
public import NumLean.Data.Scalars.Float64
public import NumLean.Data.Scalars.Float64.RealModel

@[expose] public section

open NumLean

namespace Tests.TensorNotation

variable (X : Type u)  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX]
  (I : Type v) [IndexType I nI]
  (J : Type v) [IndexType J nJ]
  (K : Type v) [IndexType K nK]
  (L : Type v) [IndexType L nL]

example : X^[I] = Tensor X I := rfl
/-- info: X^[I] : Type u_1 -/
#guard_msgs in
#check Tensor X I

example : X^[I, J] = Tensor X (I × J) := rfl
/-- info: X^[I, J] : Type u_1 -/
#guard_msgs in
#check Tensor X (I × J)

example : X^[I, J, K] = Tensor X (I × J × K) := rfl
/-- info: X^[I, J, K] : Type u_1 -/
#guard_msgs in
#check Tensor X (I × J × K)

example : X^[[I, J], K] = Tensor X ((I × J) × K) := rfl
/-- info: X^[[I, J], K] : Type u_1 -/
#guard_msgs in
#check Tensor X ((I × J) × K)

example : X^[[I, J], [K, L]] = Tensor X ((I × J) × (K × L)) := rfl
/-- info: X^[[I, J], [K, L]] : Type u_1 -/
#guard_msgs in
#check Tensor X ((I × J) × (K × L))

example : X^[[I, J], K, L] = Tensor X ((I × J) × K × L) := rfl
/-- info: X^[[I, J], [K, L]] : Type u_1 -/
#guard_msgs in
#check Tensor X ((I × J) × K × L)

variable (m n k l : Nat)

example : X^[n] = Tensor X (Fin n) := rfl
/-- info: X^[n] : Type u_1 -/
#guard_msgs in
#check Tensor X (Fin n)

example : X^[m, n] = Tensor X (Fin m × Fin n) := rfl
/-- info: X^[m, n] : Type u_1 -/
#guard_msgs in
#check Tensor X (Fin m × Fin n)

example : X^[m, n, K] = Tensor X (Fin m × Fin n × K) := rfl
/-- info: X^[m, n, K] : Type u_1 -/
#guard_msgs in
#check Tensor X (Fin m × Fin n × K)

example : X^[[m, J], k] = Tensor X ((Fin m × J) × Fin k) := rfl
/-- info: X^[[m, J], k] : Type u_1 -/
#guard_msgs in
#check Tensor X ((Fin m × J) × Fin k)

example : X^[[m, n], [K, L]] = Tensor X ((Fin m × Fin n) × (K × L)) := rfl
/-- info: X^[[m, n], [K, L]] : Type u_1 -/
#guard_msgs in
#check Tensor X ((Fin m × Fin n) × (K × L))

example : X^[[I, J], k, l] = Tensor X ((I × J) × Fin k × Fin l) := rfl
/-- info: X^[[I, J], [k, l]] : Type u_1 -/
#guard_msgs in
#check Tensor X ((I × J) × Fin k × Fin l)

/-- info: X^[[m, n], [k, L]] : Type u_1 -/
#guard_msgs in
#check Tensor X ((Fin m × Fin n) × (Fin k × L))

section LiteralNotation

/-- info: ⊞[1.0, 2, 3, 4] : Float^[4] -/
#guard_msgs in
#check (⊞[1.0, 2, 3, 4] : Float^[4])

/-- info: ⊞[1.0, 2, 3, 4] : Float^[4] -/
#guard_msgs in
#check (⊞[1.0, 2, 3, 4])

/-- info: ⊞[[1, 2, 3], [4, 5, 6]] : Float^[2, 3] -/
#guard_msgs in
#check (⊞[[1, 2, 3], [4, 5, 6]] : Float^[2, 3])

/-- info: ⊞[[1.0, 2, 3], [4, 5, 6]] : Float^[2, 3] -/
#guard_msgs in
#check (⊞[[1.0, 2, 3], [4, 5, 6]])

/-- info: ⊞[[1.0, 2, 3], [4, 5, 6]] : Float^[2, 3] -/
#guard_msgs in
#check (Tensor.ofVector (I := Fin 2 × Fin 3) (#v[1.0, 2, 3, 4, 5, 6] : Vector Float 6))

/-- info: ⊞[[1.0, 2, 3], [4, 5, 6]].shape : HTuple ℕ (hp(•, •)) -/
#guard_msgs in
#check ⊞[[1.0, 2, 3], [4, 5, 6]].shape

/-- info: ⊞[[[1], [2]], [[3], [4]]] : Float^[2, 2, 1] -/
#guard_msgs in
#check (⊞[[[1], [2]], [[3], [4]]] : Float^[2, 2, 1])

/-- info: ⊞[[[1.0], [2]], [[3], [4]]] : Float^[2, 2, 1] -/
#guard_msgs in
#check (⊞[[[1.0], [2]], [[3], [4]]])

/-- info: ⊞[⊞[1.0, 2], ⊞[3.0, 4]] : Float^[2]^[2] -/
#guard_msgs in
#check ⊞[⊞[1.0, 2], ⊞[3.0, 4]]

/-- info: ⊞[⊞[1.0, 2], ⊞[3.0, 4]] : Float^[2]^[2] -/
#guard_msgs in
#check (⊞[⊞[1.0, 2], ⊞[3.0, 4]] : (Float^[2])^[2])

/-- error: ill-shaped Tensor literal: expected sub-shape [3], got [1] -/
#guard_msgs in
#check (⊞[[1.0, 2, 3], [4]] : Float^[2, 3])

/-- error: Tensor literal shape mismatch: expected [2, 3], got [2, 2] -/
#guard_msgs in
#check (⊞[[1.0, 2], [3, 4]] : Float^[2, 3])

end LiteralNotation

section FunctionNotation

/-- info: ⊞ x =>
  match x with
  | (i, j) => if i = j then 1.0 else 0.0 : Float^[5, 5] -/
#guard_msgs in
#check ((⊞ ((i, j) : Fin 5 × Fin 5) => if i = j then 1.0 else 0.0) : Float^[5, 5])

/-- info: ⊞ i j => if i = j then 1.0 else 0.0 : Float^[5, 5] -/
#guard_msgs in
#check ((⊞ (i j : Fin 5) => if i = j then 1.0 else 0.0) : Float^[5, 5])

/-- info: ⊞ i j => if i = j then 1.0 else 0.0 : Float^[5, 5] -/
#guard_msgs in
#check (⊞ (i j : Fin 5) => if i = j then 1.0 else 0.0)

/-- info: ⊞ i => ⊞ j => if i = j then 1.0 else 0.0 : Float^[5]^[5] -/
#guard_msgs in
#check ((⊞ (i : Fin 5) => ⊞ (j : Fin 5) => if i = j then 1.0 else 0.0) : Float^[5]^[5])

/-- info: ⊞ i => ⊞ j => if i = j then 1.0 else 0.0 : Float^[5]^[5] -/
#guard_msgs in
#check (⊞ (i : Fin 5) => ⊞ (j : Fin 5) => if i = j then 1.0 else 0.0)

example (i j : Fin 5) :
    ((⊞ (i j : Fin 5) => if i = j then 1.0 else 0.0) : Float^[5, 5])[i, j]
      = if i = j then 1.0 else 0.0 := by
  simp [Function.HasUncurry.uncurry]

local instance : HasDefaultFlatRepr ℕ (Vector ℕ) 1 where
local instance : HasDefaultFlatRepr ℤ (Vector ℤ) 1 where

/-- info: ⊞ i j => if i = j then 1 else 0 : ℕ^[5, 5] -/
#guard_msgs in
#check (⊞ (i j : Fin 5) => if i = j then 1 else 0)

/-- info: ⊞ i j => if i = j then -11 else 0 : ℤ^[5, 5] -/
#guard_msgs in
#check (⊞ (i j : Fin 5) => if i = j then -11 else 0)

end FunctionNotation

section CommaGetElemNotation

/-- info: fun A i j => A[(i, j)] : Float^[2, 3] → Fin 2 → Fin 3 → Float -/
#guard_msgs in
#check fun (A : Float^[2, 3]) (i : Fin 2) (j : Fin 3) => A[i, j]

example (A : Float^[2, 3]) (i : Fin 2) (j : Fin 3) :
    A[i, j] = A[(i, j)] := rfl

/-- info: fun A i j k l => A[((i, j), k, l)] : X^[[I, J], [K, L]] → I → J → K → L → X -/
#guard_msgs in
#check fun (A : X^[[I, J], [K, L]]) (i : I) (j : J) (k : K) (l : L) =>
  A[[i, j], [k, l]]

example (A : X^[[I, J], [K, L]]) (i : I) (j : J) (k : K) (l : L) :
    A[[i, j], [k, l]] = A[((i, j), (k, l))] := rfl

example (A : Float^[2, 3]) (i : Fin 2) (j : Fin 3) :
    A[i, j]? = A[(i, j)]? := rfl

example (A : Float^[2, 3]) (i : Fin 2) (j : Fin 3) :
    A[i, j]! = A[(i, j)]! := rfl

example (A : Float^[2, 3]) (i : Fin 2) (j : Fin 3) (h : True) :
    (A[i, j]'h) = getElem A (i, j) h := rfl

example (A : X^[[I, J], [K, L]]) (i : I) (j : J) (k : K) (l : L) :
    A[[i, j], [k, l]]? = A[((i, j), (k, l))]? := rfl

example [Inhabited X] (A : X^[[I, J], [K, L]]) (i : I) (j : J) (k : K) (l : L) :
    A[[i, j], [k, l]]! = A[((i, j), (k, l))]! := rfl

example (A : X^[[I, J], [K, L]]) (i : I) (j : J) (k : K) (l : L) (h : True) :
    (A[[i, j], [k, l]]'h) = getElem A ((i, j), (k, l)) h := rfl

end CommaGetElemNotation

section SliceNotation

example (A : X^[2, 3]) : Tensor.InjectiveView X (Fin 2) (Fin 2 × Fin 3) :=
  A[:, 1]&

example (A : X^[10, 8]) : Tensor.InjectiveView X (Fin (5 - 2)) (Fin 10 × Fin 8) :=
  A[2:5, 3]&

example (A : X^[2, 3]) : Tensor.InjectiveView X (Fin 2 × Fin 3) (Fin 2 × Fin 3) :=
  A[:, :]&

example (A : X^[2, 3]) : Tensor.InjectiveView X (Fin 1) (Fin 2 × Fin 3) :=
  A[1, 2]&

example (A : X^[[2, 2], [2, 2]]) :
    Tensor.InjectiveView X (Fin 2 × Fin 2) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  A[[:, 0], [1, :]]&

example (A : X^[[10, 10], [10, 10]]) :
    Tensor.InjectiveView X ((Fin 10 × Fin 4) × Fin 5) ((Fin 10 × Fin 10) × (Fin 10 × Fin 10)) :=
  A[[:, 1:5], [2, :-5]]&

/-- error: nested tensor slice rank mismatch: expected exactly two components -/
#guard_msgs in
example (A : X^[[2, 2], [2, 2]]) :=
  A[[:, :], [1:]]&

example : Tensor.InjectiveView Float (Fin 2) (Fin 2 × Fin 3) :=
  let A := ⊞[[1.0, 2, 3], [4, 5, 6]]
  A[:, 2]&

example (B : Float^[m, n]) (_hm : 20 < m) (hn : 30 < n) :
    Tensor.InjectiveView Float (Fin m × Fin 5) (Fin m × Fin n) :=
  B[:, 5:10]&


/--
info: fun A =>
  (A.mkView
        ((FinHTupleMap.contiguous1D 0 ⋯).prod (FinHTupleMap.const (h(20)) (h(30)) (h(2)) _check._proof_4))).toInjective
    ⋯ : Float^[20, 30] → Tensor.InjectiveView Float (Fin 20) (Fin 20 × Fin 30)
-/
#guard_msgs in
#check fun (A : Float^[20,30]) => A[:, 2]&

/--
info: fun A =>
  (A.mkView
        ((FinHTupleMap.const (h(30)) (h(20)) (h(5)) _check._proof_3).prod (FinHTupleMap.contiguous1D 0 ⋯))).toInjective
    ⋯ : Float^[20, 30] → Tensor.InjectiveView Float (Fin 30) (Fin 20 × Fin 30)
-/
#guard_msgs in
#check fun (A : Float^[20,30]) => A[5, :]&

/--
info: fun A =>
  (A.mkView ((FinHTupleMap.contiguous1D 2 ⋯).pair (FinHTupleMap.contiguous1D 0 ⋯))).toInjective
    ⋯ : Float^[20, 30] → Tensor.InjectiveView Float (Fin (20 - 2) × Fin (30 - 3)) (Fin 20 × Fin 30)
-/
#guard_msgs in
#check fun (A : Float^[20,30]) => A[2:, :-3]&

/--
info: fun A =>
  (A.mkView
        ((FinHTupleMap.const (h(8)) (h(20)) (h(5)) _check._proof_3).prod
          (FinHTupleMap.contiguous1D (30 - 10) ⋯))).toInjective
    ⋯ : Float^[20, 30] → Tensor.InjectiveView Float (Fin 8) (Fin 20 × Fin 30)
-/
#guard_msgs in
#check fun (A : Float^[20,30]) => A[5, -10:-2]&

/--
info: fun A =>
  (A.mkView
        (((FinHTupleMap.contiguous1D 0 ⋯).pair (FinHTupleMap.contiguous1D 1 ⋯)).pair
          ((FinHTupleMap.const (h(50 - 5)) (h(10)) (h(2)) _check._proof_5).prod
            (FinHTupleMap.contiguous1D 0 ⋯)))).toInjective
    ⋯ : Float^[[20, 30], [10, 50]] →
  Tensor.InjectiveView Float ((Fin 20 × Fin 4) × Fin (50 - 5)) ((Fin 20 × Fin 30) × Fin 10 × Fin 50)
-/
#guard_msgs in
#check fun (A : Float^[[20,30], [10,50]]) => A[[:, 1:5],[2,:-5]]&

example (A : Float^[[20,30], [10,50]]) :
    Tensor.InjectiveView Float ((Fin 20 × Fin 4) × Fin 45)
      ((Fin 20 × Fin 30) × (Fin 10 × Fin 50)) :=
  A[[:, 1:5],[2,:-5]]&


end SliceNotation

end Tests.TensorNotation
