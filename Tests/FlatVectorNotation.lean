module

public import NumLean.Data.FlatVector.Notation
public import NumLean.Data.Scalars.Float64
public import NumLean.Data.Scalars.Float64.RealModel

@[expose] public section

open NumLean

namespace Tests.FlatVectorNotation

variable (X : Type u)  {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX]
  (I : Type v) [IndexType I nI]
  (J : Type v) [IndexType J nJ]
  (K : Type v) [IndexType K nK]
  (L : Type v) [IndexType L nL]

example : X^[I] = FlatVector X I := rfl
/-- info: X^[I] : Type u_1 -/
#guard_msgs in
#check FlatVector X I

example : X^[I, J] = FlatVector X (I × J) := rfl
/-- info: X^[I, J] : Type u_1 -/
#guard_msgs in
#check FlatVector X (I × J)

example : X^[I, J, K] = FlatVector X (I × J × K) := rfl
/-- info: X^[I, J, K] : Type u_1 -/
#guard_msgs in
#check FlatVector X (I × J × K)

example : X^[[I, J], K] = FlatVector X ((I × J) × K) := rfl
/-- info: X^[[I, J], K] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((I × J) × K)

example : X^[[I, J], [K, L]] = FlatVector X ((I × J) × (K × L)) := rfl
/-- info: X^[[I, J], [K, L]] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((I × J) × (K × L))

example : X^[[I, J], K, L] = FlatVector X ((I × J) × K × L) := rfl
/-- info: X^[[I, J], [K, L]] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((I × J) × K × L)

variable (m n k l : Nat)

example : X^[n] = FlatVector X (Fin n) := rfl
/-- info: X^[n] : Type u_1 -/
#guard_msgs in
#check FlatVector X (Fin n)

example : X^[m, n] = FlatVector X (Fin m × Fin n) := rfl
/-- info: X^[m, n] : Type u_1 -/
#guard_msgs in
#check FlatVector X (Fin m × Fin n)

example : X^[m, n, K] = FlatVector X (Fin m × Fin n × K) := rfl
/-- info: X^[m, n, K] : Type u_1 -/
#guard_msgs in
#check FlatVector X (Fin m × Fin n × K)

example : X^[[m, J], k] = FlatVector X ((Fin m × J) × Fin k) := rfl
/-- info: X^[[m, J], k] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((Fin m × J) × Fin k)

example : X^[[m, n], [K, L]] = FlatVector X ((Fin m × Fin n) × (K × L)) := rfl
/-- info: X^[[m, n], [K, L]] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((Fin m × Fin n) × (K × L))

example : X^[[I, J], k, l] = FlatVector X ((I × J) × Fin k × Fin l) := rfl
/-- info: X^[[I, J], [k, l]] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((I × J) × Fin k × Fin l)

/-- info: X^[[m, n], [k, L]] : Type u_1 -/
#guard_msgs in
#check FlatVector X ((Fin m × Fin n) × (Fin k × L))

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
#check (FlatVector.ofVector (I := Fin 2 × Fin 3) (#v[1.0, 2, 3, 4, 5, 6] : Vector Float 6))

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

/-- error: ill-shaped FlatVector literal: expected sub-shape [3], got [1] -/
#guard_msgs in
#check (⊞[[1.0, 2, 3], [4]] : Float^[2, 3])

/-- error: FlatVector literal shape mismatch: expected [2, 3], got [2, 2] -/
#guard_msgs in
#check (⊞[[1.0, 2], [3, 4]] : Float^[2, 3])

end LiteralNotation

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

end Tests.FlatVectorNotation
