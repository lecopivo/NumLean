module

@[expose] public section

namespace NumLean

def Tensor (R : Type) (I : Type) : Type := Unit

macro:max R:term "^[" I:term "]" : term => `(Tensor $R $I)

class VMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  vmul : α → β → γ

/-- Multiplication between matrices and vectors.

In particular:
  - `u *ᵥ v : R` is dot product for `u : R^[I]` and `v : R^[I]`
  - `A *ᵥ v : R^[I]` is matrix vector product for `A : R^[I, J]` and `v : R^[J]`
  - `u *ᵥ A : R^[J]` is vector matrix product for `u : R^[I]` and `A : R^[I, J]`
  - `A *ᵥ B : R^[I, J]` is matrix matrix product for `A : R^[I, J]` and `B : R^[J, K]`


Please keep in mind that `^[ ... ]` is right associated i.e. `R^[I, J, K] = R^[I, [J, K]] ≠ R^[[I, J], K]`.
This has consequence on how `T *ᵥ B` is intepreted for `T : R^[I, J, K]` and `B : R^[J, K]`.
Lucklily, `R^[I, [J, K]]` and `R^[[I, J], K]` have identical memory layout and therefore you can
convert between them at no runtime cost with:
  - `A.assocl : R^[[I, J], K]` - left associate for `A : R^[I, J, K]`
  - `B.assocr : R^[I, J, K]`   - right associate for `B : R^[[I, J], K]`

Examples of matrix/vector multiplications between higher order :
  - `T *ᵥ B : R^[I]`    - matrix vector product for `T : R^[I, J, K]` and `B : R^[J, K]`
  - `u *ᵥ T : R^[J, K]` - vector matrix product for `T : R^[I, J, K]` and `u : R^[I]`
  - `T.assocl *ᵥ w : R^[I, J]` - matrix vector product for `T : R^[I, J, K]` and `w : R^[K]`
  - `A *ᵥ T.assocl : R^[K]` - vector matrix product for `T : R^[I, J, K]` and `A : R^[I, J]`

For higher rank tensors you can reassociate the products completely with `assoclAll` and `assocrAll`
  - `X.assoclAll *ᵥ Y : R^[I₁,...,Iₘ,J₁,...Jₙ]` - matrix matrix product for `X : R^[I₁,...,Iₘ,K]` and `Y : R^[K, J₁, ..., Jₙ]`
  - `Y *ᵥ Z.assoclAll : R^[K,L]` - matrix matrix product for `Y : R^[K, J₁, ..., Jₙ]` and `Z : R^[J₁, ..., Jₙ, L]`

 -/
scoped infixr:73 " *ᵥ " => VMul.vmul

instance {R I} : VMul R^[I] R^[I] R where
  vmul := sorry

instance {R I J} : VMul R^[I × J] R^[J] R^[I] where
  vmul := sorry

instance {R I J} : VMul R^[I] R^[I × J] R^[J] where
  vmul := sorry

instance {R I J K} : VMul R^[I × J] R^[J × K] R^[I × K] where
  vmul := sorry

variable {R I J K : Type} (u : R^[I]) (v : R^[J]) (w : R^[K]) (A : R^[I × J]) (B : R^[J × K])
         (T : R^[I × J × K]) (S : R^[(J × K) × I])


-- Dot product

/-- info: u *ᵥ u : R -/
#guard_msgs in
#check u *ᵥ u

/-- info: A *ᵥ A : R -/
#guard_msgs in
#check A *ᵥ A


-- vector-matrix

/-- info: u *ᵥ A : Tensor R J -/
#guard_msgs in
#check u *ᵥ A

/-- info: u *ᵥ T : Tensor R (J × K) -/
#guard_msgs in
#check u *ᵥ T


-- matrix-vector

/-- info: A *ᵥ v : Tensor R I -/
#guard_msgs in
#check A *ᵥ v

/-- info: T *ᵥ B : Tensor R I -/
#guard_msgs in
#check T *ᵥ B


-- matrix-matrix

/-- info: A *ᵥ B : Tensor R (I × K) -/
#guard_msgs in
#check A *ᵥ B

/-- info: T *ᵥ S : Tensor R (I × I) -/
#guard_msgs in
#check T *ᵥ S


-- mixed

/-- info: A *ᵥ B *ᵥ w : Tensor R I -/
#guard_msgs in
#check A *ᵥ B *ᵥ w

/-- info: u *ᵥ A *ᵥ B *ᵥ w : R -/
#guard_msgs in
#check u *ᵥ A *ᵥ B *ᵥ w

/-- info: T *ᵥ S *ᵥ u : Tensor R I -/
#guard_msgs in
#check T *ᵥ S *ᵥ u

/-- info: u *ᵥ T *ᵥ S *ᵥ u : R -/
#guard_msgs in
#check u *ᵥ T *ᵥ S *ᵥ u
