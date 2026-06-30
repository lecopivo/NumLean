module

@[expose] public section

namespace NumLean

class VMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  vmul : α → β → γ

/-- Multiplication between matrices and vectors.

In particular:
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
