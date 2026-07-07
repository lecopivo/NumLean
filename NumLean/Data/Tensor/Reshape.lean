module

public import NumLean.Data.Tensor.HasFlatRepr
public import Mathlib.Tactic.Ring

@[expose] public section

namespace NumLean
namespace Tensor

/-- Converts `shape` into product of `Fin` types.

Examples:
  - `indexTypeOfShape h(n) = Fin n`
  - `indexTypeOfShape h(m, n) = Fin m × Fin n`
  - `indexTypeOfShape h((m, n), (k, l)) = (Fin m × Fin n) × (Fin k × Fin l)` -/
def indexTypeOfShape {r} (shape : Shape r) : Type :=
  match shape with
  | .leaf n => Fin n
  | .prod s s' => indexTypeOfShape s × indexTypeOfShape s'

/-- This class statically evaluates `indexTypeOfShape shape` and provides its result as
`I : outParam Type`. -/
class IndexTypeOfShape {r} (shape : Shape r) (I : outParam Type) where
  valid : indexTypeOfShape shape = I

instance : IndexTypeOfShape h(n) (Fin n) where
  valid := rfl

instance {I I'} [inst : IndexTypeOfShape s I] [inst' : IndexTypeOfShape s' I'] :
    IndexTypeOfShape (.prod s s') (I × I') where
  valid := by rw [indexTypeOfShape, inst.valid, inst'.valid]

/-- Tactic used to prove that reshaping a tensor is valid. -/
macro "valid_reshape_tactic" : tactic =>
  `(tactic| (first | simp | decide | ring | (simp; ring) | (cbv; ring)))

variable {X : Type u} {I : Type v} {J : Type w}
    {Ks K nX nI nJ} [HasDefaultFlatRepr X Ks] [VectorType Ks K] [HasFlatRepr X Ks nX]

/-- Reinterpret tensor storage with a directly supplied new index type of the same cardinality. -/
def reindex [IndexType I nI] [IndexType J nJ] (x : Tensor X I)
    (matching_size : nI = nJ := by valid_reshape_tactic) : Tensor X J :=
  { data := matching_size ▸ x.data }

/-- Reshape tensor given `shape : Shape r` which is usually given as `h(n₁, ..., nᵣ)` where
`n₁, ..., nᵣ` are the dimension sizes of the new shape.

Examples:
  - `x.reshape h(3,5) : Float^[3,5]` for `x : Float^[15]`
  - `A.reshape h(12) : Float^[12]` for `A : Float^[4,3]`
  - `A.reshape h(3,2,2) : Float^[3,2,2]` for `A : Float^[4,3]`
  - `y.reshape h(m + 1, n) : Float^[m + 1, n]` for `y : Float^[m * n + n]`

This function requires a proof `matching_size` that the new shape has the same number of elements
as the old shape. Use `reindex` when the target index type `J` is already known. -/
def reshape [IndexType I nI] {r : Rank} (x : Tensor X I) (shape : Shape r)
    {J} [IndexTypeOfShape shape J] [IndexType J nJ]
    (matching_size : nI = nJ := by valid_reshape_tactic) : Tensor X J :=
  x.reindex (J := J) matching_size

/-- View a product-index tensor as an outer tensor of inner tensors.

This is a zero-copy reinterpretation of the same row-major storage. -/
def curry [IndexType I nI] [IndexType J nJ] [TensorType Ks] [Inhabited K]
    (x : Tensor X (I × J)) : Tensor (Tensor X J) I :=
  { data :=
      have h : (nI * nJ) * nX = nI * (nJ * nX) := by ring
      h ▸ x.data }

/-- View an outer tensor of inner tensors as one product-index tensor.

This is a zero-copy reinterpretation of the same row-major storage. -/
def uncurry [IndexType I nI] [IndexType J nJ] [TensorType Ks] [Inhabited K]
    (x : Tensor (Tensor X J) I) : Tensor X (I × J) :=
  { data :=
      have h : nI * (nJ * nX) = (nI * nJ) * nX := by ring
      h ▸ x.data }

end Tensor
end NumLean
