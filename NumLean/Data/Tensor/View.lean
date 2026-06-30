module

public import NumLean.Data.Tensor.Basic
public import NumLean.Interfaces.Algebra.MatrixOps
public import NumLean.Interfaces.TensorAlgebra
public import NumLean.Interfaces.TensorType

@[expose] public section

namespace NumLean.Tensor

/-- `J` shaped view into `Tensor X I`.

Unlike in many other languages, this view is *owning*. When you create a view, for example
by slicing, you should give up hold off the original tensor. Once you are done working with
the view/slice you can recover the whole tensor using the `View.data` function.

-- todo: this applies more to InjectiveView as plain view does not allow to modify the data

Example usage:
```
  let mut row := A[3, :]   -- unitialize view on a row of a matrix `A`
  row += u                -- add `u` to that row
  let A := row.data       -- recover the whole matrix with modified row under "new" name (Lean shadows the original `A`)
```
First, we create a view on a row of the matrix `A`. After this point it is crucuial that we do not
refer to `A` ever again. If we do so, then `row` knows that it is the only owner of the data of `A`
and can mutate the data in place. This is what we do on the second line. Lastly, we recover the
whole matrix on the last line. A common practice it Lean is to shadow variables, the `let A := ...`
introduces brand new identifier `A` which shadows the original `A`. This has two benefits, it looks
like that we mutated `A` and we are unable to access the original `A` which would preven all
operations on `row` to mutate the data of the matrix in place.

An inline vertions of the above would be:
```
  let A := (A[3, :] + u).data
```
-/
structure View (X : Type u) (J : Type v) (I : Type w)
    {Ks K nX} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX]
    {nJ jrank jshape} [TensorIndexType J nJ jrank jshape]
    {nI irank ishape} [TensorIndexType I nI irank ishape] where
  data : Tensor X I
  layout : Layout jshape ishape

-- A[1,2,3]&
-- A[1,2,3]&!
-- A[1,2,3]&?
-- A[1,2,3]&'h

/-- Injective `J` shaped view into `Tensor X I`.

InjectiveView is required when we want to mutate the underlining data. Injectivity
of the view map `J → I` guarantees us that the every `j : J` corresponds to only a single `data[i]`
thus avoiding any ambiguity if that wans't the case. -/
structure InjectiveView (X : Type u) (J : Type v) (I : Type w)
    {Ks K nX} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX]
    {nJ jrank jshape} [TensorIndexType J nJ jrank jshape]
    {nI irank ishape} [TensorIndexType I nI irank ishape]
  extends View X J I where
  injective : layout.Injective


structure BijectiveView (X : Type u) (J : Type v) (I : Type w)
    {Ks K nX} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX]
    {nJ jrank jshape} [TensorIndexType J nJ jrank jshape]
    {nI irank ishape} [TensorIndexType I nI irank ishape]
  extends InjectiveView X J I where
  bijective : layout.Bijective


attribute [coe] InjectiveView.toView BijectiveView.toInjectiveView

open Interfaces.Algebra


-- Notation for Views:

-- View X (Fin 1) (Fin 2 × Fin 2)
-- X^[[1] -> [2,2]]
-- X^[[1] → [2,2]]

-- InjectiveView X (Fin 1) (Fin 2 × Fin 2))
-- X^[[1] >-> [2,2]]
-- X^[[1] ↪ [2,2]]

-- BijectiveView X (Fin 1) (Fin 2 × Fin 2))
-- X^[[4] <-> [2,2]]
-- X^[[4] ↔ [2,2]]

section BasicOperations

variable
    {R : Type} {Rs} [VectorType Rs R] [RingOps R] [TensorRingOps Rs R]
    {X : Type*} {nX} [HasDefaultFlatRepr X Rs nX]
    {I : Type*} {nI irank ishape} [TensorIndexType I nI irank ishape]
    {J : Type*} {nJ jrank jshape} [TensorIndexType J nJ jrank jshape]
    {K : Type*} {nK krank kshape} [TensorIndexType K nK krank kshape]

instance : Coe (InjectiveView X J I) (View X J I) := ⟨fun x => x.toView⟩
instance : Coe (BijectiveView X J I) (InjectiveView X J I) := ⟨fun x => x.toInjectiveView⟩
instance : Coe (BijectiveView X J I) (View X J I) := ⟨fun x => x.toView⟩

-- maybe call this "copy"? "mkCopy"?
namespace View

variable [TensorType Rs]

open TensorType in
def extract [Inhabited R] (x : View X J I) : Tensor X J :=
  have hj := TensorIndexTypeOfRank.size_eq_shape_size (I := J) (rank:= jrank)
  have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
  let srcData := x.data.data
  let srcMap  := (x.layout.pair (.id h(nX))).linearize
  let dstData := VectorType.replicate (As := Rs) (nJ * nX) (default : R)
  let dstMap  := (Layout.id (jshape.prod h(nX))).linearize
  let data := copySlice R x.data.data (srcMap.cast _ _ rfl (by simp [← hi]))
                          dstData (dstMap.cast _ _ rfl (by simp [←hj])) (by grind)
  { data := data }

end View

namespace InjectiveView

variable [TensorType Rs]

open TensorType in
def set (dst : InjectiveView X J I) (src : View X J K) : InjectiveView X J I :=
  let srcMap := (src.layout.pair (.id h(nX))).linearize
  let dstMap := (dst.layout.pair (.id h(nX))).linearize
  have hk := TensorIndexTypeOfRank.size_eq_shape_size (I := K) (rank:= krank)
  have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
  let data := copySlice R
    src.data.data (srcMap.cast _ _ rfl (by simp [← hk]))
    dst.data.data (dstMap.cast _ _ rfl (by simp [← hi])) sorry
  { data := {data}, layout := dst.layout, injective := dst.injective }

open TensorType in
def fill (dst : InjectiveView X J I) (x : X) : InjectiveView X J I :=
  have hj := TensorIndexTypeOfRank.size_eq_shape_size (I := J) (rank:= jrank)
  have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
  let srcData := HasFlatRepr.replicate (Ks := Rs) nJ x
  let srcMap := (Layout.id (jshape.prod h(nX))).linearize
  let dstMap := (dst.layout.pair (.id h(nX))).linearize
  let data := copySlice R
    srcData (srcMap.cast _ _ rfl (by simp [← hj]))
    dst.data.data (dstMap.cast _ _ rfl (by simp [← hi])) sorry
  { data := {data}, layout := dst.layout, injective := dst.injective }

def toBijective (x : InjectiveView X J I) (h : x.layout.Bijective) : BijectiveView X J I where
  data := x.data
  layout := x.layout
  injective := x.injective
  bijective := h

end InjectiveView

namespace View

def toInjective (x : View X J I) (h : x.layout.Injective)  : InjectiveView X J I where
  data := x.data
  layout := x.layout
  injective := h

def toBijective (x : View X J I) (h : x.layout.Bijective)  : BijectiveView X J I where
  data := x.data
  layout := x.layout
  injective := h.1
  bijective := h

end View

def _root_.NumLean.Tensor.toView (x : Tensor X I) : BijectiveView X I I where
  data := x
  layout := .id ishape
  injective := by grind
  bijective := by sorry

def _root_.NumLean.Tensor.mkView (x : Tensor X I)
    {r} {shape : Shape r} (layout : Layout shape ishape)
    {J} [IndexTypeOfShape shape J] [TensorIndexType J nJ r shape] :
    View X J I where
  data := x
  layout := layout


open TensorRingOps


instance : HAdd (InjectiveView X J I) (View X J K) (InjectiveView X J I) where
  hAdd x y :=
    let xmap := (x.layout.pair (.id h(nX))).linearize
    let ymap := (y.layout.pair (.id h(nX))).linearize
    have hk := TensorIndexTypeOfRank.size_eq_shape_size (I := K) (rank:= krank)
    have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
    let data := tensorAxpy (1 : R)
      y.data.data (ymap.cast _ _ rfl (by simp [← hk]))
      x.data.data (xmap.cast _ _ rfl (by simp [← hi])) sorry
    { data := {data}, layout := x.layout, injective := x.injective }

instance : HAdd (InjectiveView X J I) (InjectiveView X J K) (InjectiveView X J I) where
  hAdd x y := HAdd.hAdd x (y.toView : View X J K)

instance : HAdd (InjectiveView X J I) (Tensor X J) (InjectiveView X J I) where
  hAdd x y := HAdd.hAdd x (y.toView.toView : View X J J)

@[simp]
theorem add_inj_view_inj_view (x : InjectiveView X J I) (y : InjectiveView X J K) :
  x + y = x + y.toView := rfl

@[simp]
theorem add_inj_view_tensor (x : InjectiveView X J I) (y : Tensor X J) :
  x + y = x + y.toView.toView := rfl


instance : HSub (InjectiveView X J I) (View X J K) (InjectiveView X J I) where
  hSub x y :=
    let xmap := (x.layout.pair (.id h(nX))).linearize
    let ymap := (y.layout.pair (.id h(nX))).linearize
    have hk := TensorIndexTypeOfRank.size_eq_shape_size (I := K) (rank:= krank)
    have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
    let data := tensorAxpy (- 1 : R) (shape := jshape.prod h(nX))
      y.data.data (ymap.cast _ _ rfl (by simp [← hk]))
      x.data.data (xmap.cast _ _ rfl (by simp [← hi])) sorry
    { data := {data}, layout := x.layout, injective := x.injective }

instance : HSub (InjectiveView X J I) (InjectiveView X J K) (InjectiveView X J I) where
  hSub x y := x - y.toView

instance : HSub (InjectiveView X J I) (Tensor X J) (InjectiveView X J I) where
  hSub x y := x - y.toView.toView

@[simp]
theorem sub_inj_view_inj_view (x : InjectiveView X J I) (y : InjectiveView X J K) :
  x - y = x - y.toView := rfl

@[simp]
theorem sub_inj_view_tensor (x : InjectiveView X J I) (y : Tensor X J) :
  x - y = x - y.toView.toView := rfl


instance : Neg (InjectiveView X J I) where
  neg x :=
    let xmap := (x.layout.pair (.id h(nX))).linearize
    have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
    let data := tensorScal (-1 : R)
      x.data.data (xmap.cast _ _ rfl (by simp [← hi])) sorry
    { data := {data}, layout := x.layout, injective := x.injective }


instance : SMul R (InjectiveView X J I) where
  smul a x :=
    let xmap := (x.layout.pair (.id h(nX))).linearize
    have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
    let data := tensorScal a
      x.data.data (xmap.cast _ _ rfl (by simp [← hi])) sorry
    { data := {data}, layout := x.layout, injective := x.injective }


namespace View

def dot (x : View X J I) (y : View X J K) : R :=
  let xmap := (x.layout.pair (.id h(nX))).linearize
  let ymap := (y.layout.pair (.id h(nX))).linearize
  have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
  have hk := TensorIndexTypeOfRank.size_eq_shape_size (I := K) (rank:= krank)
  TensorRingOps.tensorDot x.data.data (xmap.cast _ _ rfl (by simp [← hi]))
    y.data.data (ymap.cast _ _ rfl (by simp [← hk]))

def sum (x : View X J I) : X :=
  have hi := TensorIndexTypeOfRank.size_eq_shape_size (I := I) (rank:= irank)
  HasFlatRepr.fromVector (Ks := Rs) <| Vector.ofFn fun c : Fin nX =>
    let cmap : Layout jshape h(nX) := FinHTupleMap.const jshape h(nX) h(c.1) (by simp [c.2])
    let xmap := (x.layout.prod cmap).linearize
    TensorRingOps.tensorSum x.data.data (xmap.cast _ _ rfl (by simp [← hi]))

end View

end BasicOperations


variable
    {R : Type} {Rs} [VectorType Rs R] [RingOps R] [TensorRingOps Rs R] [TensorType Rs]
    {X : Type*} [HasDefaultFlatRepr X Rs 1]
    {I : Type*} {nI irank ishape} [TensorIndexType I nI irank ishape]
    {J : Type*} {nJ jrank jshape} [TensorIndexType J nJ jrank jshape]
    {K : Type*} {nK krank kshape} [TensorIndexType K nK krank kshape]

    {IX : Type*} {nIX ixrank ixshape} [TensorIndexType IX nIX ixrank ixshape]
    {IA : Type*} {nIA iarank iashape} [TensorIndexType IA nIA iarank iashape]
    {IY : Type*} {nIY iyrank iyshape} [TensorIndexType IY nIY iyrank iyshape]
    {IB : Type*} {nIB ibrank ibshape} [TensorIndexType IB nIB ibrank ibshape]
    {IC : Type*} {nIC icrank icshape} [TensorIndexType IC nIC icrank icshape]



section MatrixOperations

namespace InjectiveView



-- x *ᵥ A + y
def vecMatMulAdd (x : View X I IX) (A : View X (I × J) IA) (y : InjectiveView X J IY) :
    InjectiveView X J IY :=
  let xmap := x.layout.linearize
  let swap : Layout (jshape.prod ishape) (ishape.prod jshape) :=
    (FinHTupleMap.sndMap jshape ishape).prod (FinHTupleMap.fstMap jshape ishape)
  let amap := (A.layout.comp swap).linearize
  let ymap := y.layout.linearize
  have hix := TensorIndexTypeOfRank.size_eq_shape_size (I := IX) (rank:= ixrank)
  have hia := TensorIndexTypeOfRank.size_eq_shape_size (I := IA) (rank:= iarank)
  have hiy := TensorIndexTypeOfRank.size_eq_shape_size (I := IY) (rank:= iyrank)
  let data := TensorRingOps.tensorGemv (1 : R) 1
    A.data.data (amap.cast _ _ rfl (by simp [← hia]))
    x.data.data (xmap.cast _ _ rfl (by simp [← hix]))
    y.data.data (ymap.cast _ _ rfl (by simp [← hiy])) sorry
  { data := {data}, layout := y.layout, injective := y.injective }


-- A *ᵥ y + x
def matVecMulAdd (A : View X (I × J) IA) (y : View X J IY) (x : InjectiveView X I IX) :
    InjectiveView X I IX :=
  let amap := A.layout.linearize
  let ymap := y.layout.linearize
  let xmap := x.layout.linearize
  have hia := TensorIndexTypeOfRank.size_eq_shape_size (I := IA) (rank:= iarank)
  have hiy := TensorIndexTypeOfRank.size_eq_shape_size (I := IY) (rank:= iyrank)
  have hix := TensorIndexTypeOfRank.size_eq_shape_size (I := IX) (rank:= ixrank)
  let data := TensorRingOps.tensorGemv (1 : R) 1
    A.data.data (amap.cast _ _ rfl (by simp [← hia]))
    y.data.data (ymap.cast _ _ rfl (by simp [← hiy]))
    x.data.data (xmap.cast _ _ rfl (by simp [← hix])) sorry
  { data := {data}, layout := x.layout, injective := x.injective }


-- A *ᵥ B + C
def matMulAdd (A : View X (I × J) IA) (B : View X (J × K) IB) (C : InjectiveView X (I × K) IC) :
    InjectiveView X (I × K) IC :=
  let amap := A.layout.linearize
  let bmap := B.layout.linearize
  let cmap := C.layout.linearize
  have hia := TensorIndexTypeOfRank.size_eq_shape_size (I := IA) (rank:= iarank)
  have hib := TensorIndexTypeOfRank.size_eq_shape_size (I := IB) (rank:= ibrank)
  have hic := TensorIndexTypeOfRank.size_eq_shape_size (I := IC) (rank:= icrank)
  let data := TensorRingOps.tensorGemm (1 : R) 1
    A.data.data (amap.cast _ _ rfl (by simp [← hia]))
    B.data.data (bmap.cast _ _ rfl (by simp [← hib]))
    C.data.data (cmap.cast _ _ rfl (by simp [← hic])) sorry
  { data := {data}, layout := C.layout, injective := C.injective }



end InjectiveView

namespace View

def vecMatMul (x : View X I IX) (A : View X (I × J) IA) : Tensor X J :=
  let dst : InjectiveView X J J :=
    { data := { data := VectorType.replicate (As := Rs) (nJ * 1) (0 : R) }
      layout := .id jshape
      injective := by grind }
  (InjectiveView.vecMatMulAdd x A dst).data

def matVecMul (A : View X (I × J) IA) (y : View X J IY) : Tensor X I :=
  let dst : InjectiveView X I I :=
    { data := { data := VectorType.replicate (As := Rs) (nI * 1) (0 : R) }
      layout := .id ishape
      injective := by grind }
  (InjectiveView.matVecMulAdd A y dst).data

def matMul (A : View X (I × J) IA) (B : View X (J × K) IB) : Tensor X (I × K) :=
  let dst : InjectiveView X (I × K) (I × K) :=
    { data := { data := VectorType.replicate (As := Rs) ((nI * nK) * 1) (0 : R) }
      layout := .id (ishape.prod kshape)
      injective := by grind }
  (InjectiveView.matMulAdd A B dst).data


-- View / View

-- vector matrix product
instance : VMul (View X I IX) (View X (I × J) IA) (Tensor X J) where
  vmul x A := vecMatMul x A

-- matrix vector product
instance : VMul (View X (I × J) IA) (View X J IY) (Tensor X I) where
  vmul A y := matVecMul A y

-- matrix matrix product
instance : VMul (View X (I × J) IA) (View X (J × K) IB) (Tensor X (I × K)) where
  vmul A B := matMul A B


-- Tensor / View

-- vector matrix product
instance : VMul (Tensor X I) (View X (I × J) IA) (Tensor X J) where
  vmul x A := vecMatMul ({ data := x, layout := .id ishape } : View X I I) A

-- vector matrix product
instance : VMul (View X I IX) (Tensor X (I × J)) (Tensor X J) where
  vmul x A := vecMatMul x ({ data := A, layout := .id (ishape.prod jshape) } : View X (I × J) (I × J))

-- matrix vector product
instance : VMul (View X (I × J) IA) (Tensor X J) (Tensor X I) where
  vmul A y := matVecMul A ({ data := y, layout := .id jshape } : View X J J)


-- Tensor / View

-- matrix vector product
instance : VMul (Tensor X (I × J)) (View X J IY) (Tensor X I) where
  vmul A y := matVecMul ({ data := A, layout := .id (ishape.prod jshape) } : View X (I × J) (I × J)) y

-- matrix matrix product
instance : VMul (Tensor X (I × J)) (View X (J × K) IB) (Tensor X (I × K)) where
  vmul A B := matMul ({ data := A, layout := .id (ishape.prod jshape) } : View X (I × J) (I × J)) B

-- matrix matrix product
instance : VMul (View X (I × J) IA) (Tensor X (J × K)) (Tensor X (I × K)) where
  vmul A B := matMul A ({ data := B, layout := .id (jshape.prod kshape) } : View X (J × K) (J × K))

end View

end MatrixOperations
