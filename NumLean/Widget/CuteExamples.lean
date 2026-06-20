import NumLean.Widget.Visualize

namespace NumLean
namespace Widget
namespace CuteExamples

open NumLean.Cute
open NumLean.Widget.CuteVis

/-! ## Figure 3 -/

def fig3a : CuteLayoutVisProps := intLayoutVisProps "Figure 3a: Col-major" "(4, 8)" "(1, 4)"
  ({ offset := 0, stride := h((1 : Int), (4 : Int)) } : Layout h((4 : Nat), (8 : Nat)) Int)

#visualize fig3a

def fig3b : CuteLayoutVisProps := intLayoutVisProps "Figure 3b: Row-major" "(4, 8)" "(8, 1)"
  ({ offset := 0, stride := h((8 : Int), (1 : Int)) } : Layout h((4 : Nat), (8 : Nat)) Int)

#visualize fig3b

def fig3c : CuteLayoutVisProps := intLayoutVisProps "Figure 3c: Col-major padded" "(4, 8)" "(1, 5)"
  ({ offset := 0, stride := h((1 : Int), (5 : Int)) } : Layout h((4 : Nat), (8 : Nat)) Int)

#visualize fig3c

def fig3d : CuteLayoutVisProps := intLayoutVisProps "Figure 3d: Col-major interleave" "(4, (4, 2))" "(4, (1, 16))"
  ({ offset := 0, stride := h((4 : Int), ((1 : Int), (16 : Int))) } :
    Layout h((4 : Nat), ((4 : Nat), (2 : Nat))) Int)

#visualize fig3d

def fig3e : CuteLayoutVisProps := intLayoutVisProps "Figure 3e: Mixed" "((2, 2), (4, 2))" "((1, 8), (2, 16))"
  ({ offset := 0, stride := h(((1 : Int), (8 : Int)), ((2 : Int), (16 : Int))) } :
    Layout h(((2 : Nat), (2 : Nat)), ((4 : Nat), (2 : Nat))) Int)

#visualize fig3e

def fig3f : CuteLayoutVisProps := intLayoutVisProps "Figure 3f: Blocked broadcast" "((2, 2), (2, 4))" "((0, 2), (0, 4))"
  ({ offset := 0, stride := h(((0 : Int), (2 : Int)), ((0 : Int), (4 : Int))) } :
    Layout h(((2 : Nat), (2 : Nat)), ((2 : Nat), (4 : Nat))) Int)

#visualize fig3f

/-! ## Figure 4 -/

def e0 : HTuple Nat hp(•, •) := h((1 : Nat), (0 : Nat))
def e1 : HTuple Nat hp(•, •) := h((0 : Nat), (1 : Nat))

def fig4a : CuteLayoutVisProps := reprLayoutVisProps "Figure 4a: Identity coordinate" "(4, 8)" "(e₀, e₁)"
  ({ offset := 0, stride := h(e0, e1) } :
    Layout h((4 : Nat), (8 : Nat)) (HTuple Nat hp(•, •)))

#visualize fig4a

def fig4b : CuteLayoutVisProps := reprLayoutVisProps "Figure 4b: Transposed block coordinate" "(4, (4, 2))" "(e₁, (e₀, 6e₁))"
  ({ offset := 0, stride := h(e1, (e0, (6 : Nat) • e1)) } :
    Layout h((4 : Nat), ((4 : Nat), (2 : Nat))) (HTuple Nat hp(•, •)))

#visualize fig4b

/-- Bit-mask values with XOR addition and parity scalar multiplication, modeling the paper's `F₂` strides. -/
structure F2Mask where
  val : Nat
  deriving Repr

instance : Zero F2Mask where
  zero := ⟨0⟩

instance : Add F2Mask where
  add a b := ⟨Nat.xor a.val b.val⟩

instance : SMul Nat F2Mask where
  smul n a := if n % 2 = 0 then 0 else a

def f1 : F2Mask := ⟨1⟩
def f5 : F2Mask := ⟨5⟩
def f16 : F2Mask := ⟨16⟩

def f2Label (x : F2Mask) : String := toString x.val

def fig4c : CuteLayoutVisProps := layoutVisPropsOfLayout "Figure 4c: Binary swizzle" "(4, (4, 3))" "(f₁, (f₅, f₁₆))"
  ({ offset := 0, stride := h(f1, (f5, f16)) } :
    Layout h((4 : Nat), ((4 : Nat), (3 : Nat))) F2Mask)
  (fun _ x => Int.ofNat x.val)
  f2Label

#visualize fig4c

/-! ## Figure 5 -/

def fig5RowShape : Shape hp(•, •) := h((3 : Nat), (2 : Nat))
def fig5ColShape : Shape hp((•, •), •) := h(((2 : Nat), (3 : Nat)), (2 : Nat))
def fig5SourceShape : Shape hp((•, •), ((•, •), •)) := HTuple.prod fig5RowShape fig5ColShape

def fig5SourceLayout : Layout fig5SourceShape Int where
  offset := 0
  stride := h(((4 : Int), (1 : Int)), (((2 : Int), (15 : Int)), (100 : Int)))

def fig5Props {p q : Profile} {targetRowsShape : Shape p} {targetColsShape : Shape q}
    (sliceExpr slicedLayout : String)
    (slice : Slice fig5SourceShape (.prod targetRowsShape targetColsShape)) : CuteSliceVisProps :=
  sliceVisPropsOfSlice ("Figure 5: " ++ sliceExpr)
    "{0} ◦ ((3, 2), ((2, 3), 2)) : ((4, 1), ((2, 15), 100))"
    sliceExpr slicedLayout fig5SourceLayout slice

def fig5SliceA : Slice fig5SourceShape h((1 : Nat), (12 : Nat)) where
  source
    | .prod _ (.leaf c) => .prod (coordOfLinear fig5RowShape 2) (coordOfLinear fig5ColShape c)

def fig5a : CuteSliceVisProps := fig5Props "A(2, _)" "{8} ◦ ((2, 3), 2) : ((2, 15), 100)" fig5SliceA

#visualize fig5a

def fig5SliceB : Slice fig5SourceShape h((6 : Nat), (1 : Nat)) where
  source
    | .prod (.leaf r) _ => .prod (coordOfLinear fig5RowShape r) (coordOfLinear fig5ColShape 5)

def fig5b : CuteSliceVisProps := fig5Props "A(_, 5)" "{32} ◦ (3, 2) : (4, 1)" fig5SliceB

#visualize fig5b

def fig5SliceC : Slice fig5SourceShape h((3 : Nat), (2 : Nat)) where
  source
    | .prod (.leaf b) (.leaf c) => .prod (coordOfLinear fig5RowShape 2) h(((0 : Nat), b), c)

def fig5c : CuteSliceVisProps := fig5Props "A(2, ((0, _), _))" "{8} ◦ (3, 2) : (15, 100)" fig5SliceC

#visualize fig5c

def fig5SliceD : Slice fig5SourceShape h((3 : Nat), ((2 : Nat), (3 : Nat))) where
  source
    | .prod (.leaf r) col => .prod h(r, (1 : Nat)) (.prod col (.leaf 0))

def fig5d : CuteSliceVisProps := fig5Props "A((_, 1), (_, 0))" "{1} ◦ (3, (2, 3)) : (4, (2, 15))" fig5SliceD

#visualize fig5d

def fig5SliceE : Slice fig5SourceShape h((3 : Nat), (3 : Nat)) where
  source
    | .prod (.leaf r) (.leaf b) => .prod h(r, (0 : Nat)) h(((0 : Nat), b), (1 : Nat))

def fig5e : CuteSliceVisProps := fig5Props "A((_, 0), ((0, _), 1))" "{100} ◦ (3, 3) : (4, 15)" fig5SliceE

#visualize fig5e

def fig5SliceF : Slice fig5SourceShape h((2 : Nat), ((2 : Nat), (2 : Nat))) where
  source
    | .prod (.leaf r) (.prod (.leaf a) (.leaf b)) => .prod h((1 : Nat), r) h((a, (0 : Nat)), b)

def fig5f : CuteSliceVisProps := fig5Props "A((1, _), ((_, 0), _))" "{4} ◦ (2, (2, 2)) : (1, (2, 100))" fig5SliceF

#visualize fig5f

end CuteExamples
end Widget
end NumLean
