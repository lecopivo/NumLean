module

public import NumLean.Misc.CuTe.Visualize
public meta import NumLean.Misc.CuTe.Visualize
public meta import NumLean.Meta.Visualize.Visualizers

@[expose] public section

namespace NumLean
namespace VisualizeExamples

open NumLean.Cute

/-! Examples for the generic `#visualize` command.

The generic instances compose visualizations in Lean:

* `A × B` displays visualizations of `A` and `B` horizontally.
* `Array A` displays a responsive flow layout; the JavaScript picks the number of columns from
  the available widget width.
* `Array (Array A)` displays fixed rows: the outer array stacks vertically and each inner array
  lays out horizontally.
* `Visualize.animation` cycles through visualizations as animation frames.
* `Visualize.prodBox` is the explicit product wrapper when alignment options matter.
-/

variable (p : HTuple.Profile)
instance : Inhabited (HTuple.Profile) := ⟨.leaf⟩
instance [Inhabited α] (p) : Inhabited (HTuple α p) := ⟨.ofFn (fun _ => default)⟩

#visualize h((2, 2), (2, 2))
    |>.allCoarseningsMap (fun q => q.numel)
    |>.map (fun ⟨_,shape⟩ => (shape.eraseProfile, (Layout.rowMajor shape).eraseShape))
           |>.reverse

def profileA : HTuple.Profile := hp(•, •)
def profileB : HTuple.Profile := hp(•, (•, •))
def profileC : HTuple.Profile := hp((•, •), (•, •))

def shapeA : Shape hp(•, •) := h((4 : Nat), (8 : Nat))
def shapeB : Shape hp(•, (•, •)) := h((2 : Nat), ((4 : Nat), (2 : Nat)))

def colMajor : Layout h((4 : Nat), (8 : Nat)) Int where
  offset := 0
  stride := h((1 : Int), (4 : Int))

def rowMajor : Layout h((4 : Nat), (8 : Nat)) Int where
  offset := 0
  stride := h((8 : Int), (1 : Int))

def padded : Layout h((4 : Nat), (8 : Nat)) Int where
  offset := 0
  stride := h((1 : Int), (5 : Int))

def blocked4x4 : Layout h(((2 : Nat), (2 : Nat)), ((2 : Nat), (2 : Nat))) Int where
  offset := 0
  stride := h(((1 : Int), (2 : Int)), ((4 : Int), (8 : Int)))

def shape_2x2_by_2 : Layout h(((2 : Nat), (2 : Nat)), (2 : Nat)) Int where
  offset := 0
  stride := h(((1 : Int), (2 : Int)), (4 : Int))

def shape_2x2_2x2_by_2 : Layout h((((2 : Nat), (2 : Nat)), ((2 : Nat), (2 : Nat))), (2 : Nat)) Int where
  offset := 0
  stride := h((((1 : Int), (2 : Int)), ((4 : Int), (8 : Int))), (16 : Int))

def shape_4_by_2x2 : Layout h((4 : Nat), ((2 : Nat), (2 : Nat))) Int where
  offset := 0
  stride := h((1 : Int), ((4 : Int), (8 : Int)))

/-! Base objects. -/

#visualize Visualize.latex "\\sum_{i=0}^{n-1} x_i^2"

#visualize (hp(•, •), Visualize.latex "(i_1, i_2) \\mapsto i_1\\bullet (1,0) + i_2 \\bullet (0,1)")

#visualize Visualize.prodBox
  (Visualize.latex "A(i,j) \\mapsto i + n j")
  (Visualize.highRankLayout blocked4x4)
  { direction := .vertical
    weights := (1, 3)
    aspectRatio? := some (1, 1)
    alignItems := "stretch"
    justifyItems := "stretch"
    gap := 8 }

#visualize profileB
#visualize shapeB
#visualize colMajor

/-! A 4×4 layout whose row and column axes are both shaped `(2,2)`. -/

#visualize Layout.rowMajor h((2,2),(2,2))
#visualize Layout.rowMajor h(((2,2),(2,2)),2)
#visualize Layout.rowMajor h((2,2),((2,2),2))
#visualize Layout.rowMajor h(4,(2,2))

/-! High-rank layout visualization: `((m,a),(n,b))` is shown as an `(m,n)` matrix of stamped
`(a,b)` blocks, recursively. -/

#visualize (Visualize.highRankLayout blocked4x4)

#visualize (Visualize.highRankLayout shape_2x2_by_2)

#visualize (Visualize.highRankLayout shape_2x2_2x2_by_2)

#visualize (Visualize.highRankLayout shape_4_by_2x2)

/-! Product composition: two independently visualizable objects side by side. -/

#visualize (profileB, shapeB)

#visualize (profileA, colMajor)

#visualize ((profileA, shapeA), colMajor)

/-! Responsive array: Lean only says “these belong together”; JS chooses a useful grid. -/

#visualize #[profileA, profileB, profileC]

#visualize #[colMajor, rowMajor, padded]

#visualize Visualize.animation #[colMajor, rowMajor, padded] 700

#visualize (Layout.rowMajor h(2,(2,2),(2,10)))

#visualize blocked4x4

#visualize colMajor
#visualize colMajor

#visualize #[
  CuteVis.intLayoutVisProps "" "" "" colMajor,
  CuteVis.intLayoutVisProps "" "" "" blocked4x4,
  CuteVis.intLayoutVisProps "" "" "" rowMajor]

#visualize #[
  CuteVis.intLayoutVisProps "" "" "" shape_2x2_by_2,
  CuteVis.intLayoutVisProps "" "" "" shape_2x2_2x2_by_2,
  CuteVis.intLayoutVisProps "" "" "" blocked4x4,
  CuteVis.intLayoutVisProps "" "" "" shape_4_by_2x2]

#visualize #[(profileA, colMajor), (profileB, rowMajor), (profileC, padded)]

/-! Explicit 2D array: outer array is vertical, inner arrays are horizontal. -/

#visualize #[#[profileA, profileB], #[profileC]]

#visualize #[#[colMajor, rowMajor], #[padded]]

#visualize #[#[(profileA, colMajor), (profileB, rowMajor)], #[(profileC, padded)]]

/-! Product options: use an explicit wrapper when bounding-box alignment matters. -/

def centeredPair := Visualize.prodBox profileB colMajor
  { alignItems := "center", justifyItems := "stretch", gap := 18 }

#visualize centeredPair

def topAlignedPair := Visualize.prodBox shapeB rowMajor
  { alignItems := "start", justifyItems := "stretch", gap := 8 }

#visualize topAlignedPair

end VisualizeExamples
end NumLean
