import NumLean.Meta.Visualize
import NumLean.Misc.CuTe

namespace NumLean

open Lean Server

/-- Visual data for an `HTuple.Profile` binary tree. -/
structure ProfileVisProps where
  profile : String := "(•,(•,(•,•)))"
  deriving RpcEncodable, ToJson, FromJson

namespace ProfileVis

def toBracketString : HTuple.Profile → String
  | .leaf => "•"
  | .prod left right => "(" ++ toBracketString left ++ "," ++ toBracketString right ++ ")"

def propsOfProfile (profile : HTuple.Profile) : ProfileVisProps where
  profile := toBracketString profile

end ProfileVis

/-- Visual data for a CUTE layout table.

`values` are row-major, length `rows * cols`. This representation is intentionally concrete: the
widget visualizes an already-evaluated layout table, so it can also display hierarchical or
otherwise non-flat layouts whose values were computed elsewhere. -/
structure CuteLayoutVisProps where
  title : String := "CUTE layout"
  shape : String := "(4, 8)"
  stride : String := "(1, 4)"
  rows : Nat := 4
  cols : Nat := 8
  values : Array Int := #[0,4,8,12,16,20,24,28, 1,5,9,13,17,21,25,29, 2,6,10,14,18,22,26,30, 3,7,11,15,19,23,27,31]
  labels : Array String := #[]
  deriving RpcEncodable, ToJson, FromJson

/-- Visual data for a CUTE slicing diagram.

`sourceValues` and `sliceValues` are row-major. `selected` contains row-major indices into the
source grid that belong to the slice. -/
structure CuteSliceVisProps where
  title : String := "CUTE slice"
  sourceLayout : String := "((3, 2), ((2, 3), 2)) : ((4, 1), ((2, 15), 100))"
  sliceExpr : String := "A(2, _)"
  slicedLayout : String := "{8} ◦ ((2, 3), 2) : ((2, 15), 100)"
  sourceRows : Nat := 6
  sourceCols : Nat := 12
  sourceValues : Array Int := #[
    0,2,15,17,30,32,100,102,115,117,130,132,
    4,6,19,21,34,36,104,106,119,121,134,136,
    8,10,23,25,38,40,108,110,123,125,138,140,
    1,3,16,18,31,33,101,103,116,118,131,133,
    5,7,20,22,35,37,105,107,120,122,135,137,
    9,11,24,26,39,41,109,111,124,126,139,141]
  selected : Array Nat := #[24,25,26,27,28,29,30,31,32,33,34,35]
  sliceRows : Nat := 1
  sliceCols : Nat := 12
  sliceValues : Array Int := #[8,10,23,25,38,40,108,110,123,125,138,140]
  sliceLabels : Array String := #[]
  deriving RpcEncodable, ToJson, FromJson

namespace CuteVis

open NumLean.Cute

/-- A total colexicographical coordinate decoder used for visualization. -/
def coordOfLinear : {p : Profile} → (shape : Shape p) → Nat → HTuple Nat p
  | .leaf, _shape, i => .leaf i
  | .prod _ _, .prod shape₀ shape₁, i =>
      let n₀ := Shape.size shape₀
      .prod (coordOfLinear shape₀ (i % n₀)) (coordOfLinear shape₁ (i / n₀))

def evalRaw {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p : Profile} {shape : Shape p} (layout : Layout shape D) (coord : HTuple Nat p) : D :=
  layout.offset + coord.inner layout.stride

def layoutTable {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p q : Profile} {shape₀ : Shape p} {shape₁ : Shape q}
    (layout : Layout (.prod shape₀ shape₁) D) : Array D :=
  let rows := Shape.size shape₀
  let cols := Shape.size shape₁
  (Array.range (rows * cols)).map fun i =>
    let row := i / cols
    let col := i % cols
    evalRaw layout (.prod (coordOfLinear shape₀ row) (coordOfLinear shape₁ col))

def layoutVisPropsOfLayout {D : Type u} [Zero D] [Add D] [SMul Nat D]
    {p q : Profile} {shape₀ : Shape p} {shape₁ : Shape q}
    (title shape stride : String) (layout : Layout (.prod shape₀ shape₁) D)
    (color : Nat → D → Int) (label : D → String) : CuteLayoutVisProps :=
  let rows := Shape.size shape₀
  let cols := Shape.size shape₁
  let vals := layoutTable layout
  { title := title
    shape := shape
    stride := stride
    rows := rows
    cols := cols
    values := vals.mapIdx color
    labels := vals.map label }

def intLayoutVisProps {p q : Profile} {shape₀ : Shape p} {shape₁ : Shape q}
    (title shape stride : String) (layout : Layout (.prod shape₀ shape₁) Int) : CuteLayoutVisProps :=
  layoutVisPropsOfLayout title shape stride layout (fun _ x => x) toString

end CuteVis

namespace Visualize

def cuteShapeString : {p : Cute.Profile} → Cute.Shape p → String
  | .leaf, .leaf n => toString n
  | .prod _ _, .prod left right =>
      "(" ++ cuteShapeString left ++ "," ++ cuteShapeString right ++ ")"

/-- Wrapper requesting the recursive high-rank tensor visualizer for a CUTE layout. -/
structure HighRankLayout {p : Cute.Profile} (shape : Cute.Shape p) where
  layout : Cute.Layout shape Int

def highRankLayout {p : Cute.Profile} {shape : Cute.Shape p}
    (layout : Cute.Layout shape Int) : HighRankLayout shape where
  layout := layout

def highRankLayoutValues {p : Cute.Profile} {shape : Cute.Shape p}
    (layout : Cute.Layout shape Int) : Array Int :=
  (Array.range (Cute.Shape.size shape)).map fun i =>
    CuteVis.evalRaw layout (CuteVis.coordOfLinear shape i)

end Visualize

instance : Visualizer CuteLayoutVisProps where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance : Visualizer CuteSliceVisProps where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance : Visualizer ProfileVisProps where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance : Visualizable HTuple.Profile ProfileVisProps where
  toVis profile := ProfileVis.propsOfProfile profile

instance {p : Cute.Profile} : Visualizable (Cute.Shape p) Visualize.BinaryTreeVis where
  toVis shape := { tree := Visualize.cuteShapeString shape }

instance {α} {β : α → Type u} [inst : ∀ a, Visualizable (β a) vis] :
    Visualizable ((a : α) × β a) vis where
  toVis xs := (inst xs.1).toVis xs.2

instance {p : Cute.Profile} {shape : Cute.Shape p} :
    Visualizable (Cute.Layout shape Int) Visualize.HighRankTensorVis where
  toVis layout :=
    let vals := Visualize.highRankLayoutValues layout
    { shape := Visualize.cuteShapeString shape, values := vals, labels := vals.map toString }

instance {p : Cute.Profile} {shape : Cute.Shape p} :
    Visualizable (Visualize.HighRankLayout shape) Visualize.HighRankTensorVis where
  toVis x :=
    let vals := Visualize.highRankLayoutValues x.layout
    { shape := Visualize.cuteShapeString shape, values := vals, labels := vals.map toString }

end NumLean
