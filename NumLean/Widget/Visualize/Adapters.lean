import NumLean.Widget.Visualize.Visualizers
import NumLean.Widget.ProfileVis
import NumLean.Widget.CuteVis

namespace NumLean
namespace Widget

open Lean Server

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

instance : Visualizer ProfileVisProps where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance : Visualizer CuteLayoutVisProps where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance : Visualizer CuteSliceVisProps where
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

end Widget
end NumLean
