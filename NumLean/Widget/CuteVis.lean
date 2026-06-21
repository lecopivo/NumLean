import Lean.Elab.Command
import Lean.Server.Rpc.Basic
import ProofWidgets.Component.Basic
import Qq
import NumLean.Misc.CuTe

namespace NumLean
namespace Widget

open Lean Server Elab Command ProofWidgets

/-- Props for a Figure-3-style CUTE layout visualization.

`values` are row-major, length `rows * cols`.  This representation is intentionally concrete:
the widget visualizes an already-evaluated layout table, so it can also display hierarchical or
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

/-- Props for a Figure-5-style slicing visualization.

`sourceValues` and `sliceValues` are row-major.  `selected` contains row-major indices into the
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

/-- A total colexicographical coordinate decoder used for visualization.

The intended use is with valid row/column positions less than `Shape.size shape`. It is total so
the visualizer can remain proof-free. -/
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

def reprLayoutVisProps {D : Type u} [Zero D] [Add D] [SMul Nat D] [Repr D]
    {p q : Profile} {shape₀ : Shape p} {shape₁ : Shape q}
    (title shape stride : String) (layout : Layout (.prod shape₀ shape₁) D) : CuteLayoutVisProps :=
  layoutVisPropsOfLayout title shape stride layout (fun i _ => Int.ofNat i) (fun x => reprStr x)

def rawLinearIndex : {p : Profile} → (shape : Shape p) → HTuple Nat p → Nat
  | .leaf, _shape, .leaf i => i
  | .prod _ _, .prod shape₀ shape₁, .prod row col =>
      rawLinearIndex shape₀ row + Shape.size shape₀ * rawLinearIndex shape₁ col

def sliceVisPropsOfSlice {ps0 ps1 pt0 pt1 : Profile}
    {sourceRowsShape : Shape ps0} {sourceColsShape : Shape ps1}
    {targetRowsShape : Shape pt0} {targetColsShape : Shape pt1}
    (title sourceLayoutName sliceExpr slicedLayoutName : String)
    (sourceLayout : Layout (.prod sourceRowsShape sourceColsShape) Int)
    (slice : Slice (.prod sourceRowsShape sourceColsShape) (.prod targetRowsShape targetColsShape)) :
    CuteSliceVisProps :=
  let sourceRows := Shape.size sourceRowsShape
  let sourceCols := Shape.size sourceColsShape
  let targetRows := Shape.size targetRowsShape
  let targetCols := Shape.size targetColsShape
  let sourceValues := layoutTable sourceLayout
  let targetLinear := Array.range (targetRows * targetCols)
  let sourceCoords := targetLinear.map fun i =>
    let row := i / targetCols
    let col := i % targetCols
    let targetCoord := HTuple.prod (coordOfLinear targetRowsShape row) (coordOfLinear targetColsShape col)
    slice.source targetCoord
  let selected := sourceCoords.map fun coord =>
    match coord with
    | .prod row col =>
        -- Source panel is displayed with row coordinate as the outer grid row and column coordinate
        -- as the inner grid column.
        rawLinearIndex sourceRowsShape row * sourceCols + rawLinearIndex sourceColsShape col
  let sliceValues := sourceCoords.map fun coord => evalRaw sourceLayout coord
  { title := title
    sourceLayout := sourceLayoutName
    sliceExpr := sliceExpr
    slicedLayout := slicedLayoutName
    sourceRows := sourceRows
    sourceCols := sourceCols
    sourceValues := sourceValues
    selected := selected
    sliceRows := targetRows
    sliceCols := targetCols
    sliceValues := sliceValues }

end CuteVis

@[widget_module]
def CuteLayoutVis : Component CuteLayoutVisProps where
  javascript := (include_str "js" / "cuteVis.js") ++ "\n/* cute-layout-vis-v7 */"

@[widget_module]
def CuteSliceVis : Component CuteSliceVisProps where
  javascript := (include_str "js" / "cuteVis.js") ++ "\n/* cute-slice-vis-v7 */"

/-- Display a Figure-3-style CUTE layout heatmap. -/
syntax (name := cuteLayoutVisCmd) "#cute_layout_vis" (term)? : command

open Meta Elab Term Qq in
@[command_elab cuteLayoutVisCmd]
def elabCuteLayoutVis : CommandElab := fun stx => do
  let props ←
    match stx with
    | `(#cute_layout_vis $x:term) => do
      let props ← liftTermElabM <| elabTerm x q(CuteLayoutVisProps)
      liftTermElabM <| unsafe evalExpr CuteLayoutVisProps q(CuteLayoutVisProps) props
    | `(#cute_layout_vis) => pure { : CuteLayoutVisProps }
    | _ => throwUnsupportedSyntax
  liftCoreM <| Lean.Widget.savePanelWidgetInfo
    (hash CuteLayoutVis.javascript)
    (rpcEncode props)
    stx

/-- Display a Figure-5-style CUTE slicing visualization. -/
syntax (name := cuteSliceVisCmd) "#cute_slice_vis" (term)? : command

open Meta Elab Term Qq in
@[command_elab cuteSliceVisCmd]
def elabCuteSliceVis : CommandElab := fun stx => do
  let props ←
    match stx with
    | `(#cute_slice_vis $x:term) => do
      let props ← liftTermElabM <| elabTerm x q(CuteSliceVisProps)
      liftTermElabM <| unsafe evalExpr CuteSliceVisProps q(CuteSliceVisProps) props
    | `(#cute_slice_vis) => pure { : CuteSliceVisProps }
    | _ => throwUnsupportedSyntax
  liftCoreM <| Lean.Widget.savePanelWidgetInfo
    (hash CuteSliceVis.javascript)
    (rpcEncode props)
    stx

end Widget
end NumLean
