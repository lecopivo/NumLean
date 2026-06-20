import Lean.Elab.Command
import Lean.Server.Rpc.Basic
import ProofWidgets.Component.Basic
import Qq
import NumLean.Widget.ProfileVis
import NumLean.Widget.CuteVis

namespace NumLean
namespace Widget

open Lean Server Elab Command ProofWidgets

/-- Generic bridge from Lean objects to ProofWidgets visualizations.

`Props` is the concrete data structure consumed by the widget.  The command evaluates objects
through `toProps`, encodes the props as RPC JSON, and loads `javascript` as the widget module. -/
class Visualizable (α : Type u) (Props : outParam (Type v)) where
  javascript : String
  toProps : α → Props
  encodeProps : Props → StateM RpcObjectStore Json

namespace Visualize

def javascript : String := (include_str "js" / "visualize.js") ++ "\n/* numlean-visualize-v17 */"

@[widget_module]
def Component : ProofWidgets.Component Json where
  javascript := javascript

def str (s : String) : Json := Json.str s

def obj (fields : List (String × Json)) : Json := Json.mkObj fields

def profileItem (props : ProfileVisProps) : Json :=
  obj [("kind", str "profile"), ("profile", str props.profile)]

def layoutItem (props : CuteLayoutVisProps) : Json :=
  obj [ ("kind", str "highRankLayout")
      , ("shape", str props.shape)
      , ("values", toJson props.values)
      , ("labels", toJson props.labels) ]

def highRankLayoutItem (shape : String) (values : Array Int) (labels : Array String) : Json :=
  obj [ ("kind", str "highRankLayout")
      , ("shape", str shape)
      , ("values", toJson values)
      , ("labels", toJson labels) ]

def sliceItem (props : CuteSliceVisProps) : Json :=
  obj [ ("kind", str "slice")
      , ("sourceRows", toJson props.sourceRows)
      , ("sourceCols", toJson props.sourceCols)
      , ("sourceValues", toJson props.sourceValues)
      , ("selected", toJson props.selected)
      , ("sliceRows", toJson props.sliceRows)
      , ("sliceCols", toJson props.sliceCols)
      , ("sliceValues", toJson props.sliceValues)
      , ("sliceLabels", toJson props.sliceLabels) ]

def shapeString : {p : Cute.Profile} → Cute.Shape p → String
  | .leaf, .leaf n => toString n
  | .prod _ _, .prod left right => "(" ++ shapeString left ++ "," ++ shapeString right ++ ")"

def shapeItem {p : Cute.Profile} (shape : Cute.Shape p) : Json :=
  obj [ ("kind", str "shape")
      , ("shape", str (shapeString shape)) ]

/-- Wrapper requesting the recursive high-rank layout visualizer for a CUTE layout. -/
structure HighRankLayout {p : Cute.Profile} (shape : Cute.Shape p) where
  layout : Cute.Layout shape Int

def highRankLayout {p : Cute.Profile} {shape : Cute.Shape p}
    (layout : Cute.Layout shape Int) : HighRankLayout shape where
  layout := layout

def highRankLayoutValues {p : Cute.Profile} {shape : Cute.Shape p}
    (layout : Cute.Layout shape Int) : Array Int :=
  (Array.range (Cute.Shape.size shape)).map fun i =>
    CuteVis.evalRaw layout (CuteVis.coordOfLinear shape i)

/-- Layout options for product visualizations.  Values are CSS alignment keywords. -/
structure ProdOptions where
  alignItems : String := "start"
  justifyItems : String := "stretch"
  gap : Nat := 10

/-- Explicit product wrapper for overriding the default side-by-side box layout. -/
structure ProdBox (α : Type u) (β : Type v) where
  options : ProdOptions := {}
  left : α
  right : β

def prodBox (left : α) (right : β) (options : ProdOptions := {}) : ProdBox α β where
  options := options
  left := left
  right := right

def prodItem (left right : Json) (options : ProdOptions := {}) : Json :=
  obj [ ("kind", str "prod")
      , ("left", left)
      , ("right", right)
      , ("alignItems", str options.alignItems)
      , ("justifyItems", str options.justifyItems)
      , ("gap", toJson options.gap) ]

def flowItem (items : Array Json) : Json :=
  obj [("kind", str "flow"), ("items", Json.arr items)]

def gridItem (rows : Array (Array Json)) : Json :=
  obj [("kind", str "grid"), ("rows", Json.arr (rows.map Json.arr))]

end Visualize

namespace Visualizable

def toRpc {α : Type u} {Props : Type v} [v : Visualizable α Props]
    (x : α) : StateM RpcObjectStore Json :=
  v.encodeProps (v.toProps x)

def javascriptFor {α : Type u} {Props : Type v} [Visualizable α Props] (_x : α) : String :=
  Visualizable.javascript (α := α) (Props := Props)

end Visualizable

instance : Visualizable ProfileVisProps Json where
  javascript := Visualize.javascript
  toProps := Visualize.profileItem
  encodeProps := pure

instance : Visualizable HTuple.Profile Json where
  javascript := Visualize.javascript
  toProps profile := Visualize.profileItem (ProfileVis.propsOfProfile profile)
  encodeProps := pure

instance {p : Cute.Profile} : Visualizable (Cute.Shape p) Json where
  javascript := Visualize.javascript
  toProps := Visualize.shapeItem
  encodeProps := pure

instance {α} {β : α → Type u} [Inhabited α] [inst : ∀ a, Visualizable (β a) prop] :
    Visualizable ((a : α) × β a) prop where
  javascript := (inst default).javascript
  toProps xs := (inst xs.1).toProps xs.2
  encodeProps := (inst default).encodeProps

instance : Visualizable CuteLayoutVisProps Json where
  javascript := Visualize.javascript
  toProps := Visualize.layoutItem
  encodeProps := pure

instance : Visualizable CuteSliceVisProps Json where
  javascript := Visualize.javascript
  toProps := Visualize.sliceItem
  encodeProps := pure

instance {p : Cute.Profile} {shape : Cute.Shape p} :
    Visualizable (Cute.Layout shape Int) Json where
  javascript := Visualize.javascript
  toProps layout :=
    let vals := Visualize.highRankLayoutValues layout
    Visualize.highRankLayoutItem (Visualize.shapeString shape) vals (vals.map toString)
  encodeProps := pure

instance {p : Cute.Profile} {shape : Cute.Shape p} :
    Visualizable (Visualize.HighRankLayout shape) Json where
  javascript := Visualize.javascript
  toProps x :=
    let vals := Visualize.highRankLayoutValues x.layout
    Visualize.highRankLayoutItem (Visualize.shapeString shape) vals (vals.map toString)
  encodeProps := pure

instance (priority := low) {α : Type u} [v : Visualizable α Json] :
    Visualizable (Array α) Json where
  javascript := Visualize.javascript
  toProps xs := Visualize.flowItem (xs.map v.toProps)
  encodeProps := pure

instance (priority := high) {α : Type u} [v : Visualizable α Json] :
    Visualizable (Array (Array α)) Json where
  javascript := Visualize.javascript
  toProps rows := Visualize.gridItem (rows.map fun xs => xs.map v.toProps)
  encodeProps := pure

instance {α : Type u} {β : Type v} [va : Visualizable α Json] [vb : Visualizable β Json] :
    Visualizable (α × β) Json where
  javascript := Visualize.javascript
  toProps x := Visualize.prodItem (va.toProps x.1) (vb.toProps x.2)
  encodeProps := pure

instance {α : Type u} {β : Type v} [va : Visualizable α Json] [vb : Visualizable β Json] :
    Visualizable (Visualize.ProdBox α β) Json where
  javascript := Visualize.javascript
  toProps x := Visualize.prodItem (va.toProps x.left) (vb.toProps x.right) x.options
  encodeProps := pure

/-- Generic visualization command.

Examples:
```lean
#visualize hp(•,(•,•))
#visualize #[hp(•,•), hp(•,(•,•))]
#visualize (hp(•,•), ({ offset := 0, stride := h((1 : Int), (4 : Int)) } :
  Cute.Layout h((4 : Nat), (8 : Nat)) Int))
```
-/
syntax (name := visualizeCmd) "#visualize" term : command

open Meta Elab Term Qq in
@[command_elab visualizeCmd]
def elabVisualize : CommandElab := fun stx => do
  match stx with
  | `(#visualize $x:term) => do
      let (rpc, js) ← liftTermElabM <| do
        let xExpr ← instantiateMVars (← elabTermAndSynthesize x none)
        let xTy ← instantiateMVars (← inferType xExpr)
        let propsTy ← mkFreshTypeMVar
        let instType := mkAppN (← mkConstWithFreshMVarLevels ``Visualizable) #[xTy, propsTy]
        let inst ← synthInstance instType
        let propsTy ← instantiateMVars propsTy
        let rpcExpr ← instantiateMVars (← mkAppOptM ``Visualizable.toRpc #[xTy, propsTy, inst, xExpr])
        let jsExpr ← instantiateMVars (← mkAppOptM ``Visualizable.javascriptFor #[xTy, propsTy, inst, xExpr])
        let rpc ← unsafe evalExpr (StateM RpcObjectStore Json) q(StateM RpcObjectStore Json) rpcExpr
        let js ← unsafe evalExpr String q(String) jsExpr
        pure (rpc, js)
      liftCoreM <| Lean.Widget.savePanelWidgetInfo
        (hash js)
        rpc
        stx
  | _ => throwUnsupportedSyntax

end Widget
end NumLean
