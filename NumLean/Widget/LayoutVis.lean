import Lean.Elab.Command
import Lean.Server.Rpc.Basic
import ProofWidgets.Component.Basic
import Qq

namespace NumLean
namespace Widget

open Lean Server Elab Command ProofWidgets


structure LayoutVisProps where
  sourceShape : Array Nat := #[3,4]
  targetShape : Array Nat := #[6,7]
  base : Int := 15
  strides : Array Int := #[7,1]
  memorySize : Nat := 42
  deriving RpcEncodable

@[widget_module]
def LayoutVis : Component LayoutVisProps where
  javascript := (include_str "js" / "layoutVis.js") ++ "\n/* layout-vis-no-title-v16 */"

/--
Display the tensor layout visualizer in the infoview.

Syntax:
```lean
#layout_vis
```

For now this shows a fixed normal-tensor submatrix view of a `6x7` row-major matrix with
source shape `[3, 4]`, base offset `15`, and strides `[7, 1]`. Future versions will accept
explicit source shape, target shape, base, and stride values in the command syntax.
-/
syntax (name := layoutVisCmd) "#layout_vis" (term)? : command

open Meta Elab Term Qq in
@[command_elab layoutVisCmd]
def elabLayoutVis : CommandElab := fun stx => do
  let props ←
    match stx with
    | `(#layout_vis $x:term) => do
      let props ← liftTermElabM <| elabTerm x q(LayoutVisProps)
      let props ← liftTermElabM <| unsafe evalExpr LayoutVisProps q(LayoutVisProps) props
      pure props
    | `(#layout_vis) =>
      pure { : LayoutVisProps}
    | _ => throwUnsupportedSyntax
  liftCoreM <| Lean.Widget.savePanelWidgetInfo
    (hash LayoutVis.javascript)
    (rpcEncode props)
    stx

end Widget
end NumLean
