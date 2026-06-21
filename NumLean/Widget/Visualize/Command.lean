import Lean.Elab.Command
import Qq
import NumLean.Widget.Visualize.Visualizers

namespace NumLean
namespace Widget

open Lean Server Elab Command ProofWidgets

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
        let visTy ← mkFreshTypeMVar
        let visInstType := mkAppN (← mkConstWithFreshMVarLevels ``Visualizable) #[xTy, visTy]
        let visInst ← synthInstance visInstType
        let visTy ← instantiateMVars visTy
        let rendererInstType := mkApp (← mkConstWithFreshMVarLevels ``Visualizer) visTy
        let rendererInst ← synthInstance rendererInstType
        let rpcExpr ← instantiateMVars
          (← mkAppOptM ``Visualizable.toRpc #[xTy, visTy, visInst, rendererInst, xExpr])
        let jsExpr ← instantiateMVars
          (← mkAppOptM ``Visualizable.javascriptFor #[xTy, visTy, visInst, rendererInst, xExpr])
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
