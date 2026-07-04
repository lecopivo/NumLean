module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval
public meta import Lean.Widget.UserWidget
public import Qq
public import NumLean.Meta.Visualize.Visualizers

@[expose] public section

namespace NumLean

open Lean Server Elab Command ProofWidgets

/-- Generic visualization command.

Examples:
```lean
#visualize hp(•,(•,•))
#visualize #[hp(•,•), hp(•,(•,•))]
#visualize (Visualize.latex "x + y", Visualize.latex "x - y")
#visualize with aspect := 1 / 1 hp(•,(•,•))
#visualize with maxHeightRatio := 2 hp(•,(•,•))
```
-/
syntax (name := visualizeAspectCmd) (priority := high) "#visualize" "with" "aspect" ":=" num "/" num term : command
syntax (name := visualizeMaxHeightCmd) (priority := high) "#visualize" "with" "maxHeightRatio" ":=" num term : command
syntax (name := visualizeCmd) (priority := low) "#visualize" term : command

open Meta Elab Term Qq in
private meta def natLit (stx : TSyntax `num) : CommandElabM Nat := do
  match stx.raw.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected natural number literal"

private meta def wrapProps (rpc : Json) (options : List (String × Json)) : Json :=
  if options.isEmpty then rpc
  else Json.mkObj [
    ("numleanVisualizeOptions", Json.mkObj options),
    ("item", rpc)]

open Meta Elab Term Qq in
private meta def visualizeTerm (stx : Syntax) (x : Term) (options : List (String × Json)) : CommandElabM Unit := do
  let (rpcM, js) ← liftTermElabM <| do
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
    let rpcM ← unsafe evalExpr (StateM RpcObjectStore Json) q(StateM RpcObjectStore Json) rpcExpr
    let js ← unsafe evalExpr String q(String) jsExpr
    pure (rpcM, js)
  liftCoreM <| Lean.Widget.savePanelWidgetInfo
    (hash js)
    (rpcM.map fun rpc => wrapProps rpc options)
    stx

@[command_elab visualizeCmd]
meta def elabVisualize : CommandElab := fun stx => do
  match stx with
  | `(#visualize $x:term) => visualizeTerm stx x []
  | _ => throwUnsupportedSyntax

@[command_elab visualizeAspectCmd]
meta def elabVisualizeAspect : CommandElab := fun stx => do
  match stx with
  | `(#visualize with aspect := $w:num / $h:num $x:term) => do
      let w ← natLit w
      let h ← natLit h
      if w == 0 || h == 0 then
        throwErrorAt stx "aspect ratio components must be positive"
      visualizeTerm stx x [("aspectRatio", toJson (w, h))]
  | _ => throwUnsupportedSyntax

@[command_elab visualizeMaxHeightCmd]
meta def elabVisualizeMaxHeight : CommandElab := fun stx => do
  match stx with
  | `(#visualize with maxHeightRatio := $ratio:num $x:term) => do
      let ratio ← natLit ratio
      if ratio == 0 then
        throwErrorAt stx "maxHeightRatio must be positive"
      visualizeTerm stx x [("maxHeightRatio", toJson ratio)]
  | _ => throwUnsupportedSyntax

end NumLean
