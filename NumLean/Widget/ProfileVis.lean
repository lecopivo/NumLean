import Lean.Elab.Command
import Lean.Server.Rpc.Basic
import ProofWidgets.Component.Basic
import Qq
import NumLean.Data.HTuple.Basic

namespace NumLean
namespace Widget

open Lean Server Elab Command ProofWidgets

structure ProfileVisProps where
  profile : String := "(•,(•,(•,•)))"
  deriving RpcEncodable

namespace ProfileVis

def toBracketString : HTuple.Profile → String
  | .leaf => "•"
  | .prod left right => "(" ++ toBracketString left ++ "," ++ toBracketString right ++ ")"

def propsOfProfile (profile : HTuple.Profile) : ProfileVisProps where
  profile := toBracketString profile

end ProfileVis

@[widget_module]
def HTupleProfileVis : Component ProfileVisProps where
  javascript := (include_str "js" / "profileVis.js") ++ "\n/* htuple-profile-vis-v6 */"

/-- Display an `HTuple.Profile` as bracket notation and as a binary tree. -/
syntax (name := htupleProfileVisCmd) "#profile_vis" (term)? : command

open Meta Elab Term Qq in
@[command_elab htupleProfileVisCmd]
def elabHTupleProfileVis : CommandElab := fun stx => do
  let props ←
    match stx with
    | `(#profile_vis $x:term) => do
      let expr ← liftTermElabM <| elabTerm x q(HTuple.Profile)
      let profile ← liftTermElabM <| unsafe evalExpr HTuple.Profile q(HTuple.Profile) expr
      pure (ProfileVis.propsOfProfile profile)
    | `(#profile_vis) => pure { : ProfileVisProps }
    | _ => throwUnsupportedSyntax
  liftCoreM <| Lean.Widget.savePanelWidgetInfo
    (hash HTupleProfileVis.javascript)
    (rpcEncode props)
    stx

end Widget
end NumLean
