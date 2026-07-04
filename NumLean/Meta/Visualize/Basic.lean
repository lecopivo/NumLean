module

public import Lean.Server.Rpc.Basic
public import ProofWidgets.Component.Basic

@[expose] public section

namespace NumLean

open Lean Server ProofWidgets

/-- A concrete visual representation that knows which widget JavaScript renders it. -/
class Visualizer (α : Type u) where
  javascript : String
  encodeProps : α → StateM RpcObjectStore Json

/-- Convert a Lean value to visual data handled by a `Visualizer`. -/
class Visualizable (α : Type u) (vis : outParam (Type v)) where
  toVis : α → vis

namespace Visualize

def javascript : String :=
  (include_str ".." / ".." / ".." / "js" / "visualize.js") ++ "\n/* numlean-visualize-v50 */"

meta def javascriptMeta : String :=
  (include_str ".." / ".." / ".." / "js" / "visualize.js") ++ "\n/* numlean-visualize-v50 */"

@[widget_module]
meta def Component : ProofWidgets.Component Json where
  javascript := javascriptMeta

def str (s : String) : Json := Json.str s

def obj (fields : List (String × Json)) : Json := Json.mkObj fields

end Visualize

namespace Visualizer

def toRpc {α : Type u} [v : Visualizer α] (x : α) : StateM RpcObjectStore Json :=
  v.encodeProps x

def javascriptFor {α : Type u} [Visualizer α] (_x : α) : String :=
  Visualizer.javascript (α := α)

end Visualizer

namespace Visualizable

def toRpc {α : Type u} {vis : Type v} [Visualizable α vis] [Visualizer vis]
    (x : α) : StateM RpcObjectStore Json :=
  Visualizer.toRpc (Visualizable.toVis (vis := vis) x)

def javascriptFor {α : Type u} {vis : Type v} [Visualizable α vis] [Visualizer vis]
    (_x : α) : String :=
  Visualizer.javascript (α := vis)

end Visualizable

end NumLean
