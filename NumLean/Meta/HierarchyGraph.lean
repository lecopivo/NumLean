module

public import Lean
public import Lean.Data.Json.FromToJson
public import NumLean.Meta.Visualize.Basic

@[expose] public section

namespace NumLean
namespace HierarchyGraph

open Lean Meta Elab Command Server ProofWidgets

inductive HierarchyEdgeKind where
  | extends
  | assumes
deriving Repr, BEq, Inhabited, ToJson, FromJson

structure HierarchyClassNode where
  name : Name
  label : String
  type : String
  tag? : Option Name
  tags : Array Name := #[]
deriving Repr, Inhabited, ToJson, FromJson

structure HierarchyClassEdge where
  source : Name
  target : Name
  kind : HierarchyEdgeKind
deriving Repr, Inhabited, ToJson, FromJson

structure HierarchyInstanceEdge where
  name : Name
  label : String
  inputs : Array Name
  output : Name
  type : String
  priority? : Option Nat
  tag? : Option Name
  tags : Array Name := #[]
deriving Repr, Inhabited, ToJson, FromJson

structure HierarchyGraph where
  classes : Array HierarchyClassNode
  classEdges : Array HierarchyClassEdge
  instances : Array HierarchyInstanceEdge
deriving Repr, Inhabited, ToJson, FromJson

structure HierarchyGraphEntry where
  declName : Name
  tags : Array Name := #[]
deriving Inhabited, Repr

meta initialize hierarchyGraphExt : SimpleScopedEnvExtension HierarchyGraphEntry (Array HierarchyGraphEntry) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := #[]
    addEntry := fun s e => s.push e
  }

syntax (name := hierarchyGraphAttr) "hierarchy_graph" (ppSpace ident)* : attr

meta def parseTags : Syntax → CoreM (Array Name)
  | `(attr| hierarchy_graph $[$tags]*) => pure (tags.map (·.getId))
  | _ => throwUnsupportedSyntax

meta initialize registerBuiltinAttribute {
  name := `hierarchyGraphAttr
  descr := "mark a class or instance declaration for hierarchy graph generation"
  applicationTime := .afterCompilation
  add := fun decl stx kind => do
    let tags ← parseTags stx
    if !tags.isEmpty && (← getInstancePriority? decl).isSome then
      throwError "hierarchy_graph tags are only allowed on class declarations; use bare @[hierarchy_graph] for instances"
    hierarchyGraphExt.add { declName := decl, tags } kind
  erase := fun _ => throwError "can't remove hierarchy_graph attributes"
}

meta def shortLabel (name : Name) : String :=
  name.components.getLast?.map toString |>.getD name.toString

meta def generalTag : Name := `general

meta def otherTag : Name := `other

meta def entryMatchesTags (tags : Array Name) (entry : HierarchyGraphEntry) : Bool :=
  tags.isEmpty || entry.tags.any (tags.contains ·) || (entry.tags.isEmpty && tags.contains generalTag)

meta def classEntryTags (entry : HierarchyGraphEntry) : Array Name :=
  if entry.tags.isEmpty then #[generalTag] else entry.tags

meta def appClassName? (e : Expr) : MetaM (Option Name) := do
  let e ← whnfR e
  let fn := e.getAppFn
  let some n := fn.constName? | return none
  if (← isClass? e).isSome then
    return some n
  return none

meta def collectAssumedClasses (type : Expr) : MetaM (Array Name) := do
  forallTelescopeReducing type fun xs _ => do
    let mut result := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo.isInstImplicit then
        if let some cls ← appClassName? decl.type then
          unless result.contains cls do
            result := result.push cls
    return result

meta def resultClass? (type : Expr) : MetaM (Option Name) := do
  forallTelescopeReducing type fun _ body => appClassName? body

meta def typeString (e : Expr) : CoreM String :=
  return toString e

meta def classNode? (entry : HierarchyGraphEntry) : MetaM (Option HierarchyClassNode) := do
  unless isStructure (← getEnv) entry.declName do
    return none
  let info ← getConstInfo entry.declName
  return some {
    name := entry.declName
    label := shortLabel entry.declName
    type := ← typeString info.type
    tag? := (classEntryTags entry)[0]?
    tags := classEntryTags entry
  }

meta def parentClassEdges (className : Name) : CoreM (Array HierarchyClassEdge) := do
  let env ← getEnv
  if !isStructure env className then
    return #[]
  let info := getStructureInfo env className
  let mut edges := #[]
  for p in info.parentInfo do
    edges := edges.push { source := className, target := p.structName, kind := .extends }
  return edges

meta def ensureClassNode (nodes : Array HierarchyClassNode) (name : Name) : Array HierarchyClassNode :=
  if nodes.any (·.name == name) then
    nodes
  else
    nodes.push { name, label := shortLabel name, type := "", tag? := none }

meta def mergeTags (a b : Array Name) : Array Name := Id.run do
  let mut result := a
  for tag in b do
    unless result.contains tag do
      result := result.push tag
  return result

meta def ensureOtherClassNode (nodes : Array HierarchyClassNode) (name : Name) : Array HierarchyClassNode :=
  if nodes.any (·.name == name) then
    nodes
  else
    nodes.push { name, label := shortLabel name, type := "", tag? := some otherTag, tags := #[otherTag] }

meta def mergeClassNodes (nodes : Array HierarchyClassNode) : Array HierarchyClassNode := Id.run do
  let mut result := #[]
  for node in nodes do
    if let some i := result.findIdx? (·.name == node.name) then
      if h : i < result.size then
        let old := result[i]
        result := result.set i {
          old with
          type := if old.type.isEmpty then node.type else old.type
          tag? := old.tag? <|> node.tag?
          tags := mergeTags old.tags node.tags
        } h
      else
        result := result.push node
    else
      result := result.push node
  return result

meta def closeClassNodes (nodes : Array HierarchyClassNode) (edges : Array HierarchyClassEdge)
    (instances : Array HierarchyInstanceEdge) : Array HierarchyClassNode := Id.run do
  let mut nodes := nodes
  for edge in edges do
    nodes := ensureClassNode nodes edge.source
    nodes := ensureClassNode nodes edge.target
  for inst in instances do
    nodes := ensureOtherClassNode nodes inst.output
    for input in inst.inputs do
      nodes := ensureOtherClassNode nodes input
  return nodes

meta def assumeClassEdges (className : Name) : MetaM (Array HierarchyClassEdge) := do
  let info ← getConstInfo className
  let parents ← parentClassEdges className
  let parentNames := parents.map (·.target)
  let assumptions ← collectAssumedClasses info.type
  let mut edges := #[]
  for cls in assumptions do
    unless parentNames.contains cls do
      edges := edges.push { source := className, target := cls, kind := .assumes }
  return edges

meta def instanceEdge? (entry : HierarchyGraphEntry) : MetaM (Option HierarchyInstanceEdge) := do
  unless (← getInstancePriority? entry.declName).isSome do
    return none
  let info ← getConstInfo entry.declName
  let some output ← resultClass? info.type | return none
  let inputs ← collectAssumedClasses info.type
  return some {
    name := entry.declName
    label := shortLabel entry.declName
    inputs := inputs
    output := output
    type := ← typeString info.type
    priority? := ← getInstancePriority? entry.declName
    tag? := none
    tags := #[]
  }

meta def generateHierarchyGraphWithTags (tags : Array Name := #[]) : CoreM HierarchyGraph := do
  let allEntries := hierarchyGraphExt.getState (← getEnv)
  MetaM.run' do
    let mut classes := #[]
    let mut classEdges := #[]
    let mut instances := #[]
    for entry in allEntries do
      if let some node ← classNode? entry then
        if entryMatchesTags tags entry then
          classes := classes.push node
          classEdges := classEdges ++ (← parentClassEdges entry.declName)
          classEdges := classEdges ++ (← assumeClassEdges entry.declName)
      if let some edge ← instanceEdge? entry then
        if tags.isEmpty || tags.contains otherTag then
          instances := instances.push edge
    classes := mergeClassNodes (closeClassNodes classes classEdges instances)
    return { classes, classEdges, instances }

meta def generateHierarchyGraph (tag? : Option Name := none) : CoreM HierarchyGraph := do
  generateHierarchyGraphWithTags (tag?.map (#[·]) |>.getD #[])

meta def edgeKindJson : HierarchyEdgeKind → Json
  | .extends => Json.str "extends"
  | .assumes => Json.str "assumes"

meta def nameJson (name : Name) : Json := Json.str name.toString

meta def nameArrayJson (names : Array Name) : Json := Json.arr (names.map nameJson)

meta def classNodeJson (node : HierarchyClassNode) : Json := Json.mkObj [
  ("name", nameJson node.name),
  ("label", Json.str node.label),
  ("type", Json.str node.type),
  ("tag?", node.tag?.map nameJson |>.getD Json.null),
  ("tags", nameArrayJson node.tags)
]

meta def classEdgeJson (edge : HierarchyClassEdge) : Json := Json.mkObj [
  ("source", nameJson edge.source),
  ("target", nameJson edge.target),
  ("kind", edgeKindJson edge.kind)
]

meta def instanceEdgeJson (edge : HierarchyInstanceEdge) : Json := Json.mkObj [
  ("name", nameJson edge.name),
  ("label", Json.str edge.label),
  ("inputs", nameArrayJson edge.inputs),
  ("output", nameJson edge.output),
  ("type", Json.str edge.type),
  ("priority?", edge.priority?.map (fun n => Json.str (toString n)) |>.getD Json.null),
  ("tag?", edge.tag?.map nameJson |>.getD Json.null),
  ("tags", nameArrayJson edge.tags)
]

meta def hierarchyGraphJson (graph : HierarchyGraph) : Json := Json.mkObj [
  ("classes", Json.arr (graph.classes.map classNodeJson)),
  ("classEdges", Json.arr (graph.classEdges.map classEdgeJson)),
  ("instances", Json.arr (graph.instances.map instanceEdgeJson))
]

meta def generateHierarchyGraphJson (tag? : Option Name := none) : CoreM Json := do
  return hierarchyGraphJson (← generateHierarchyGraph tag?)

meta def generateHierarchyGraphJsonWithTags (tags : Array Name := #[]) : CoreM Json := do
  return hierarchyGraphJson (← generateHierarchyGraphWithTags tags)

end HierarchyGraph

namespace Visualize

abbrev HierarchyGraph := NumLean.HierarchyGraph.HierarchyGraph

end Visualize

instance : Visualizer Visualize.HierarchyGraph where
  javascript := Visualize.javascript
  encodeProps graph := pure (Lean.toJson graph)

namespace HierarchyGraph

open Lean Elab Command Server ProofWidgets

syntax (name := hierarchyGraphJsonCmd) "#hierarchy_graph_json" (ppSpace ident)* : command

@[command_elab hierarchyGraphJsonCmd]
meta def elabHierarchyGraphJson : CommandElab := fun stx => do
  let tags ← match stx with
    | `(#hierarchy_graph_json $[$tags]*) => pure (tags.map fun tag => tag.getId)
    | _ => throwUnsupportedSyntax
  let json ← liftCoreM <| generateHierarchyGraphJsonWithTags tags
  logInfo m!"{json}"

syntax (name := visualizeHierarchyGraphCmd) "#visualize_hierarchy_graph" (ppSpace ident)* : command

@[command_elab visualizeHierarchyGraphCmd]
meta def elabVisualizeHierarchyGraph : CommandElab := fun stx => do
  let tags ← match stx with
    | `(#visualize_hierarchy_graph $[$tags]*) => pure (tags.map fun tag => tag.getId)
    | _ => throwUnsupportedSyntax
  let graph ← liftCoreM <| generateHierarchyGraphWithTags tags
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash Visualize.javascriptMeta)
    (pure (hierarchyGraphJson graph))
    stx

end HierarchyGraph
end NumLean
