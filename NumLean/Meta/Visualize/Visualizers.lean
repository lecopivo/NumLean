import NumLean.Meta.Visualize.Basic

namespace NumLean

open Lean Server

namespace Visualize

/-- Visual data for a LaTeX formula rendered by the shared NumLean visualizer widget.

The string is passed to MathJax as TeX source.  It should not include surrounding `$...$` or
`\[...\]` delimiters.

Example:
```lean
Visualize.latex "\\sum_{i=0}^{n-1} x_i^2"
```
-/
structure LaTeX where
  /-- TeX source for the formula, without Markdown/math delimiters. -/
  source : String
deriving Inhabited, Repr, ToJson, FromJson

def latex (source : String) : LaTeX where
  source := source

/-- Visual data for a hierarchical high-rank tensor shown as recursively stamped heat-map blocks.

The visualizer interprets `shape` as a recursive binary product of tensor extents.  For a product
shape, the left component controls the outer stamped block grid and the right component is rendered
recursively inside each stamp.  The `values` and `labels` arrays are indexed in the same linear
order; `values` drives the heat-map colors and `labels` is the text printed inside cells.

Example payload for a `2 × 2` row-major layout:
```lean
{ shape := "(2,2)"
  values := #[0, 1, 2, 3]
  labels := #["0", "1", "2", "3"] }
```

Example payload for a stamped `((2,2),(2,2))` layout:
```lean
{ shape := "((2,2),(2,2))"
  values := #[0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  labels := #["0", "4", "1", "5", "8", "12", "9", "13",
              "2", "6", "3", "7", "10", "14", "11", "15"] }
```
-/
structure HighRankTensorVis where
  /-- Recursive tensor shape, using leaves like `2` and products like `(2,2)` or `((2,2),(2,2))`. -/
  shape : String
  /-- Linearized cell values used for color scaling.  Length should equal the product of `shape`. -/
  values : Array Int
  /-- Cell labels shown in the heat-map.  Usually the same length as `values`. -/
  labels : Array String
deriving ToJson, FromJson

/-- Visual data for a binary tree diagram.

The tree string uses a compact recursive syntax: leaves are arbitrary labels and parentheses denote
binary products.  This type is intentionally not tied to CUTE shapes; CUTE profiles and shapes are
just one source of binary-tree-shaped data.

Example:
```lean
{ shape := "(4,(2,8))" }
```
-/
structure BinaryTreeVis where
  /-- Recursive tree string, such as `4`, `(4,8)`, `(4,(2,8))`, or `(left,right)`. -/
  tree : String
deriving ToJson, FromJson

/-- Visual data for a responsive one-dimensional collection of visual items.

The JavaScript widget lays the items out in a responsive flow; the number of columns depends on the
available infoview width.  Each item must already be encoded by its own `Visualizer` before it is
placed in the flow.

Example after encoding child items to JSON:
```lean
{ items := #[toJson ({ tree := "(2,2)" } : Visualize.BinaryTreeVis)] }
```
-/
structure Flow (α : Type u) where
  /-- Items to display in responsive row/column flow order. -/
  items : Array α
deriving ToJson, FromJson

/-- Visual data for a two-dimensional collection of visual items with explicit rows.

The outer array is vertical and each inner array is a row.  Unlike `Flow`, the row structure is part
of the visual data and is preserved by the renderer.

Example after encoding child items to JSON:
```lean
{ rows := #[#[toJson ({ tree := "(2,2)" } : Visualize.BinaryTreeVis)], #[]] }
```
-/
structure Grid (α : Type u) where
  /-- Rows of items; each inner array is rendered horizontally. -/
  rows : Array (Array α)
deriving ToJson, FromJson

/-- Orientation for product visualizations.

`horizontal` places the left visual item beside the right visual item. `vertical` stacks the left
visual item above the right visual item, which is useful for titles, captions, or formulas attached
to diagrams.

Examples:
```lean
{ direction := .horizontal, weights := (1, 2) }
{ direction := .vertical, weights := (1, 3) }
```
-/
inductive ProdDirection where
  /-- Lay out the two children left-to-right. -/
  | horizontal
  /-- Lay out the two children top-to-bottom. -/
  | vertical
deriving ToJson, FromJson

/-- Layout options for product visualizations.

The string fields are passed through as CSS grid alignment keywords.  Use values such as `"start"`,
`"center"`, `"end"`, or `"stretch"`.

Example:
```lean
{ alignItems := "center", justifyItems := "stretch", gap := 18 }
{ direction := .vertical
  weights := (1, 3)
  aspectRatio? := some (1, 1)
  alignItems := "stretch"
  justifyItems := "stretch"
  gap := 8 }
```
-/
structure ProdOptions where
  /-- Whether to place the children beside each other or stack them vertically. -/
  direction : ProdDirection := .horizontal
  /-- Relative sizes of the first and second child along `direction`, interpreted as CSS `fr` units. -/
  weights : Nat × Nat := (1, 1)
  /-- Optional target aspect ratio `(width, height)` for the product container. -/
  aspectRatio? : Option (Nat × Nat) := none
  /-- CSS `align-items` value for the two-item product grid. -/
  alignItems : String := "start"
  /-- CSS `justify-items` value for the two-item product grid. -/
  justifyItems : String := "stretch"
  /-- Gap between left and right visualizations, in CSS pixels. -/
  gap : Nat := 10
deriving ToJson, FromJson

/-- Visual data for a product node that composes two independent visual items side by side.

This is the visual representation used for Lean pairs and `Visualize.prodBox`.  The `left` and
`right` fields are visual data, not arbitrary source values; they are produced by recursively using
`Visualizable.toVis` and rendered by their corresponding `Visualizer` instances.

Example after encoding child items to JSON:
```lean
{ options := { alignItems := "start", justifyItems := "stretch", gap := 10 }
  left := toJson ({ tree := "(2,2)" } : Visualize.BinaryTreeVis)
  right := toJson (Visualize.latex "i \\mapsto i + 1") }
```
-/
structure Prod (α : Type u) (β : Type v) where
  /-- Layout controls for the side-by-side product container. -/
  options : ProdOptions := {}
  /-- Left visual item. -/
  left : α
  /-- Right visual item. -/
  right : β
deriving ToJson, FromJson

/-- Explicit product wrapper for overriding the default side-by-side box layout. -/
structure ProdBox (α : Type u) (β : Type v) where
  options : ProdOptions := {}
  left : α
  right : β

def prodBox (left : α) (right : β) (options : ProdOptions := {}) : ProdBox α β where
  options := options
  left := left
  right := right

/-- Backwards-compatible alias for the original high-rank layout visual data name. -/
abbrev HighRankLayoutVis := HighRankTensorVis

end Visualize

instance : Visualizer Visualize.LaTeX where
  javascript := Visualize.javascript
  encodeProps x := pure (toJson x)

instance : Visualizer Visualize.BinaryTreeVis where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance : Visualizer Visualize.HighRankTensorVis where
  javascript := Visualize.javascript
  encodeProps props := pure (toJson props)

instance {α : Type u} [v : Visualizer α] : Visualizer (Visualize.Flow α) where
  javascript := Visualize.javascript
  encodeProps flow := do
    let items ← flow.items.mapM v.encodeProps
    pure (toJson ({ items := items } : Visualize.Flow Json))

instance {α : Type u} [v : Visualizer α] : Visualizer (Visualize.Grid α) where
  javascript := Visualize.javascript
  encodeProps grid := do
    let rows ← grid.rows.mapM fun row => row.mapM v.encodeProps
    pure (toJson ({ rows := rows } : Visualize.Grid Json))

instance {α : Type u} {β : Type v} [va : Visualizer α] [vb : Visualizer β] :
    Visualizer (Visualize.Prod α β) where
  javascript := Visualize.javascript
  encodeProps x := do
    let left ← va.encodeProps x.left
    let right ← vb.encodeProps x.right
    pure (toJson ({ options := x.options, left := left, right := right } : Visualize.Prod Json Json))

instance (priority := low) {α : Type u} [Visualizer α] : Visualizable α α where
  toVis := id

instance (priority := low) {α : Type u} {vis : Type v} [Visualizable α vis] :
    Visualizable (Array α) (Visualize.Flow vis) where
  toVis xs := { items := xs.map (Visualizable.toVis (vis := vis)) }

instance (priority := high) {α : Type u} {vis : Type v} [Visualizable α vis] :
    Visualizable (Array (Array α)) (Visualize.Grid vis) where
  toVis rows := { rows := rows.map fun xs => xs.map (Visualizable.toVis (vis := vis)) }

instance {α : Type u} {β : Type v} {visα : Type w} {visβ : Type x}
    [Visualizable α visα] [Visualizable β visβ] :
    Visualizable (α × β) (Visualize.Prod visα visβ) where
  toVis x :=
    { left := Visualizable.toVis (vis := visα) x.1
      right := Visualizable.toVis (vis := visβ) x.2 }

instance {α : Type u} {β : Type v} {visα : Type w} {visβ : Type x}
    [Visualizable α visα] [Visualizable β visβ] :
    Visualizable (Visualize.ProdBox α β) (Visualize.Prod visα visβ) where
  toVis x :=
    { options := x.options
      left := Visualizable.toVis (vis := visα) x.left
      right := Visualizable.toVis (vis := visβ) x.right }

end NumLean
