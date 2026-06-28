module

public import NumLean.Data.FinHTuple.Basic

@[expose] public section

namespace NumLean

namespace FinHTuple

namespace Pretty

inductive Orientation where
  | row
  | col

def joinSep (sep : String) : List String → String
  | [] => ""
  | x :: xs => xs.foldl (fun acc y => acc ++ sep ++ y) x

def bracket (s : String) : String :=
  "[" ++ s ++ "]"

def leafValues {A : Type u} [ToString A] (n : Nat) (f : FinHTuple h(n) → A) : List String :=
  (List.range n).map fun i =>
    if h : i < n then
      toString (f (ofNatLt i h))
    else
      ""

partial def lines {A : Type u} [ToString A] : {p : HTuple.Profile} →
    (shape : HTuple Nat p) → (FinHTuple shape → A) → Orientation → Array String
  | .leaf, .leaf n, f, .row =>
      #[bracket (joinSep "," (leafValues n f))]
  | .leaf, .leaf n, f, .col =>
      let values := leafValues n f
      if values.isEmpty then
        #["[]"]
      else
        values.toArray.map bracket
  | .prod _ _, .prod left right, f, _ =>
      let leftGrid := matrix left .col
      let blockRows := leftGrid.map fun row =>
        row.map fun i =>
          lines right
            (fun j => f ((prodEquiv left right).symm (i, j)))
            .row
      let rows := blockRows.foldl
        (fun acc row =>
          let rowLines := mergeRow row
          if acc.isEmpty then
            rowLines
          else if rowLines.size > 1 then
            acc ++ #["---"] ++ rowLines
          else
            acc ++ rowLines)
        #[]
      if isSingleRowMatrix left right then
        rows.map fun row => bracket row
      else
        rows

where
  matrix : {p : HTuple.Profile} → (shape : HTuple Nat p) → Orientation → Array (Array (FinHTuple shape))
    | .leaf, .leaf n, .row =>
        #[((List.range n).filterMap fun i =>
          if h : i < n then some (ofNatLt i h) else none).toArray]
    | .leaf, .leaf n, .col =>
        ((List.range n).filterMap fun i =>
          if h : i < n then some #[ofNatLt i h] else none).toArray
    | .prod _ _, .prod left right, _ =>
        let leftGrid := matrix left .col
        let rightGrid := matrix right .row
        (leftGrid.toList.foldl (fun rows leftRow =>
          rows ++ rightGrid.toList.map (fun rightRow =>
            (leftRow.toList.foldl (fun cells i =>
              cells ++ rightRow.toList.map (fun j => (prodEquiv left right).symm (i, j))) []).toArray)) []).toArray

  mergeRow (blocks : Array (Array String)) : Array String :=
    let height := blocks.foldl (fun h block => max h block.size) 0
    (List.range height).toArray.map fun r =>
      joinSep " " <| blocks.toList.map fun block =>
        if h : r < block.size then block[r] else ""

  isSingleRowMatrix : {p q : HTuple.Profile} → HTuple Nat p → HTuple Nat q → Bool
    | .leaf, .leaf, .leaf 1, .leaf _ => true
    | _, _, _, _ => false

end Pretty

/-- Render a function over a bounded hierarchical shape as Kronecker-style text.

For a product shape `HTuple.prod s s'`, the left shape chooses the block positions and every block
is the recursively rendered right shape. -/
def printTensor {A : Type u} [ToString A] {p : HTuple.Profile}
    (shape : HTuple Nat p) (f : FinHTuple shape → A) : String :=
  Pretty.joinSep "\n" (Pretty.lines shape f .row).toList

end FinHTuple

end NumLean
