module

public import NumLean.Data.HTuple.Order

@[expose] public section

open Lean Std PRange

namespace NumLean.HTuple.Range

/-- Base fallback for `get_tensor_elem_tactic`, using the generic `HTuple` order grind set. -/
macro "get_tensor_elem_tactic_base" : tactic =>
  `(tactic|
    first
    | grind only [$(mkIdent `grind_htuple_order):ident]
    | exact mem_rco_mono (by assumption)
        (by grind only [$(mkIdent `grind_htuple_order):ident])
        (by grind only [$(mkIdent `grind_htuple_order):ident]))

/-- Prove simple scalar bounds from `HTuple` half-open range membership hypotheses. -/
macro "get_tensor_elem_tactic" : tactic => `(tactic| get_tensor_elem_tactic_base)

macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| get_tensor_elem_tactic)


end NumLean.HTuple.Range
