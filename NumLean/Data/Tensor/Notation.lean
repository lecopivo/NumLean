module

public import NumLean.Data.Tensor.HasFlatRepr
public import Lean.Elab.Term
public import Lean.PrettyPrinter.Delaborator

@[expose] public section

namespace NumLean.Tensor

open Lean Lean.Elab Lean.Elab.Term Lean.Meta
open Lean.Parser Lean.Parser.Term

declare_syntax_cat tensor_type_stx (behavior := both)
syntax term : tensor_type_stx
syntax (priority := high) tensor_type_stx ", " tensor_type_stx,* : tensor_type_stx
syntax (priority := high) "[" tensor_type_stx "]" : tensor_type_stx

/-- Elaborates a `Tensor` index type expression.

Type leaves are used directly, while `Nat` leaves become `Fin n`. Commas build right-associated
products, and bracketed subexpressions preserve grouping. -/
syntax (name := tensorIndex) "tensor_index%[" tensor_type_stx "]" : term

private meta partial def elabTensorIndexType : TSyntax `tensor_type_stx → TermElabM Expr
  | `(tensor_type_stx| [ $I:tensor_type_stx ] ) =>
      elabTensorIndexType I
  | `(tensor_type_stx| $I:tensor_type_stx, $J:tensor_type_stx, $Js:tensor_type_stx,* ) => do
      let items := #[I.raw, J.raw] ++ Js.getElems
      let mut rest ← elabTensorIndexType ⟨items.back!⟩
      for I in items.pop.reverse do
        rest ← mkAppM ``Prod #[← elabTensorIndexType ⟨I⟩, rest]
      pure rest
  | `(tensor_type_stx| $I:tensor_type_stx, $J:tensor_type_stx ) => do
      mkAppM ``Prod #[← elabTensorIndexType I, ← elabTensorIndexType J]
  | `(tensor_type_stx| $I:term ) => do
      let e ← elabTerm I none
      let type ← whnf (← inferType e)
      if ← isDefEq type (mkConst ``Nat) then
        mkAppM ``Fin #[e]
      else
        Term.ensureHasType (some (mkSort (← mkFreshLevelMVar))) e
  | _ => throwUnsupportedSyntax

@[term_elab tensorIndex]
meta def elabTensorIndex : TermElab := fun stx expectedType? => do
  let `(tensorIndex| tensor_index%[$I:tensor_type_stx]) := stx
    | throwUnsupportedSyntax
  let e ← elabTensorIndexType I
  match expectedType? with
  | some expectedType => Term.ensureHasType (some expectedType) e
  | none => pure e

macro X:term "^[" Is:tensor_type_stx "]" : term => `(Tensor $X tensor_index%[$Is])

declare_syntax_cat flat_tensor_lit_stx (behavior := both)
syntax term : flat_tensor_lit_stx
syntax "[" flat_tensor_lit_stx,* "]" : flat_tensor_lit_stx
syntax (name := flatTensorLit) "⊞[" flat_tensor_lit_stx,* "]" : term

@[term_parser]
meta def tensorOfFnNotationParser := leading_parser:maxPrec "⊞" >> basicFun

private meta def formatShape (shape : List Nat) : MessageData :=
  m!"[{MessageData.joinSep (shape.map fun n => m!"{n}") ", "}]"

private meta structure TensorLit where
  stx : Syntax
  shape : List Nat
  leaves : Array Term
  deriving Inhabited

private meta partial def normalizeLitSyntax (stx : Syntax) : Syntax :=
  if stx.getKind == `choice then
    normalizeLitSyntax stx.getArgs.back!
  else
    stx

private meta def isAtom (value : String) : Syntax → Bool
  | .atom _ value' => value == value'
  | _ => false

private meta partial def parseTensorLitSyntax (stx : Syntax) : TermElabM TensorLit := do
  let stx := normalizeLitSyntax stx
  let args := stx.getArgs
  if stx.getKind == `NumLean.Tensor.flat_tensor_lit_stx_ then
    if h : 0 < args.size then
      pure { stx := stx, shape := [], leaves := #[⟨args[0]⟩] }
    else
      throwErrorAt stx "ill-formed Tensor literal"
  else if 2 < args.size && (isAtom "[" args[0]! || isAtom "⊞[" args[0]!) && isAtom "]" args.back! then
    let itemStxs := args[1]!.getArgs.filter fun stx => !(isAtom "," stx)
    if itemStxs.isEmpty then
      throwErrorAt stx "empty Tensor literals are not supported"
    let children ← itemStxs.mapM parseTensorLitSyntax
    let expected := children[0]!.shape
    let mut leaves := #[]
    for child in children do
      unless child.shape == expected do
        throwErrorAt child.stx
          "ill-shaped Tensor literal: expected sub-shape {formatShape expected}, got {formatShape child.shape}"
      leaves := leaves ++ child.leaves
    pure { stx := stx, shape := children.size :: expected, leaves := leaves }
  else
    throwErrorAt stx "ill-formed Tensor literal"

private meta def parseTensorLit (stx : TSyntax `flat_tensor_lit_stx) : TermElabM TensorLit :=
  parseTensorLitSyntax stx.raw

private meta partial def mkFinProdType : List Nat → MetaM Expr
  | [] => throwError "Tensor literal must have positive rank"
  | [n] => mkAppM ``Fin #[mkNatLit n]
  | n :: ns => do
      mkAppM ``Prod #[← mkAppM ``Fin #[mkNatLit n], ← mkFinProdType ns]

private meta def flatTensorType? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnf type
  let fn := type.getAppFn
  unless fn.isConstOf ``Tensor do
    return none
  let args := type.getAppArgs
  if h : 2 ≤ args.size then
    return some (args[0], args[1])
  else
    return none

private meta partial def natLitValue? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => pure (some n)
  | _ => do
      let e ← reduce e
      match e with
      | .lit (.natVal n) => pure (some n)
      | _ => pure none

private meta partial def shapeOfIndexType? (I : Expr) : MetaM (Option (List Nat)) := do
  let I ← whnf I
  let fn := I.getAppFn
  let args := I.getAppArgs
  if fn.isConstOf ``Fin then
    if h : 0 < args.size then
      return (← natLitValue? args[0]).map fun n => [n]
    else
      return none
  else if fn.isConstOf ``Prod then
    if h : 2 ≤ args.size then
      match ← shapeOfIndexType? args[0], ← shapeOfIndexType? args[1] with
      | some left, some right => return some (left ++ right)
      | _, _ => return none
    else
      return none
  else
    return none

private meta def getExpectedTensorType (expectedType? : Option Expr) : TermElabM (Option (Expr × Expr)) := do
  match expectedType? with
  | none => pure none
  | some expectedType => flatTensorType? expectedType

private meta partial def curriedFunctionTypeOfIndex (I X : Expr) : MetaM Expr := do
  let I ← whnf I
  let fn := I.getAppFn
  let args := I.getAppArgs
  if fn.isConstOf ``Prod then
    if h : 2 ≤ args.size then
      mkArrow args[0] (← curriedFunctionTypeOfIndex args[1] X)
    else
      mkArrow I X
  else
    mkArrow I X

private meta def mkTensorOfFnStx (fn : Expr) : TermElabM Term := do
  let fn ← instantiateMVars fn
  let type ← whnf (← inferType fn)
  let some (I, X) := type.arrow?
    | throwError "⊞ _ => _: expected function type, got{indentExpr type}"
  let XStx ← Term.exprToSyntax X
  let IStx ← Term.exprToSyntax I
  let fnStx ← Term.exprToSyntax fn
  `(term| Tensor.ofFn (X := $XStx:term) (I := $IStx:term) $fnStx)

@[term_elab tensorOfFnNotationParser]
meta def elabTensorOfFnNotation : TermElab := fun stx expectedType? => do
  let `(term| ⊞ $bs:funBinder* => $body:term) := stx
    | throwUnsupportedSyntax
  match expectedType? with
  | some expectedType =>
      match ← getExpectedTensorType (some expectedType) with
      | some (X, I) => do
          let fStx ← `(term| fun $bs* => $body)
          let curriedF ← curriedFunctionTypeOfIndex I X
          let directF ← mkArrow I X
          let fn ←
            if bs.size = 1 then
              elabTermAndSynthesize fStx (some directF)
            else
              try
                elabTermAndSynthesize fStx (some curriedF)
              catch _ =>
                elabTermAndSynthesize fStx (some directF)
          let arity := (← inferType fn).getNumHeadForalls
          let fn ←
            if arity = 1 then
              pure fn
            else
              mkAppM ``Function.HasUncurry.uncurry #[fn]
          let XStx ← Term.exprToSyntax X
          let IStx ← Term.exprToSyntax I
          let fnStx ← Term.exprToSyntax fn
          elabTermEnsuringType
            (← `(term| Tensor.ofFn (X := $XStx:term) (I := $IStx:term) $fnStx)) expectedType
      | none => do
          let fn ← elabTermAndSynthesize (← `(term| fun $bs* => $body)) none
          let arity := (← inferType fn).getNumHeadForalls
          let fn ← if arity = 1 then pure fn else mkAppM ``Function.HasUncurry.uncurry #[fn]
          elabTermEnsuringType (← mkTensorOfFnStx fn) expectedType
  | none => do
      let fn ← elabTermAndSynthesize (← `(term| fun $bs* => $body)) none
      let arity := (← inferType fn).getNumHeadForalls
      let fn ← if arity = 1 then pure fn else mkAppM ``Function.HasUncurry.uncurry #[fn]
      elabTerm (← mkTensorOfFnStx fn) none

private meta def elabLeaves (leaves : Array Term) (expectedElemType? : Option Expr) : TermElabM (Array Expr × Expr) := do
  if h : leaves.size = 0 then
    throwError "empty Tensor literals are not supported"
  else
    match expectedElemType? with
    | some X => do
        let leaves ← leaves.mapM fun leaf => elabTermEnsuringType leaf X
        pure (leaves, X)
    | none => do
        let first ← elabTerm leaves[0] none
        let X ← inferType first
        let mut out := #[first]
        for i in [1:leaves.size] do
          out := out.push (← elabTermEnsuringType leaves[i]! X)
        pure (out, X)

private meta partial def mkVectorLitSyntax : Array Term → TermElabM Term
  | #[] => `(#v[])
  | #[x] => `(#v[$x])
  | xs => do
      let x := xs[0]!
      let rest ← mkVectorLitSyntax (xs.extract 1 xs.size)
      match rest with
      | `(term| #v[$ys,*]) => `(#v[$x, $ys,*])
      | _ => throwUnsupportedSyntax

private meta def mkTensorOfVectorTerm (X I : Expr) (leaves : Array Term) : TermElabM Term := do
  let X ← Term.exprToSyntax X
  let I ← Term.exprToSyntax I
  let n : Term := ⟨Syntax.mkNumLit (toString leaves.size)⟩
  let vector ← mkVectorLitSyntax leaves
  `(Tensor.ofVector (I := $I:term) (($vector:term) : Vector $X:term $n:term))

@[term_elab flatTensorLit]
meta def elabTensorLit : TermElab := fun stx expectedType? => do
  let parsed ← parseTensorLitSyntax stx
  let expected ← getExpectedTensorType expectedType?
  match expected with
  | some (_, I) =>
      match ← shapeOfIndexType? I with
      | some expectedShape =>
          unless parsed.shape == expectedShape do
            throwErrorAt stx
              "Tensor literal shape mismatch: expected {formatShape expectedShape}, got {formatShape parsed.shape}"
      | none => pure ()
  | none => pure ()
  let (_leafExprs, X) ← elabLeaves parsed.leaves (expected.map Prod.fst)
  let I ←
    match expected with
    | some (_, I) => pure I
    | none => mkFinProdType parsed.shape
  let outStx ← mkTensorOfVectorTerm X I parsed.leaves
  match expectedType? with
  | some expectedType => elabTermEnsuringType outStx expectedType
  | none => elabTerm outStx none

open Lean.PrettyPrinter
open Lean.PrettyPrinter.Delaborator

private meta def isProdTerm : TSyntax `term → Bool
  | `(term| Prod $_ $_) => true
  | `(term| $_ × $_) => true
  | _ => false

private meta partial def tensorStxOfTerm : TSyntax `term → UnexpandM (TSyntax `tensor_type_stx)
  | `(term| Fin $n:term) => `(tensor_type_stx| $n:term)
  | `(term| Prod $I:term $J:term) => tensorSeqStxOfProd I J
  | `(term| $I:term × $J:term) => tensorSeqStxOfProd I J
  | I => `(tensor_type_stx| $I:term)
where
  itemStxOfTerm (I : TSyntax `term) : UnexpandM (TSyntax `tensor_type_stx) := do
    let isProd := isProdTerm I
    let I ← tensorStxOfTerm I
    if isProd then
      `(tensor_type_stx| [$I:tensor_type_stx])
    else
      pure I

  commaStx (I J : TSyntax `tensor_type_stx) : UnexpandM (TSyntax `tensor_type_stx) :=
    `(tensor_type_stx| $I:tensor_type_stx, $J:tensor_type_stx)

  tensorSeqStxOfProd (I J : TSyntax `term) : UnexpandM (TSyntax `tensor_type_stx) := do
    let I' ← itemStxOfTerm I
    match J with
    | `(term| Prod $J₁:term $J₂:term) =>
        if isProdTerm I then
          commaStx I' (← itemStxOfTerm J)
        else
          commaStx I' (← tensorSeqStxOfProd J₁ J₂)
    | `(term| $J₁:term × $J₂:term) =>
        if isProdTerm I then
          commaStx I' (← itemStxOfTerm J)
        else
          commaStx I' (← tensorSeqStxOfProd J₁ J₂)
    | _ => commaStx I' (← itemStxOfTerm J)

@[app_unexpander NumLean.Tensor]
meta def unexpandTensor : Unexpander
  | `($(_) $X:term $I:term) => do
      let I ← tensorStxOfTerm I
      `(term| $X:term^[$I:tensor_type_stx])
  | _ => throw ()

@[app_unexpander Tensor.ofFn]
meta def unexpandTensorOfFn : Unexpander
  | `($(_) $f) => do
      match f with
      | `(term| ↿fun $bs:funBinder* => $body:term) =>
          `(term| ⊞ $bs* => $body)
      | `(term| ↿(fun $bs:funBinder* => $body:term)) =>
          `(term| ⊞ $bs* => $body)
      | `(term| fun $bs:funBinder* => $body:term) =>
          `(term| ⊞ $bs* => $body)
      | `(term| Function.HasUncurry.uncurry (fun $bs:funBinder* => $body:term)) =>
          `(term| ⊞ $bs* => $body)
      | _ => throw ()
  | _ => throw ()

private meta def vectorLitItems? (stx : Term) : Option (Array Term) := do
  let args := stx.raw.getArgs
  guard <| 2 < args.size
  let items := args[1]!.getArgs.filter fun stx => !(isAtom "," stx)
  pure <| items.map fun stx => (⟨stx⟩ : Term)

private meta partial def flatLitItemsOfShape (shape : List Nat) (leaves : Array Term) (offset : Nat) :
    DelabM (Array (TSyntax `flat_tensor_lit_stx) × Nat) := do
  match shape with
  | [] => failure
  | n :: rest =>
      let mut items := #[]
      let mut offset := offset
      for _ in [0:n] do
        let (item, offset') ← flatLitItemOfShape rest leaves offset
        items := items.push item
        offset := offset'
      pure (items, offset)
where
  flatLitItemOfShape (shape : List Nat) (leaves : Array Term) (offset : Nat) :
      DelabM (TSyntax `flat_tensor_lit_stx × Nat) := do
    match shape with
    | [] =>
        if h : offset < leaves.size then
          pure (← `(flat_tensor_lit_stx| $(leaves[offset]):term), offset + 1)
        else
          failure
    | _ =>
        let (items, offset) ← flatLitItemsOfShape shape leaves offset
        pure (← `(flat_tensor_lit_stx| [$items:flat_tensor_lit_stx,*]), offset)

@[app_delab Tensor.ofVector]
meta def delabTensorOfVector : Delab := whenPPOption Lean.getPPNotation do
  let args := (← SubExpr.getExpr).getAppArgs
  guard <| 1 < args.size
  let I := args[1]!
  let some shape ← shapeOfIndexType? I | failure
  let vectorStx ← SubExpr.withAppArg delab
  let some leaves := vectorLitItems? vectorStx | failure
  let (items, offset) ← flatLitItemsOfShape shape leaves 0
  guard <| offset == leaves.size
  `(⊞[$items:flat_tensor_lit_stx,*])
