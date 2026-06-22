import NumLean.Algebra.Float

namespace NumLean

inductive KernelTypeTag where
  | real
  | nat
  | int
deriving Repr, BEq

abbrev KernelType (R : Type) : KernelTypeTag -> Type
  | .real => R
  | .nat => Nat
  | .int => Int

/-- Well-typed scalar/index expression syntax for kernels. -/
inductive KernelExpr (R : Type) : KernelTypeTag -> Type where
  | bvar (t : KernelTypeTag) (idx : Nat) : KernelExpr R t
  | ctx (arrayIndex : Nat) (elemIndex : KernelExpr R .nat) : KernelExpr R .real
  | ctxSize (arrayIndex : Nat) : KernelExpr R .nat
  | lit (v : R) : KernelExpr R .real
  | natLit (v : Nat) : KernelExpr R .nat
  | intLit (v : Int) : KernelExpr R .int
  | cast (t : KernelTypeTag) {s : KernelTypeTag} (a : KernelExpr R s) : KernelExpr R t
  | add {t} (a b : KernelExpr R t) : KernelExpr R t
  | sub {t} (a b : KernelExpr R t) : KernelExpr R t
  | mul {t} (a b : KernelExpr R t) : KernelExpr R t
  | div {t} (a b : KernelExpr R t) : KernelExpr R t
  | neg {t} (a : KernelExpr R t) : KernelExpr R t
  | abs {t} (a : KernelExpr R t) : KernelExpr R t
  | sqrt (a : KernelExpr R .real) : KernelExpr R .real
  | sin (a : KernelExpr R .real) : KernelExpr R .real
  | cos (a : KernelExpr R .real) : KernelExpr R .real
  | exp (a : KernelExpr R .real) : KernelExpr R .real
  | log (a : KernelExpr R .real) : KernelExpr R .real
  | fma (a b c : KernelExpr R .real) : KernelExpr R .real
  | min {t} (a b : KernelExpr R t) : KernelExpr R t
  | max {t} (a b : KernelExpr R t) : KernelExpr R t
  | ifLt {c t} (a b : KernelExpr R c) (thenExpr elseExpr : KernelExpr R t) : KernelExpr R t
deriving Repr

namespace KernelExpr

instance : Add (KernelExpr R t) where add := .add
instance : Sub (KernelExpr R t) where sub := .sub
instance : Mul (KernelExpr R t) where mul := .mul
instance : Div (KernelExpr R t) where div := .div
instance : Neg (KernelExpr R t) where neg := .neg

def WellFormed (boundVars : Array ((t : KernelTypeTag) × KernelType R t)) (ctx : Array (Array R)) :
    KernelExpr R t -> Prop
  | .bvar t i => ∃ h : i < boundVars.size, (boundVars[i]'h).1 = t
  | .ctx arrayIndex elemIndex => arrayIndex < ctx.size ∧ WellFormed boundVars ctx elemIndex
  | .ctxSize arrayIndex => arrayIndex < ctx.size
  | .lit _ | .natLit _ | .intLit _ => True
  | .cast _ a | .neg a | .abs a |
      .sqrt a | .sin a | .cos a | .exp a | .log a => WellFormed boundVars ctx a
  | .add a b | .sub a b | .mul a b | .div a b | .min a b | .max a b =>
      WellFormed boundVars ctx a ∧ WellFormed boundVars ctx b
  | .fma a b c => WellFormed boundVars ctx a ∧ WellFormed boundVars ctx b ∧ WellFormed boundVars ctx c
  | .ifLt a b thenExpr elseExpr =>
      WellFormed boundVars ctx a ∧
      WellFormed boundVars ctx b ∧
      WellFormed boundVars ctx thenExpr ∧
      WellFormed boundVars ctx elseExpr

instance [Add R] : Add (KernelType R t) := match t with
  | .real => inferInstanceAs (Add R)
  | .int => inferInstanceAs (Add Int)
  | .nat => inferInstanceAs (Add Nat)

def eval {R : Type} [ROps R] [DecidableRel (· < · : R -> R -> Prop)]
    (boundVars : Array ((t : KernelTypeTag) × KernelType R t))
    (ctx : Array (Array R)) {t} (k : KernelExpr R t)
    (hk : WellFormed boundVars ctx k) :
    KernelType R t :=
  match t, k with
  | _, .bvar _ i =>
    let val := boundVars[i]'(by simp [WellFormed] at hk; grind)
    _root_.cast (by simp [WellFormed] at hk; obtain ⟨_,hk⟩ := hk; rw[hk]) val.2
  | _, .ctx arrayIndex elemIndex =>
    have idx := elemIndex.eval boundVars ctx hk.2
    (ctx[arrayIndex]'hk.1).getD idx 0
  | _, .ctxSize arrayIndex =>
    (ctx[arrayIndex]'hk).size
  | _, .lit v => v
  | _, .natLit v => v
  | _, .intLit v => v
  | .real, .cast _ (s := .real) a =>
    a.eval boundVars ctx (by simpa [WellFormed] using hk)
  | .real, .cast _ (s := .nat) a =>
    a.eval boundVars ctx (by simpa [WellFormed] using hk) • (1 : R)
  | .real, .cast _ (s := .int) a =>
    a.eval boundVars ctx (by simpa [WellFormed] using hk) • (1 : R)
  | .nat, .cast _ (s := .real) _ =>
    0
  | .nat, .cast _ (s := .nat) a =>
    a.eval boundVars ctx (by simpa [WellFormed] using hk)
  | .nat, .cast _ (s := .int) a =>
    (a.eval boundVars ctx (by simpa [WellFormed] using hk)).toNat
  | .int, .cast _ (s := .real) _ =>
    0
  | .int, .cast _ (s := .nat) a =>
    Int.ofNat (a.eval boundVars ctx (by simpa [WellFormed] using hk))
  | .int, .cast _ (s := .int) a =>
    a.eval boundVars ctx (by simpa [WellFormed] using hk)
  | _, add x y =>
    x.eval boundVars ctx hk.1 + y.eval boundVars ctx hk.2
  | .real, sub x y =>
    x.eval boundVars ctx hk.1 - y.eval boundVars ctx hk.2
  | .nat, sub x y =>
    x.eval boundVars ctx hk.1 - y.eval boundVars ctx hk.2
  | .int, sub x y =>
    x.eval boundVars ctx hk.1 - y.eval boundVars ctx hk.2
  | .real, mul x y =>
    x.eval boundVars ctx hk.1 * y.eval boundVars ctx hk.2
  | .nat, mul x y =>
    x.eval boundVars ctx hk.1 * y.eval boundVars ctx hk.2
  | .int, mul x y =>
    x.eval boundVars ctx hk.1 * y.eval boundVars ctx hk.2
  | .real, div x y =>
    x.eval boundVars ctx hk.1 / y.eval boundVars ctx hk.2
  | .nat, div x y =>
    x.eval boundVars ctx hk.1 / y.eval boundVars ctx hk.2
  | .int, div x y =>
    x.eval boundVars ctx hk.1 / y.eval boundVars ctx hk.2
  | .real, neg x =>
    -x.eval boundVars ctx (by simpa [WellFormed] using hk)
  | .nat, neg x =>
    x.eval boundVars ctx (by simpa [WellFormed] using hk)
  | .int, neg x =>
    -x.eval boundVars ctx (by simpa [WellFormed] using hk)
  | .real, abs x =>
    let v := x.eval boundVars ctx (by simpa [WellFormed] using hk)
    if v < 0 then -v else v
  | .nat, abs x =>
    x.eval boundVars ctx (by simpa [WellFormed] using hk)
  | .int, abs x =>
    let v := x.eval boundVars ctx (by simpa [WellFormed] using hk)
    if v < 0 then -v else v
  | _, sqrt x =>
    ROps.sqrt (x.eval boundVars ctx (by simpa [WellFormed] using hk))
  | _, sin x =>
    RCOps.sin (x.eval boundVars ctx (by simpa [WellFormed] using hk))
  | _, cos x =>
    RCOps.cos (x.eval boundVars ctx (by simpa [WellFormed] using hk))
  | _, exp x =>
    RCOps.exp (x.eval boundVars ctx (by simpa [WellFormed] using hk))
  | _, log x =>
    ROps.log (x.eval boundVars ctx (by simpa [WellFormed] using hk))
  | _, fma x y z =>
    x.eval boundVars ctx hk.1 * y.eval boundVars ctx hk.2.1 + z.eval boundVars ctx hk.2.2
  | .real, min x y =>
    let xv := x.eval boundVars ctx hk.1
    let yv := y.eval boundVars ctx hk.2
    if xv < yv then xv else yv
  | .nat, min x y =>
    Nat.min (x.eval boundVars ctx hk.1) (y.eval boundVars ctx hk.2)
  | .int, min x y =>
    let xv := x.eval boundVars ctx hk.1
    let yv := y.eval boundVars ctx hk.2
    if xv < yv then xv else yv
  | .real, max x y =>
    let xv := x.eval boundVars ctx hk.1
    let yv := y.eval boundVars ctx hk.2
    if xv < yv then yv else xv
  | .nat, max x y =>
    Nat.max (x.eval boundVars ctx hk.1) (y.eval boundVars ctx hk.2)
  | .int, max x y =>
    let xv := x.eval boundVars ctx hk.1
    let yv := y.eval boundVars ctx hk.2
    if xv < yv then yv else xv
  | _, ifLt (c := .real) a b x y =>
    if a.eval boundVars ctx hk.1 < b.eval boundVars ctx hk.2.1 then
      x.eval boundVars ctx hk.2.2.1
    else
      y.eval boundVars ctx hk.2.2.2
  | _, ifLt (c := .nat) a b x y =>
    if a.eval boundVars ctx hk.1 < b.eval boundVars ctx hk.2.1 then
      x.eval boundVars ctx hk.2.2.1
    else
      y.eval boundVars ctx hk.2.2.2
  | _, ifLt (c := .int) a b x y =>
    if a.eval boundVars ctx hk.1 < b.eval boundVars ctx hk.2.1 then
      x.eval boundVars ctx hk.2.2.1
    else
      y.eval boundVars ctx hk.2.2.2
termination_by sizeOf k


def toCCodeBody {R} [ToString R] {t} (k : KernelExpr R t) : String :=
  match k with
  | .bvar _ idx => s!"x{idx}"
  | .ctx arrayIndex elemIndex => s!"hy{arrayIndex}[{toCCodeBody elemIndex}]"
  | .ctxSize arrayIndex => s!"hy{arrayIndex}_size"
  | .lit v => s!"{v}"
  | .natLit v => s!"{v}"
  | .intLit v => s!"{v}"
  | .cast .real a => s!"((float)({toCCodeBody a}))"
  | .cast .nat a => s!"((size_t)({toCCodeBody a}))"
  | .cast .int a => s!"((long)({toCCodeBody a}))"
  | .add a b => s!"({toCCodeBody a} + {toCCodeBody b})"
  | .sub a b => s!"({toCCodeBody a} - {toCCodeBody b})"
  | .mul a b => s!"({toCCodeBody a} * {toCCodeBody b})"
  | .div a b => s!"({toCCodeBody a} / {toCCodeBody b})"
  | .neg a => s!"(-{toCCodeBody a})"
  | .abs a => s!"abs({toCCodeBody a})"
  | .sqrt a => s!"sqrt({toCCodeBody a})"
  | .sin a => s!"sin({toCCodeBody a})"
  | .cos a => s!"cos({toCCodeBody a})"
  | .exp a => s!"exp({toCCodeBody a})"
  | .log a => s!"log({toCCodeBody a})"
  | .fma a b c => s!"fma({toCCodeBody a}, {toCCodeBody b}, {toCCodeBody c})"
  | .min a b => s!"min({toCCodeBody a}, {toCCodeBody b})"
  | .max a b => s!"max({toCCodeBody a}, {toCCodeBody b})"
  | .ifLt a b thenExpr elseExpr =>
    s!"(({toCCodeBody a} < {toCCodeBody b}) ? {toCCodeBody thenExpr} : {toCCodeBody elseExpr})"



-- def eval (ctx : Array (Array Float32)) (x : Float32) (gid : Nat) (expr : Float32KernelExpr) : Float32 :=
--   KernelExpr.eval ctx x gid expr

-- def mapArraySpec (expr : Float32KernelExpr) (ctx : Array (Array Float32)) (xs : Array Float32) : Array Float32 :=
--   KernelExpr.mapArraySpec expr ctx xs

end KernelExpr
end NumLean
