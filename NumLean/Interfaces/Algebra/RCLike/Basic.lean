import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import NumLean.Interfaces.Algebra.NormedAlgebra

namespace NumLean

@[hierarchy_graph algebra_ops]
class RCOps (R : outParam (Type u)) (K : Type v) extends NormedFieldOps R K,
    NormedAlgebraOps R K, Star K, BEq K where
  le : K → K → Prop
  lt : K → K → Prop
  decLe : DecidableRel le
  decLt : DecidableRel lt
  make : R → R → K
  re : K → R
  im : K → R
  I : K
  cexp : K → K
  csin : K → K
  ccos : K → K
  cpow : K → K → K

attribute [instance 200] RCOps.toNormedFieldOps RCOps.toNormedAlgebraOps RCOps.toStar RCOps.toBEq

@[hierarchy_graph algebra_lawful]
class LawfulDataRCOps {R : outParam (Type u)} (K : Type v) [RCOps R K]
    extends LawfulDataNormedFieldOps K where
  completeSpace : CompleteSpace K
  decEq : DecidableEq K
  reHom : K → ℝ
  imHom : K → ℝ

namespace RCOps

noncomputable def toComplex {R : outParam (Type u)} {K : Type v} [RCOps R K]
    [LawfulDataRCOps (R := R) K] (z : K) : ℂ where
  re := LawfulDataRCOps.reHom (R := R) z
  im := LawfulDataRCOps.imHom (R := R) z

noncomputable def ofComplex {R : outParam (Type u)} {K : Type v} [RCOps R K]
    [LawfulDataRCOps (R := R) K] (z : ℂ) : K :=
  RCOps.make (R := R) (K := K) (LawfulDataRNorm.requiv (E := K).symm z.re)
    (LawfulDataRNorm.requiv (E := K).symm z.im)

end RCOps

@[hierarchy_graph algebra_lawful]
class LawfulRCOps {R : outParam (Type u)} (K : Type v) [RCOps R K]
    [Zero R] [LawfulDataRCOps (R := R) K] : Prop extends LawfulNormedFieldOps K where
  le_refl : ∀ x : K, RCOps.le (R := R) x x
  le_trans : ∀ x y z : K, RCOps.le (R := R) x y → RCOps.le (R := R) y z →
    RCOps.le (R := R) x z
  lt_iff_le_not_ge : ∀ x y : K,
    RCOps.lt (R := R) x y ↔ RCOps.le (R := R) x y ∧ ¬ RCOps.le (R := R) y x
  le_antisymm : ∀ x y : K, RCOps.le (R := R) x y → RCOps.le (R := R) y x → x = y
  reHom_apply : ∀ z : K, LawfulDataRCOps.reHom (R := R) z =
    LawfulDataRNorm.requiv (E := K) (RCOps.re (R := R) z)
  imHom_apply : ∀ z : K, LawfulDataRCOps.imHom (R := R) z =
    LawfulDataRNorm.requiv (E := K) (RCOps.im (R := R) z)
  re_zero : LawfulDataRCOps.reHom (R := R) (0 : K) = 0
  re_add : ∀ z w : K, LawfulDataRCOps.reHom (R := R) (z + w) =
    LawfulDataRCOps.reHom (R := R) z + LawfulDataRCOps.reHom (R := R) w
  im_zero : LawfulDataRCOps.imHom (R := R) (0 : K) = 0
  im_add : ∀ z w : K, LawfulDataRCOps.imHom (R := R) (z + w) =
    LawfulDataRCOps.imHom (R := R) z + LawfulDataRCOps.imHom (R := R) w
  star_star : ∀ z : K, star (star z) = z
  star_mul : ∀ z w : K, star (z * w) = star w * star z
  star_add : ∀ z w : K, star (z + w) = star z + star w
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : K, x < ‖a‖ ∧ ‖a‖ < y
  I_re : LawfulDataRCOps.reHom (R := R) (RCOps.I (R := R) (K := K)) = 0
  I_mul_I : RCOps.I (R := R) (K := K) = 0 ∨
    RCOps.I (R := R) (K := K) * RCOps.I (R := R) (K := K) = -1
  re_add_im : ∀ z : K,
    RCOps.make (R := R) (K := K) (RCOps.re (R := R) z) (RCOps.im (R := R) z) = z
  re_add_im_algebraMap : ∀ z : K,
    NormedAlgebraOps.algebraMap (R := R) (A := K) (RCOps.re (R := R) z) +
      NormedAlgebraOps.algebraMap (R := R) (A := K) (RCOps.im (R := R) z) *
        RCOps.I (R := R) (K := K) = z
  ofReal_re : ∀ r : R, LawfulDataRCOps.reHom (R := R)
    (RCOps.make (R := R) (K := K) r 0) = LawfulDataRNorm.requiv (E := K) r
  ofReal_im : ∀ r : R, LawfulDataRCOps.imHom (R := R)
    (RCOps.make (R := R) (K := K) r 0) = 0
  ofReal_re_algebraMap : ∀ r : R, LawfulDataRCOps.reHom (R := R)
    (NormedAlgebraOps.algebraMap (R := R) (A := K) r) = LawfulDataRNorm.requiv (E := K) r
  ofReal_im_algebraMap : ∀ r : R, LawfulDataRCOps.imHom (R := R)
    (NormedAlgebraOps.algebraMap (R := R) (A := K) r) = 0
  mul_re : ∀ z w : K, LawfulDataRCOps.reHom (R := R) (z * w) =
    LawfulDataRCOps.reHom (R := R) z * LawfulDataRCOps.reHom (R := R) w -
      LawfulDataRCOps.imHom (R := R) z * LawfulDataRCOps.imHom (R := R) w
  mul_im : ∀ z w : K, LawfulDataRCOps.imHom (R := R) (z * w) =
    LawfulDataRCOps.reHom (R := R) z * LawfulDataRCOps.imHom (R := R) w +
      LawfulDataRCOps.imHom (R := R) z * LawfulDataRCOps.reHom (R := R) w
  conj_re : ∀ z : K, LawfulDataRCOps.reHom (R := R) (star z) =
    LawfulDataRCOps.reHom (R := R) z
  conj_im : ∀ z : K, LawfulDataRCOps.imHom (R := R) (star z) =
    -LawfulDataRCOps.imHom (R := R) z
  conj_I : star (RCOps.I (R := R) (K := K)) = -RCOps.I (R := R) (K := K)
  norm_sq_eq_def : ∀ z : K, ‖z‖ ^ 2 =
    LawfulDataRCOps.reHom (R := R) z * LawfulDataRCOps.reHom (R := R) z +
      LawfulDataRCOps.imHom (R := R) z * LawfulDataRCOps.imHom (R := R) z
  mul_im_I : ∀ z : K,
    LawfulDataRCOps.imHom (R := R) z *
        LawfulDataRCOps.imHom (R := R) (RCOps.I (R := R) (K := K)) =
      LawfulDataRCOps.imHom (R := R) z
  le_iff_re_im : ∀ {z w : K}, RCOps.le (R := R) z w ↔
    LawfulDataRCOps.reHom (R := R) z ≤ LawfulDataRCOps.reHom (R := R) w ∧
      LawfulDataRCOps.imHom (R := R) z = LawfulDataRCOps.imHom (R := R) w
  cexp_eq_ofComplex : ∀ z : K, RCOps.cexp z =
    RCOps.ofComplex (R := R) (K := K) (Complex.exp (RCOps.toComplex (R := R) z))
  csin_eq_ofComplex : ∀ z : K, RCOps.csin z =
    RCOps.ofComplex (R := R) (K := K) (Complex.sin (RCOps.toComplex (R := R) z))
  ccos_eq_ofComplex : ∀ z : K, RCOps.ccos z =
    RCOps.ofComplex (R := R) (K := K) (Complex.cos (RCOps.toComplex (R := R) z))
  cpow_eq_ofComplex : ∀ z w : K, RCOps.cpow z w =
    RCOps.ofComplex (R := R) (K := K)
      (Complex.cpow (RCOps.toComplex (R := R) z) (RCOps.toComplex (R := R) w))

@[hierarchy_graph algebra_lawful]
class LawfulRCLikeOps (K : Type v) [RCOps ℝ K]
    [LawfulDataRCOps (R := ℝ) K] extends LawfulRCOps K where
  re_apply : ∀ z : K, RCOps.re (R := ℝ) z = LawfulDataRCOps.reHom (R := ℝ) z
  im_apply : ∀ z : K, RCOps.im (R := ℝ) z = LawfulDataRCOps.imHom (R := ℝ) z
  re_add_im_algebraMap_real : ∀ z : K,
    NormedAlgebraOps.algebraMap (R := ℝ) (A := K) (LawfulDataRCOps.reHom (R := ℝ) z) +
      NormedAlgebraOps.algebraMap (R := ℝ) (A := K) (LawfulDataRCOps.imHom (R := ℝ) z) *
        RCOps.I (R := ℝ) (K := K) = z
  ofReal_re_algebraMap_real : ∀ r : ℝ,
    LawfulDataRCOps.reHom (R := ℝ) (NormedAlgebraOps.algebraMap (R := ℝ) (A := K) r) = r
  ofReal_im_algebraMap_real : ∀ r : ℝ,
    LawfulDataRCOps.imHom (R := ℝ) (NormedAlgebraOps.algebraMap (R := ℝ) (A := K) r) = 0

@[hierarchy_graph algebra_ops]
class ROps (R : Type u) extends RCOps R R where
  -- decLL : DecidableLT R
  -- decLE : DecidableLE R
  exp : R → R
  sin : R → R
  cos : R → R
  pow : R → R → R
  log : R → R
  sqrt : R → R

attribute [instance 200] ROps.toRCOps

@[hierarchy_graph algebra_lawful]
class LawfulDataROps (R : Type u) [ROps R] extends LawfulDataRCOps (R := R) R

namespace ROps

instance instLE {R : Type u} [ROps R] : LE R where
  le := RCOps.le (R := R) (K := R)

instance instLT {R : Type u} [ROps R] : LT R where
  lt := RCOps.lt (R := R) (K := R)

instance instDecidableLE {R : Type u} [ROps R] : DecidableRel (· ≤ · : R → R → Prop) :=
  RCOps.decLe (R := R) (K := R)

instance instDecidableLT {R : Type u} [ROps R] : DecidableRel (· < · : R → R → Prop) :=
  RCOps.decLt (R := R) (K := R)

noncomputable def toReal {R : Type u} [ROps R] [LawfulDataROps R] (x : R) : ℝ :=
  LawfulDataRNorm.requiv (E := R) x

noncomputable def ofReal {R : Type u} [ROps R] [LawfulDataROps R] (x : ℝ) : R :=
  LawfulDataRNorm.requiv (E := R).symm x

end ROps

@[hierarchy_graph algebra_lawful]
class LawfulROps (R : Type u) [ROps R] [LawfulDataROps R] : Prop extends
    LawfulRCOps (R := R) R where
  algebraMap_eq_self : ∀ x : R, NormedAlgebraOps.algebraMap (R := R) (A := R) x = x
  norm_ofReal : ∀ x : ℝ, ‖ROps.ofReal (R := R) x‖ = ‖x‖
  requiv_zero : LawfulDataRNorm.requiv (E := R) (0 : R) = 0
  requiv_one : LawfulDataRNorm.requiv (E := R) (1 : R) = 1
  requiv_add : ∀ x y : R, LawfulDataRNorm.requiv (E := R) (x + y) =
    LawfulDataRNorm.requiv (E := R) x + LawfulDataRNorm.requiv (E := R) y
  requiv_mul : ∀ x y : R, LawfulDataRNorm.requiv (E := R) (x * y) =
    LawfulDataRNorm.requiv (E := R) x * LawfulDataRNorm.requiv (E := R) y
  requiv_le : ∀ x y : R, x ≤ y ↔
    LawfulDataRNorm.requiv (E := R) x ≤ LawfulDataRNorm.requiv (E := R) y
  re_eq : ∀ x : R, LawfulDataRCOps.reHom (R := R) x = ROps.toReal x
  im_eq_zero : ∀ x : R, LawfulDataRCOps.imHom (R := R) x = 0
  I_eq_zero : RCOps.I (R := R) (K := R) = 0
  make_eq_re : ∀ x y : R, RCOps.make (R := R) (K := R) x y = x
  lt_iff_toReal_lt : ∀ {x y : R}, x < y ↔ ROps.toReal x < ROps.toReal y
  exp_eq_ofReal : ∀ x : R, ROps.exp x = ROps.ofReal (Real.exp (ROps.toReal x))
  sin_eq_ofReal : ∀ x : R, ROps.sin x = ROps.ofReal (Real.sin (ROps.toReal x))
  cos_eq_ofReal : ∀ x : R, ROps.cos x = ROps.ofReal (Real.cos (ROps.toReal x))
  pow_eq_ofReal : ∀ x y : R, ROps.pow x y = ROps.ofReal (ROps.toReal x ^ ROps.toReal y)
  log_eq_ofReal : ∀ x : R, ROps.log x = ROps.ofReal (Real.log (ROps.toReal x))
  sqrt_eq_ofReal : ∀ x : R, ROps.sqrt x = ROps.ofReal (Real.sqrt (ROps.toReal x))


end NumLean
