import NumLean.Interfaces.BlasOps.ArrayOps

namespace NumLean

variable {K} [Add K] [Mul K] [Inhabited K]

@[simp, grind =]
theorem _root_.Array.size_axpby (n : Nat)
    (a : K) (xs : Array K) (xoff xinc : Nat)
    (b : K) (ys : Array K) (yoff yinc : Nat) :
    (Array.axpby n a xs xoff xinc b ys yoff yinc).size = ys.size := sorry

theorem _root_.Array.axpby_getElem (n : Nat)
    (a : K) (xs : Array K) (xoff xinc : Nat)
    (b : K) (ys : Array K) (yoff yinc : Nat)
    (i : Nat) (hi : i < ys.size) (hyinc : yinc ≠ 0) :
    (Array.axpby n a xs xoff xinc b ys yoff yinc)[i]'(by grind)
    =
    let j := (i - yoff) / yinc
    if h : i = yoff + j * yinc ∧ xoff + j * xinc < xs.size then
      a * xs[xoff + j * xinc] + b * ys[i]
    else
      ys[i] := sorry

theorem _root_.Array.axpby_getElem_01 (a b : K) (xs ys : Array K)
    (i : Nat) (h : xs.size = ys.size) (hi : i < ys.size) :
    (Array.axpby xs.size a xs 0 1 b ys 0 1)[i]'(by grind) = a * xs[i] + b * ys[i] := by
  rw[Array.axpby_getElem (hi := hi) (hyinc := by simp)]
  grind

@[simp, grind =]
theorem _root_.Array.size_scal (n : Nat)
    (a : K) (xs : Array K) (xoff xinc : Nat) :
    (Array.scal n a xs xoff xinc).size = xs.size := sorry

theorem _root_.Array.scal_getElem (n : Nat)
    (a : K) (xs : Array K) (xoff xinc : Nat)
    (i : Nat) (hi : i < xs.size) :
    (Array.scal n a xs xoff xinc)[i]'(by grind)
    =
    let j := (i - xoff) / xinc
    if h : i = xoff + j * xinc then
      a * xs[i]
    else
      xs[i] := sorry

theorem _root_.Array.scal_getElem_01
    (a : K) (xs : Array K) (i : Nat) (hi : i < xs.size) :
    (Array.scal xs.size a xs 0 1)[i]'(by grind)
    =
    a * xs[i] := by
  rw[Array.scal_getElem (hi := hi)]
  grind

end NumLean
