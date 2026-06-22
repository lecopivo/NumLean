import NumLean.Tactic.TBounds
import NumLean.Interfaces.IndexType

namespace NumLean.Tests.TBounds

example (i j nX nI : Nat) (hi : i < nI) (hj : j < nX) :
    i * nX + j < nI * nX := by
  tbounds

example (i nX nI : Nat) (hi : i < nI) :
    i * nX + nX ≤ nI * nX := by
  tbounds

example (i j nX nI : Nat) (hi : i < nI) (hj : j < nX) :
    j + i * nX < nX * nI := by
  tbounds

example (i nX nI : Nat) (hi : i < nI) :
    nX + i * nX ≤ nX * nI := by
  tbounds

example (i j k nI nJ nK : Nat) (hi : i < nI) (hj : j < nJ) (hk : k < nK) :
    (i * nJ + j) * nK + k < (nI * nJ) * nK := by
  tbounds

example (i j k nI nJ nK : Nat) (hi : i < nI) (hj : j < nJ) (hk : k < nK) :
    k + j * nK + i * nJ * nK < nK * nJ * nI := by
  tbounds

example (i j nI nJ nK : Nat) (hi : i < nI) (hj : j < nJ) :
    (i * nJ + j) * nK + nK ≤ (nI * nJ) * nK := by
  tbounds

example (i j k l nI nJ nK nL : Nat)
    (hi : i < nI) (hj : j < nJ) (hk : k < nK) (hl : l < nL) :
    (((i * nJ + j) * nK + k) * nL + l) < (((nI * nJ) * nK) * nL) := by
  tbounds

example (i : Fin nI) (j : Fin nX) :
    i.1 * nX + j.1 < nI * nX := by
  have hi := i.2
  have hj := j.2
  tbounds

example (i : Fin nI) :
    i.1 * nX + nX ≤ nI * nX := by
  have hi := i.2
  tbounds

example (xoff xinc xn n i : Nat) (hx : xoff + n * xinc ≤ xn) (hxinc : xinc ≠ 0)
    (hi : i ∈ (0...n : Std.Rco Nat)) :
    xoff + i * xinc < xn := by
  tbounds


example (nX nI : Nat) (i : Fin nI) (j : Fin nX) :
    i.1 * nX + j.1 < nI * nX := by
  tbounds

example (nX nI : Nat) {I : Type} [IndexType I nI] (i : I) (j : Fin nX) :
    (toFin i).1 * nX + j.1 < nI * nX := by
  tbounds using (toFin i)

end NumLean.Tests.TBounds
