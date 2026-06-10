import Mathlib.Analysis.RCLike.Basic
import NumLean.Interfaces.ArrayType.Basic
import NumLean.Interfaces.BlasOps.ArrayOps

namespace NumLean

class BLASOps (Ks : Type u) (K : outParam (Type v)) where

  axpby (n : Nat) (a : K) (xs : Ks) (xoff xinc : Nat) (b : K) (ys : Ks) (yoff yinc : Nat) : Ks

  scal (n : Nat) (a : K) (xs : Ks) (xoff xinc : Nat) : Ks

  -- -- todo: add `const` i.e. create const array
  -- --           `push`
  -- --           `emptyWithCapacity`
  -- --           `append`?
  -- --           `subarray`/`copynew`/`extract` which extract slice into a newly allocated buffer

  -- /-- Size of the array `xs`. -/
  -- size (xs : Ks) : Nat

  -- /-- Total element access. Out-of-bounds behavior is implementation-defined. -/
  -- get (xs : Ks) (i : Nat) : K

  -- /-- Total element update. Out-of-bounds behavior is implementation-defined. -/
  -- set (xs : Ks) (i : Nat) (x : K) : Ks

  -- /-- Build an array from a finite function. -/
  -- ofFn (n : Nat) (f : Fin n → K) : Ks

  -- /-- Copy a strided slice of `xs` into a strided slice of `ys`. -/
  -- copy (n : Nat) (xs : Ks) (offx incx : Nat) (ys : Ks) (offy incy : Nat) : Ks

  -- /-- Swap strided slices of two arrays. -/
  -- swap (n : Nat) (xs : Ks) (offx incx : Nat) (ys : Ks) (offy incy : Nat) : Ks × Ks

  -- /-- Scale a strided slice. -/
  -- scal (n : Nat) (a : K) (xs : Ks) (offx incx : Nat) : Ks

  -- /-- Return `a * xs + b * ys` on the selected strided slice of `ys`. -/
  -- axpby (n : Nat) (a : K) (xs : Ks) (offx incx : Nat) (b : K) (ys : Ks) (offy incy : Nat) : Ks

  -- /-- Dot product of two strided slices. -/
  -- dot (n : Nat) (xs : Ks) (offx incx : Nat) (ys : Ks) (offy incy : Nat) : K

  -- /-- Euclidean norm of a strided slice. -/
  -- nrm2 (n : Nat) (xs : Ks) (offx incx : Nat) : K

  -- /-- BLAS absolute sum of a strided slice. -/
  -- asum (n : Nat) (xs : Ks) (offx incx : Nat) : K

  -- /-- Index of an entry with maximum absolute value in a strided slice. -/
  -- amax (n : Nat) (xs : Ks) (offx incx : Nat) : Nat


open ArrayType BLASOps in
class LawfulBLASOps (Ks : Type u) {K : outParam (Type v)}
    [BLASOps Ks K] [ArrayType Ks K] [RCLike K] where

  axpby_spec (n : Nat) (a : K) (xs : Ks) (xoff xinc : Nat) (b : K) (ys : Ks) (yoff yinc : Nat) :
    toArray (axpby n a xs xoff xinc b ys yoff yinc)
    =
    Array.axpby n a (toArray xs) xoff xinc b (toArray ys) yoff yinc

  scal_spec (n : Nat) (a : K) (xs : Ks) (xoff xinc : Nat) :
    toArray (scal n a xs xoff xinc)
    =
    Array.scal n a (toArray xs) xoff xinc


end NumLean
