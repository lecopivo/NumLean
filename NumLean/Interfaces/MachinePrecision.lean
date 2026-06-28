module

@[expose] public section

namespace NumLean

/-- Machine precision of type `R`. Many floating point algorithms needs to check for non-zero
values. However checking `x == 0` is usually not robust and something like `abs(x) <= 1e-6` is used.

This type class attaches machine precision to a conrete type

- for `Float64` we have `prec = 1e-12`
- for `Float32` we have `prec = 1e-6`

For `ℝ` we do not provide default instance as we often want to show that a program is still
valid in the limit of `prec → 0₊`.-/
class MachinePrecision (R : Type u) [LE R] [Zero R] where
  machinePrec : R
  positive : 0 ≤ machinePrec

instance : MachinePrecision Float where
  machinePrec := 2.22e-16
  positive := by native_decide

instance : MachinePrecision Float32 where
  machinePrec := 1.19e-7
  positive := by native_decide

export MachinePrecision (machinePrec)
