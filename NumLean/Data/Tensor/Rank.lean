module

public import NumLean.Data.FinHTuple

@[expose] public section

namespace NumLean
namespace Tensor

/-- The rank structure of a tensor.

`Rank` describes how tensor indices are structured. For ordinary tensors, `.leaf` is used for a
single-axis index, while `.prod p q` combines two index structures, such as the row and column
coordinates of a matrix.

The notation `hp(...)` is syntax for building `HTuple.Profile` values: `•` means `.leaf`, commas
build nested `.prod` nodes, and parentheses keep explicit grouping.

Examples:
- `hp(•)` is `.leaf`, rank 1, used for vectors.
- `hp(•,•)` is `.prod .leaf .leaf`, rank 2, used for matrices.
- `hp(•,•,•,•)` is rank 4, used for ordinary four-axis tensors.
- `hp((•,•),(•,•))` is also rank 4, but grouped as a matrix of matrices.

This plays the role usually called tensor rank, dimension count, or axis structure in libraries
such as NumPy, PyTorch, or XLA, except NumLean keeps this structure at the type level.

**Note:** This is an abbreviation for `HTuple.Profile`. Because it is an abbreviation, it inherits
all `HTuple.Profile` notation and operations, such as `.prod` and `hp(...)`. Lean may display the
resulting type as `HTuple.Profile` instead of `Tensor.Rank`, but the two are definitionally the
same. -/
abbrev Rank := HTuple.Profile

end Tensor
end NumLean
