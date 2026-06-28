module

public import NumLean.Data.Tensor.Shape
public import NumLean.Data.FinHTuple

@[expose] public section

namespace NumLean
namespace Tensor



abbrev FinIndex {p : Rank} (shape : Shape p) := FinHTuple shape

end Tensor
end NumLean
