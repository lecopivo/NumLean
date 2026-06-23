import NumLean.Data.Tensor.Shape
import NumLean.Data.FinHTuple

namespace NumLean
namespace Tensor



abbrev FinIndex {p : Rank} (shape : Shape p) := FinHTuple shape

end Tensor
end NumLean
