module

public import NumLean.Interfaces.Algebra.Field.Lawful
public import NumLean.Data.Prod.Algebra.Ring

@[expose] public section

namespace NumLean
namespace Interfaces
namespace Algebra

instance {A B : Type _} [FieldOps A] [FieldOps B] : FieldOps (A × B) where
  nnratCast q := ⟨NNRat.cast q, NNRat.cast q⟩
  ratCast q := ⟨Rat.cast q, Rat.cast q⟩
  nnqsmul q a := ⟨FieldOps.nnqsmul q a.1, FieldOps.nnqsmul q a.2⟩
  qsmul q a := ⟨FieldOps.qsmul q a.1, FieldOps.qsmul q a.2⟩

end Algebra
end Interfaces
end NumLean
