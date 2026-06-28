module

@[expose] public section

/-- Typeclass for half-open ranges that provide an explicitly indexed enumeration view. -/
class Std.Rco.HasEnum (ρ : Type u) (ε : outParam (Type v)) where
  enum : ρ → ε

namespace Std.Rco

/-- Enumerate a half-open range with whatever indexed view its element type provides. -/
@[inline] def enum {α : Type u} (r : Std.Rco α) {ε : Type v} [HasEnum (Std.Rco α) ε] : ε :=
  HasEnum.enum r

end Std.Rco
