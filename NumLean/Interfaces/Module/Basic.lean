module

public import Mathlib.Algebra.Module.Basic

@[expose] public section

namespace NumLean
namespace Interfaces
namespace Module

/-!
There is no separate `ModuleOps` class: the computational operation for a module action is exactly
`SMul K X`. Lawfulness of that action is recorded in `LawfulModuleOps`.
-/

end Module
end Interfaces
end NumLean
