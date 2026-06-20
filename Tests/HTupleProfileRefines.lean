import NumLean.Data.HTuple.Basic

namespace NumLean

namespace Tests

namespace HTupleProfileRefines

open HTuple

example : (hp(•, •)).StrictlyRefines hp(•) :=
  inferInstance

example : (hp((•, •), •)).StrictlyRefines hp(•, •) :=
  inferInstance

example {p q : HTuple.Profile} [p.StrictlyRefines q] : p.Refines q :=
  inferInstance

example (p : HTuple.Profile) : p.StrictlyRefines p → False :=
  HTuple.Profile.not_strictlyRefines_self p

end HTupleProfileRefines

end Tests

end NumLean
