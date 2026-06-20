import NumLean.Meta.CCompiler

set_option backward.do.legacy false

open NumLean

namespace Tests.ExternIn

@[extern_in "generated/extern_scalar.c"]
def scalarKernel (n : USize) (x y : Float) : Float :=
  n.toFloat + x * y

@[extern_in "generated/extern_fill.c"]
def fillKernel (n : USize) (dst : FloatArray) (x : Float) : FloatArray := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    dst := dst.set! i.toNat x
  return dst

end Tests.ExternIn
