import Init.Data.Float

namespace NumLean

@[unbox]
structure Complex32 where
  (re im : Float32)

attribute [ext] Complex32

namespace Complex32

protected def abs (z : Complex32) : Float32 :=
  Float32.sqrt (z.re * z.re + z.im * z.im)

protected def log (z : Complex32) : Complex32 :=
  ⟨Float32.log z.abs, Float32.atan2 z.im z.re⟩

protected def exp (z : Complex32) : Complex32 :=
  let r := Float32.exp z.re
  ⟨r * Float32.cos z.im, r * Float32.sin z.im⟩

protected def sin (z : Complex32) : Complex32 :=
  ⟨Float32.sin z.re * Float32.cosh z.im,
    Float32.cos z.re * Float32.sinh z.im⟩

protected def cos (z : Complex32) : Complex32 :=
  ⟨Float32.cos z.re * Float32.cosh z.im,
    -(Float32.sin z.re * Float32.sinh z.im)⟩

end Complex32

end NumLean
