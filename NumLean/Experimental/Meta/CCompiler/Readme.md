
# Experimental C Compiler of very small subset of Lean

This is very simple compiler of Lean code to C. It is intended to be used to a very simple C code which just runs few for loops and modifies few arrays. Any operations what would trigger copy on write should be rejected(hopefully...).

WARNING: This compiler is almost entirelly AI generated and serves only as a proof of concept. At this point, its output should be inspected manually.

It allows you to write Lean definition like
```
@[extern_in "generated/extern_fill.c"]
def fillKernel (n : USize) (dst : FloatArray) (x : Float) : FloatArray := Id.run do
  let mut dst := dst
  for_all i in 0...n do
    dst := dst.set! i.toNat x
  return dst
```
which will generate `c/generated/extern_fill.c` file with
```
void numlean_generated_extern_fill_kernel(size_t n,
    double * restrict dst,
    size_t dst_size,
    double x) {
  for (size_t i = 0; i < n; ++i) {
    dst[i] = x;
  }
}

LEAN_EXPORT lean_object* numlean_generated_extern_fill(size_t n,
    lean_object* dst,
    double x) {
  if (!lean_is_exclusive(dst)) {
    dst = lean_copy_float_array(dst);
  }
  numlean_generated_extern_fill_kernel(n, lean_float_array_cptr(dst), lean_sarray_size(dst), x);
  return dst;
}
}
```
and marks `fillKernel` with `@[extern "numlean_generated_extern_fill"]`.

## Motivation

This is a very limited Lean to C compiler and most Lean programs will be rejected. However, because it is so restrictive we can generate raw loops in C and get much more efficient code. This way we also get a reference implementation in Lean which we can prove correct under some sensible conditions like `xs.size < 2^64` and `n < 2^64`. In this context "prove correct" can for example mean that any pointer arithmetics does not overflow.
