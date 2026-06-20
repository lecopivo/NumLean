#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <math.h>

LEAN_EXPORT lean_obj_res lean_copy_float32_array(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_int32_array(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_int64_array(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_usize_array(lean_obj_arg a);

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
