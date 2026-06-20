#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <math.h>

LEAN_EXPORT lean_obj_res lean_copy_float32_array(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_int32_array(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_int64_array(lean_obj_arg a);
LEAN_EXPORT lean_obj_res lean_copy_usize_array(lean_obj_arg a);

double numlean_generated_extern_scalar_kernel(size_t n,
    double x,
    double y) {
  return ((double)(n) + (x * y));
}

LEAN_EXPORT double numlean_generated_extern_scalar(size_t n,
    double x,
    double y) {
  double _ret = numlean_generated_extern_scalar_kernel(n, x, y);
  return _ret;
}
