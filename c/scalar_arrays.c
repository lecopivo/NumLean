#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

static lean_obj_res lean_scalar_byte_array_reserve(lean_obj_arg a, size_t byte_count) {
    lean_obj_res r = lean_alloc_sarray(1, byte_count, byte_count);
    memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a), byte_count);
    return r;
}

#define DEFINE_SCALAR_ARRAY(NAME, CTYPE, BYTES, DEFAULT_VALUE, BOX, UNBOX) \
static inline CTYPE * lean_##NAME##_array_cptr(b_lean_obj_arg a) { \
    return (CTYPE*)lean_sarray_cptr(a); \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_mk(lean_obj_arg a) { \
    if (lean_is_sarray(a)) return a; \
    size_t size = lean_array_size(a); \
    lean_obj_res r = lean_alloc_sarray(1, size * (BYTES), size * (BYTES)); \
    CTYPE *out = lean_##NAME##_array_cptr(r); \
    for (size_t i = 0; i < size; ++i) { \
        out[i] = (CTYPE)(UNBOX(lean_array_get_core(a, i))); \
    } \
    lean_dec_ref(a); \
    return r; \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_data(lean_obj_arg a) { \
    if (!lean_is_sarray(a)) return a; \
    size_t size = lean_sarray_size(a) / (BYTES); \
    lean_obj_res out = lean_mk_empty_array_with_capacity(lean_usize_to_nat(size)); \
    CTYPE *src = lean_##NAME##_array_cptr(a); \
    for (size_t i = 0; i < size; ++i) { \
        out = lean_array_push(out, BOX(src[i])); \
    } \
    lean_dec_ref(a); \
    return out; \
} \
LEAN_EXPORT lean_obj_res lean_copy_##NAME##_array(lean_obj_arg a) { \
    if (!lean_is_sarray(a)) return lean_copy_expand_array(a, false); \
    lean_obj_res r = lean_scalar_byte_array_reserve(a, lean_sarray_size(a)); \
    lean_dec_ref(a); \
    return r; \
} \
LEAN_EXPORT lean_obj_res lean_mk_empty_##NAME##_array(b_lean_obj_arg capacity) { \
    size_t n = lean_usize_of_nat(capacity); \
    return lean_alloc_sarray(1, 0, n * (BYTES)); \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_size(b_lean_obj_arg a) { \
    size_t size = lean_is_sarray((lean_object*)a) ? lean_sarray_size(a) / (BYTES) : lean_array_size(a); \
    return lean_box(size); \
} \
LEAN_EXPORT CTYPE lean_##NAME##_array_uget(b_lean_obj_arg a, size_t i) { \
    if (!lean_is_sarray((lean_object*)a)) return (CTYPE)(UNBOX(lean_array_get_core(a, i))); \
    return lean_##NAME##_array_cptr(a)[i]; \
} \
LEAN_EXPORT CTYPE lean_##NAME##_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) { \
    return lean_##NAME##_array_uget(a, lean_usize_of_nat(i)); \
} \
LEAN_EXPORT CTYPE lean_##NAME##_array_get(b_lean_obj_arg a, b_lean_obj_arg i) { \
    if (!lean_is_scalar(i)) return (DEFAULT_VALUE); \
    size_t idx = lean_unbox(i); \
    size_t size = lean_is_sarray((lean_object*)a) ? lean_sarray_size(a) / (BYTES) : lean_array_size(a); \
    return idx < size ? lean_##NAME##_array_uget(a, idx) : (DEFAULT_VALUE); \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_push(lean_obj_arg a, CTYPE v) { \
    if (!lean_is_sarray(a)) return lean_array_push(a, BOX(v)); \
    size_t old_size = lean_sarray_size(a); \
    size_t new_size = old_size + (BYTES); \
    lean_obj_res r = lean_alloc_sarray(1, new_size, new_size); \
    memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a), old_size); \
    lean_##NAME##_array_cptr(r)[old_size / (BYTES)] = v; \
    lean_dec_ref(a); \
    return r; \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_uset(lean_obj_arg a, size_t i, CTYPE v) { \
    if (!lean_is_sarray(a)) return lean_array_uset(a, i, BOX(v)); \
    lean_obj_res r; \
    if (lean_is_exclusive(a)) r = a; \
    else { \
        r = lean_scalar_byte_array_reserve(a, lean_sarray_size(a)); \
        lean_dec_ref(a); \
    } \
    lean_##NAME##_array_cptr(r)[i] = v; \
    return r; \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_fset(lean_obj_arg a, b_lean_obj_arg i, CTYPE v) { \
    return lean_##NAME##_array_uset(a, lean_usize_of_nat(i), v); \
} \
LEAN_EXPORT lean_obj_res lean_##NAME##_array_set(lean_obj_arg a, b_lean_obj_arg i, CTYPE v) { \
    if (!lean_is_scalar(i)) return a; \
    size_t idx = lean_unbox(i); \
    size_t size = lean_is_sarray(a) ? lean_sarray_size(a) / (BYTES) : lean_array_size(a); \
    return idx < size ? lean_##NAME##_array_uset(a, idx, v) : a; \
}

DEFINE_SCALAR_ARRAY(float32, float, sizeof(float), 0.0f, lean_box_float32, lean_unbox_float32)
DEFINE_SCALAR_ARRAY(int32, int32_t, sizeof(int32_t), 0, lean_box_uint32, lean_unbox_uint32)
DEFINE_SCALAR_ARRAY(int64, int64_t, sizeof(int64_t), 0, lean_box_uint64, lean_unbox_uint64)
DEFINE_SCALAR_ARRAY(usize, size_t, sizeof(size_t), 0, lean_box_usize, lean_unbox_usize)
