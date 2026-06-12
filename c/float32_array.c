#include <lean/lean.h>

LEAN_EXPORT lean_obj_res lean_float32_array_mk(lean_obj_arg a) {
    return a;
}

LEAN_EXPORT lean_obj_res lean_float32_array_data(lean_obj_arg a) {
    return a;
}

LEAN_EXPORT lean_obj_res lean_mk_empty_float32_array(b_lean_obj_arg capacity) {
    return lean_mk_empty_array_with_capacity(capacity);
}

LEAN_EXPORT lean_obj_res lean_float32_array_size(b_lean_obj_arg a) {
    return lean_box(lean_array_size(a));
}

LEAN_EXPORT float lean_float32_array_uget(b_lean_obj_arg a, size_t i) {
    return lean_unbox_float32(lean_array_get_core(a, i));
}

LEAN_EXPORT float lean_float32_array_fget(b_lean_obj_arg a, b_lean_obj_arg i) {
    return lean_float32_array_uget(a, lean_unbox(i));
}

LEAN_EXPORT float lean_float32_array_get(b_lean_obj_arg a, b_lean_obj_arg i) {
    if (lean_is_scalar(i)) {
        size_t idx = lean_unbox(i);
        return idx < lean_array_size(a) ? lean_float32_array_uget(a, idx) : 0.0f;
    } else {
        return 0.0f;
    }
}

LEAN_EXPORT lean_obj_res lean_float32_array_push(lean_obj_arg a, float d) {
    return lean_array_push(a, lean_box_float32(d));
}

LEAN_EXPORT lean_obj_res lean_float32_array_uset(lean_obj_arg a, size_t i, float d) {
    return lean_array_uset(a, i, lean_box_float32(d));
}

LEAN_EXPORT lean_obj_res lean_float32_array_fset(lean_obj_arg a, b_lean_obj_arg i, float d) {
    return lean_float32_array_uset(a, lean_unbox(i), d);
}

LEAN_EXPORT lean_obj_res lean_float32_array_set(lean_obj_arg a, b_lean_obj_arg i, float d) {
    if (!lean_is_scalar(i)) {
        return a;
    } else {
        size_t idx = lean_unbox(i);
        if (idx >= lean_array_size(a)) {
            return a;
        } else {
            return lean_float32_array_uset(a, idx, d);
        }
    }
}
