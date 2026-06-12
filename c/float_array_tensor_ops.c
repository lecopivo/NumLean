#include <lean/lean.h>

static size_t lean_nat_array_get_size_t(b_lean_obj_arg xs, size_t i) {
    return lean_usize_of_nat(lean_array_get_core(xs, i));
}

static size_t numel_of(b_lean_obj_arg counts) {
    size_t rank = lean_array_size(counts);
    size_t n = 1;
    for (size_t k = 0; k < rank; ++k) {
        n *= lean_nat_array_get_size_t(counts, k);
    }
    return n;
}

static size_t offset_of_linear(size_t rank, b_lean_obj_arg counts, b_lean_obj_arg strides, size_t linear) {
    size_t off = 0;
    for (size_t rev = 0; rev < rank; ++rev) {
        size_t k = rank - 1 - rev;
        size_t count = lean_nat_array_get_size_t(counts, k);
        size_t coord = linear % count;
        linear /= count;
        off += coord * lean_nat_array_get_size_t(strides, k);
    }
    return off;
}

LEAN_EXPORT lean_obj_res lean_float_array_fill_tensor_slice(
        b_lean_obj_arg counts, lean_obj_arg dst, b_lean_obj_arg dst_off,
        b_lean_obj_arg dst_strides, double x) {
    size_t rank = lean_array_size(counts);
    size_t total = numel_of(counts);
    size_t dst_size = lean_sarray_size(dst);
    size_t base = lean_usize_of_nat(dst_off);
    for (size_t linear = 0; linear < total; ++linear) {
        size_t di = base + offset_of_linear(rank, counts, dst_strides, linear);
        if (di < dst_size) {
            dst = lean_float_array_uset(dst, di, x);
        }
    }
    return dst;
}

LEAN_EXPORT lean_obj_res lean_float_array_copy_tensor_slice(
        b_lean_obj_arg counts, b_lean_obj_arg src, b_lean_obj_arg src_off,
        b_lean_obj_arg src_strides, lean_obj_arg dst, b_lean_obj_arg dst_off,
        b_lean_obj_arg dst_strides) {
    size_t rank = lean_array_size(counts);
    size_t total = numel_of(counts);
    size_t src_size = lean_sarray_size(src);
    size_t dst_size = lean_sarray_size(dst);
    size_t src_base = lean_usize_of_nat(src_off);
    size_t dst_base = lean_usize_of_nat(dst_off);
    for (size_t linear = 0; linear < total; ++linear) {
        size_t si = src_base + offset_of_linear(rank, counts, src_strides, linear);
        size_t di = dst_base + offset_of_linear(rank, counts, dst_strides, linear);
        if (si < src_size && di < dst_size) {
            dst = lean_float_array_uset(dst, di, lean_float_array_uget(src, si));
        }
    }
    return dst;
}

LEAN_EXPORT lean_obj_res lean_float_array_extract_tensor_slice(
        b_lean_obj_arg counts, b_lean_obj_arg src, b_lean_obj_arg src_off,
        b_lean_obj_arg src_strides) {
    size_t rank = lean_array_size(counts);
    size_t total = numel_of(counts);
    lean_obj_res out = lean_mk_empty_float_array(lean_usize_to_nat(total));
    size_t src_size = lean_sarray_size(src);
    size_t src_base = lean_usize_of_nat(src_off);
    for (size_t linear = 0; linear < total; ++linear) {
        size_t si = src_base + offset_of_linear(rank, counts, src_strides, linear);
        double value = si < src_size ? lean_float_array_uget(src, si) : 0.0;
        out = lean_float_array_push(out, value);
    }
    return out;
}
