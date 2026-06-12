#include <lean/lean.h>

LEAN_EXPORT lean_obj_res lean_float_array_fill_tensor_slice(
        b_lean_obj_arg counts, lean_obj_arg dst, b_lean_obj_arg dst_off,
        b_lean_obj_arg dst_strides, double x);

LEAN_EXPORT lean_obj_res lean_float_array_copy_tensor_slice(
        b_lean_obj_arg counts, b_lean_obj_arg src, b_lean_obj_arg src_off,
        b_lean_obj_arg src_strides, lean_obj_arg dst, b_lean_obj_arg dst_off,
        b_lean_obj_arg dst_strides);

LEAN_EXPORT lean_obj_res lean_float_array_extract_tensor_slice(
        b_lean_obj_arg counts, b_lean_obj_arg src, b_lean_obj_arg src_off,
        b_lean_obj_arg src_strides);

static lean_obj_res nat_array2(size_t x0, size_t x1) {
    lean_obj_res xs = lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(2));
    xs = lean_array_push(xs, lean_usize_to_nat(x0));
    xs = lean_array_push(xs, lean_usize_to_nat(x1));
    return xs;
}

static lean_obj_res nat_array1(size_t x0) {
    lean_obj_res xs = lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(1));
    xs = lean_array_push(xs, lean_usize_to_nat(x0));
    return xs;
}

static lean_obj_res float_array(const double *values, size_t n) {
    lean_obj_res xs = lean_mk_empty_float_array(lean_usize_to_nat(n));
    for (size_t i = 0; i < n; ++i) {
        xs = lean_float_array_push(xs, values[i]);
    }
    return xs;
}

static int expect_float_array(const char *name, b_lean_obj_arg actual,
        const double *expected, size_t n) {
    if (lean_sarray_size(actual) != n) {
        return 1;
    }
    for (size_t i = 0; i < n; ++i) {
        if (lean_float_array_uget(actual, i) != expected[i]) {
            return 1;
        }
    }
    (void)name;
    return 0;
}

static int test_fill(void) {
    lean_obj_res counts = nat_array2(2, 3);
    lean_obj_res strides = nat_array2(4, 1);
    double dst_data[] = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0};
    double expected[] = {0.0, 9.5, 9.5, 9.5, 4.0, 9.5, 9.5, 9.5, 8.0};
    lean_obj_res dst = float_array(dst_data, 9);
    lean_obj_res actual = lean_float_array_fill_tensor_slice(
        counts, dst, lean_usize_to_nat(1), strides, 9.5);
    return expect_float_array("fill", actual, expected, 9);
}

static int test_copy(void) {
    lean_obj_res counts = nat_array2(2, 2);
    lean_obj_res src_strides = nat_array2(5, 2);
    lean_obj_res dst_strides = nat_array2(3, 1);
    double src_data[] = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0};
    double dst_data[] = {100.0, 101.0, 102.0, 103.0, 104.0, 105.0, 106.0};
    double expected[] = {100.0, 2.0, 4.0, 103.0, 7.0, 9.0, 106.0};
    lean_obj_res src = float_array(src_data, 10);
    lean_obj_res dst = float_array(dst_data, 7);
    lean_obj_res actual = lean_float_array_copy_tensor_slice(
        counts, src, lean_usize_to_nat(2), src_strides, dst, lean_usize_to_nat(1), dst_strides);
    return expect_float_array("copy", actual, expected, 7);
}

static int test_extract(void) {
    lean_obj_res counts = nat_array2(2, 3);
    lean_obj_res strides = nat_array2(4, 1);
    double src_data[] = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0};
    double expected[] = {1.0, 2.0, 3.0, 5.0, 6.0, 7.0};
    lean_obj_res src = float_array(src_data, 9);
    lean_obj_res actual = lean_float_array_extract_tensor_slice(
        counts, src, lean_usize_to_nat(1), strides);
    return expect_float_array("extract", actual, expected, 6);
}

static int test_out_of_bounds(void) {
    lean_obj_res counts = nat_array1(4);
    lean_obj_res strides = nat_array1(2);
    double dst_data[] = {0.0, 1.0, 2.0, 3.0};
    double fill_expected[] = {0.0, 8.0, 2.0, 8.0};
    lean_obj_res dst = float_array(dst_data, 4);
    lean_obj_res filled = lean_float_array_fill_tensor_slice(
        counts, dst, lean_usize_to_nat(1), strides, 8.0);
    if (expect_float_array("fill out of bounds", filled, fill_expected, 4) != 0) {
        return 1;
    }

    double src_data[] = {10.0, 11.0, 12.0, 13.0};
    double extract_expected[] = {11.0, 13.0, 0.0, 0.0};
    lean_obj_res src = float_array(src_data, 4);
    lean_obj_res extracted = lean_float_array_extract_tensor_slice(
        counts, src, lean_usize_to_nat(1), strides);
    return expect_float_array("extract out of bounds", extracted, extract_expected, 4);
}

static int test_zero_count(void) {
    lean_obj_res counts = nat_array2(2, 0);
    lean_obj_res strides = nat_array2(4, 1);
    double xs_data[] = {1.0, 2.0, 3.0};
    double expected[] = {1.0, 2.0, 3.0};
    lean_obj_res xs = float_array(xs_data, 3);
    lean_obj_res filled = lean_float_array_fill_tensor_slice(
        counts, xs, lean_usize_to_nat(0), strides, 9.0);
    if (expect_float_array("fill zero count", filled, expected, 3) != 0) {
        return 1;
    }

    lean_obj_res extracted = lean_float_array_extract_tensor_slice(
        counts, xs, lean_usize_to_nat(0), strides);
    return expect_float_array("extract zero count", extracted, expected, 0);
}

int main(void) {
    if (test_fill() != 0) return 1;
    if (test_copy() != 0) return 1;
    if (test_extract() != 0) return 1;
    if (test_out_of_bounds() != 0) return 1;
    if (test_zero_count() != 0) return 1;
    return 0;
}
