#define _DEFAULT_SOURCE 1
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>

LEAN_EXPORT lean_obj_res lean_miri_lgammaf_r(float value) {
    int sign = 0;
    float result = lgammaf_r(value, &sign);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_float32(result));
    lean_ctor_set(pair, 1, lean_box_uint32((uint32_t) sign));
    return pair;
}

LEAN_EXPORT lean_obj_res lean_miri_lgamma_r(double value) {
    int sign = 0;
    double result = lgamma_r(value, &sign);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_float(result));
    lean_ctor_set(pair, 1, lean_box_uint32((uint32_t) sign));
    return pair;
}
