/* Native experiment boundary, pinned to the built Lean runtime. Factories only
   construct ordinary Lean data. All semantic validation runs in compile(). */
#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>

extern lean_object *initialize_lean_x2dmiri_NativeRunner(uint8_t);
extern lean_object *lean_miri_ir_scalar(uint8_t, lean_object *);
extern lean_object *lean_miri_ir_natural(uint64_t);
extern lean_object *lean_miri_ir_array(lean_object *);
extern lean_object *lean_miri_ir_object(lean_object *);
extern lean_object *lean_miri_ir_image(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_miri_ir_compile(lean_object *, lean_object *);
extern lean_object *lean_miri_ir_run(lean_object *);

#define API __attribute__((visibility("default")))
API uint64_t lean_miri_bridge_version(void) { return 2; }
API int lean_miri_bridge_initialize(void) {
    lean_object *result = initialize_lean_x2dmiri_NativeRunner(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        lean_dec_ref(result);
        return 1;
    }
    lean_dec_ref(result);
    lean_init_task_manager();
    return 0;
}
API void lean_miri_bridge_finalize(void) { lean_finalize_task_manager(); }
API void lean_miri_bridge_inc(lean_object *value) { lean_inc(value); }
API void lean_miri_bridge_dec(lean_object *value) { lean_dec(value); }
API lean_object *lean_miri_bridge_array(size_t capacity) {
    return lean_alloc_array(0, capacity);
}
API lean_object *lean_miri_bridge_push(lean_object *array, lean_object *value) {
    return lean_array_push(array, value);
}
API lean_object *lean_miri_bridge_nat(uint64_t value) { return lean_uint64_to_nat(value); }
API lean_object *lean_miri_bridge_string(const char *bytes, size_t length) {
    return lean_mk_string_from_bytes(bytes, length);
}
API lean_object *lean_miri_bridge_pair(uint64_t first, uint64_t second) {
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_uint64_to_nat(first));
    lean_ctor_set(pair, 1, lean_uint64_to_nat(second));
    return pair;
}
/* The returned root is retained before releasing its Except/IO wrapper. */
static lean_object *unwrap(lean_object *result, int io) {
    int ok = io ? lean_io_result_is_ok(result) : lean_obj_tag(result) == 1;
    if (!ok) {
        if (io) lean_io_result_show_error(result);
        lean_dec(result);
        fflush(NULL);
        return NULL;
    }
    lean_object *value = lean_ctor_get(result, 0);
    lean_inc(value);
    lean_dec(result);
    return value;
}
API lean_object *lean_miri_bridge_natural(uint64_t value) { return lean_miri_ir_natural(value); }
API lean_object *lean_miri_bridge_scalar(uint8_t tag, lean_object *text) {
    return unwrap(lean_miri_ir_scalar(tag, text), 0);
}
API lean_object *lean_miri_bridge_row_array(lean_object *children) {
    return lean_miri_ir_array(children);
}
API lean_object *lean_miri_bridge_row_object(lean_object *fields) {
    return lean_miri_ir_object(fields);
}
API lean_object *lean_miri_bridge_image(lean_object *fields, lean_object *nodes, uint64_t root) {
    return lean_miri_ir_image(fields, nodes, lean_uint64_to_nat(root));
}
API lean_object *lean_miri_bridge_compile(lean_object *image, lean_object *args) {
    return unwrap(lean_miri_ir_compile(image, args), 1);
}
/* A transient ownership handoff for the single direct-source entry. This is
   cleared before executing and never retains data between source programs. */
static lean_object *pending_ir = NULL;
static lean_object *run_ir_main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    lean_object *ir = pending_ir;
    pending_ir = NULL;
    return lean_miri_ir_run(ir);
}
API int lean_miri_bridge_run(lean_object *ir) {
    if (pending_ir != NULL) { lean_dec(ir); return 1; }
    pending_ir = ir;
    /* Match the generated Lean executable's runtime thread/stack policy.
       Calling directly on Rust's smaller main stack breaks long diagnostics. */
    char program[] = "lean-miri-execution-ir";
    char *argv[] = {program, NULL};
    lean_object *result = lean_run_main(&run_ir_main, 1, argv);
    if (pending_ir != NULL) { lean_dec(pending_ir); pending_ir = NULL; }
    int code = lean_io_result_is_ok(result) ? 0 : 1;
    if (code) lean_io_result_show_error(result);
    lean_dec(result);
    /* Lean's FILE buffering and Rust's stderr are independent. In particular a
       retained reference UB diagnostic must not split a long terminal JSON line. */
    fflush(NULL);
    return code;
}
