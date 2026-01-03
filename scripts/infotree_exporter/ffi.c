#include <lean/lean.h>
#include <lean/mimalloc.h>

// Lean extern expects a function returning `lean_object*`.
lean_object* lean_mi_collect(uint8_t force) {
  mi_collect(force != 0);
  return lean_io_result_mk_ok(lean_box(0));
}

// Print mimalloc stats to stderr.
lean_object* lean_mi_stats_print(lean_object* /*unused*/) {
  mi_stats_print(NULL);
  return lean_io_result_mk_ok(lean_box(0));
}
