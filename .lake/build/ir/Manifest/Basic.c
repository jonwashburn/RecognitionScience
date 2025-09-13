// Lean compiler output
// Module: Manifest.Basic
// Imports: Init Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Manifest_all;
LEAN_EXPORT lean_object* l_Manifest_routeA;
static lean_object* l_Manifest_lambda___closed__0;
static lean_object* l_Manifest_all___closed__0;
LEAN_EXPORT lean_object* l_Manifest_lambda;
LEAN_EXPORT lean_object* l_Manifest_routeB;
static lean_object* l_Manifest_routeA___closed__0;
static lean_object* l_Manifest_routeB___closed__0;
static lean_object* _init_l_Manifest_routeA___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Route A: OK (placeholder).", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Manifest_routeA() {
_start:
{
lean_object* x_1; 
x_1 = l_Manifest_routeA___closed__0;
return x_1;
}
}
static lean_object* _init_l_Manifest_routeB___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Route B: OK (placeholder).", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Manifest_routeB() {
_start:
{
lean_object* x_1; 
x_1 = l_Manifest_routeB___closed__0;
return x_1;
}
}
static lean_object* _init_l_Manifest_lambda___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("λ_rec uniqueness: OK (placeholder).", 36, 35);
return x_1;
}
}
static lean_object* _init_l_Manifest_lambda() {
_start:
{
lean_object* x_1; 
x_1 = l_Manifest_lambda___closed__0;
return x_1;
}
}
static lean_object* _init_l_Manifest_all___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Manifest: A⇒C, B⇒C, λ_rec uniqueness — OK (placeholders).", 64, 57);
return x_1;
}
}
static lean_object* _init_l_Manifest_all() {
_start:
{
lean_object* x_1; 
x_1 = l_Manifest_all___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Manifest_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Manifest_routeA___closed__0 = _init_l_Manifest_routeA___closed__0();
lean_mark_persistent(l_Manifest_routeA___closed__0);
l_Manifest_routeA = _init_l_Manifest_routeA();
lean_mark_persistent(l_Manifest_routeA);
l_Manifest_routeB___closed__0 = _init_l_Manifest_routeB___closed__0();
lean_mark_persistent(l_Manifest_routeB___closed__0);
l_Manifest_routeB = _init_l_Manifest_routeB();
lean_mark_persistent(l_Manifest_routeB);
l_Manifest_lambda___closed__0 = _init_l_Manifest_lambda___closed__0();
lean_mark_persistent(l_Manifest_lambda___closed__0);
l_Manifest_lambda = _init_l_Manifest_lambda();
lean_mark_persistent(l_Manifest_lambda);
l_Manifest_all___closed__0 = _init_l_Manifest_all___closed__0();
lean_mark_persistent(l_Manifest_all___closed__0);
l_Manifest_all = _init_l_Manifest_all();
lean_mark_persistent(l_Manifest_all);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
