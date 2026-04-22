// Lean compiler output
// Module: LeanGraphCanonizerV4Correctness
// Imports: public import Init public meta import Init public import LeanGraphCanonizerV4 public import Mathlib.Tactic
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg(lean_object* v_v1_3_, lean_object* v_v2_4_, lean_object* v_vts_5_){
_start:
{
lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___x_11_; lean_object* v___y_13_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_11_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0, &lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0_once, _init_lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0);
v___x_17_ = lean_array_get_size(v_vts_5_);
v___x_18_ = lean_nat_dec_lt(v_v1_3_, v___x_17_);
if (v___x_18_ == 0)
{
v___y_13_ = v___x_11_;
goto v___jp_12_;
}
else
{
lean_object* v___x_19_; 
v___x_19_ = lean_array_fget_borrowed(v_vts_5_, v_v1_3_);
lean_inc(v___x_19_);
v___y_13_ = v___x_19_;
goto v___jp_12_;
}
v___jp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_array_set(v_vts_5_, v_v1_3_, v___y_8_);
v___x_10_ = lean_array_set(v___x_9_, v_v2_4_, v___y_7_);
return v___x_10_;
}
v___jp_12_:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_array_get_size(v_vts_5_);
v___x_15_ = lean_nat_dec_lt(v_v2_4_, v___x_14_);
if (v___x_15_ == 0)
{
v___y_7_ = v___y_13_;
v___y_8_ = v___x_11_;
goto v___jp_6_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = lean_array_fget_borrowed(v_vts_5_, v_v2_4_);
lean_inc(v___x_16_);
v___y_7_ = v___y_13_;
v___y_8_ = v___x_16_;
goto v___jp_6_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg___boxed(lean_object* v_v1_20_, lean_object* v_v2_21_, lean_object* v_vts_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_GraphCanonizationProofs_Graph_swapVTs___redArg(v_v1_20_, v_v2_21_, v_vts_22_);
lean_dec(v_v2_21_);
lean_dec(v_v1_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs(lean_object* v_n_24_, lean_object* v_v1_25_, lean_object* v_v2_26_, lean_object* v_vts_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GraphCanonizationProofs_Graph_swapVTs___redArg(v_v1_25_, v_v2_26_, v_vts_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___boxed(lean_object* v_n_29_, lean_object* v_v1_30_, lean_object* v_v2_31_, lean_object* v_vts_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GraphCanonizationProofs_Graph_swapVTs(v_n_29_, v_v1_30_, v_v2_31_, v_vts_32_);
lean_dec(v_v2_31_);
lean_dec(v_v1_30_);
lean_dec(v_n_29_);
return v_res_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GraphCanonizationProofs_LeanGraphCanonizerV4(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GraphCanonizationProofs_LeanGraphCanonizerV4Correctness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GraphCanonizationProofs_LeanGraphCanonizerV4(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
