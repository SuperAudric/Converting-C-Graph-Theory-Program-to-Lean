// Lean compiler output
// Module: FullCorrectness.Permutation
// Imports: public import Init public meta import Init public import FullCorrectness.Basic public import Mathlib.GroupTheory.Perm.Basic
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
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___redArg___lam__0(lean_object* v_00_u03c3_1_, lean_object* v_G_2_, lean_object* v_i_3_, lean_object* v_j_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toFun_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_5_ = lp_mathlib_Equiv_symm___redArg(v_00_u03c3_1_);
v_toFun_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_n(v_toFun_6_, 2);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_1(v_toFun_6_, v_i_3_);
v___x_8_ = lean_apply_1(v_toFun_6_, v_j_4_);
v___x_9_ = lean_apply_2(v_G_2_, v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___redArg(lean_object* v_00_u03c3_10_, lean_object* v_G_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___redArg___lam__0), 4, 2);
lean_closure_set(v___f_12_, 0, v_00_u03c3_10_);
lean_closure_set(v___f_12_, 1, v_G_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute(lean_object* v_n_13_, lean_object* v_00_u03c3_14_, lean_object* v_G_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___redArg___lam__0), 4, 2);
lean_closure_set(v___f_16_, 0, v_00_u03c3_14_);
lean_closure_set(v___f_16_, 1, v_G_15_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_permute___boxed(lean_object* v_n_17_, lean_object* v_00_u03c3_18_, lean_object* v_G_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_GraphCanonizationProofs_Graph_AdjMatrix_permute(v_n_17_, v_00_u03c3_18_, v_G_19_);
lean_dec(v_n_17_);
return v_res_20_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GraphCanonizationProofs_FullCorrectness_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_GroupTheory_Perm_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GraphCanonizationProofs_FullCorrectness_Permutation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GraphCanonizationProofs_FullCorrectness_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_GroupTheory_Perm_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
