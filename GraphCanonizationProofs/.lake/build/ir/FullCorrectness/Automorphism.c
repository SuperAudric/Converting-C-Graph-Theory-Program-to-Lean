// Lean compiler output
// Module: FullCorrectness.Automorphism
// Imports: public import Init public meta import Init public import FullCorrectness.Permutation public import Mathlib.Algebra.Group.Subgroup.Basic
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
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_Aut(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_Aut___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_orbitSetoid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_orbitSetoid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_Aut(lean_object* v_n_1_, lean_object* v_G_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_Aut___boxed(lean_object* v_n_4_, lean_object* v_G_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_GraphCanonizationProofs_Graph_AdjMatrix_Aut(v_n_4_, v_G_5_);
lean_dec_ref(v_G_5_);
lean_dec(v_n_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_orbitSetoid(lean_object* v_n_7_, lean_object* v_G_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_orbitSetoid___boxed(lean_object* v_n_10_, lean_object* v_G_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_GraphCanonizationProofs_Graph_AdjMatrix_orbitSetoid(v_n_10_, v_G_11_);
lean_dec_ref(v_G_11_);
lean_dec(v_n_10_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GraphCanonizationProofs_FullCorrectness_Permutation(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Group_Subgroup_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GraphCanonizationProofs_FullCorrectness_Automorphism(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GraphCanonizationProofs_FullCorrectness_Permutation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Group_Subgroup_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
