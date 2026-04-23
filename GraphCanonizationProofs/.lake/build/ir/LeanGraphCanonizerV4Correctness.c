// Lean compiler output
// Module: LeanGraphCanonizerV4Correctness
// Imports: public import Init public meta import Init public import LeanGraphCanonizerV4 public import FullCorrectness.Basic public import Mathlib.Tactic
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
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter(lean_object* v_n_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__1_11_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__1_11_);
v_val_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref(v_x_10_);
v___x_16_ = lean_apply_1(v_h__2_12_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter___boxed(lean_object* v_n_17_, lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4Correctness_0__Graph_labelEdgesAccordingToRankings__isomorphic_match__1__1_splitter(v_n_17_, v_motive_18_, v_x_19_, v_h__1_20_, v_h__2_21_);
lean_dec(v_n_17_);
return v_res_22_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_nat_to_int(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg(lean_object* v_v1_25_, lean_object* v_v2_26_, lean_object* v_vts_27_){
_start:
{
lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v___x_33_; lean_object* v___y_35_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_33_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0, &lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0_once, _init_lp_GraphCanonizationProofs_Graph_swapVTs___redArg___closed__0);
v___x_39_ = lean_array_get_size(v_vts_27_);
v___x_40_ = lean_nat_dec_lt(v_v1_25_, v___x_39_);
if (v___x_40_ == 0)
{
v___y_35_ = v___x_33_;
goto v___jp_34_;
}
else
{
lean_object* v___x_41_; 
v___x_41_ = lean_array_fget_borrowed(v_vts_27_, v_v1_25_);
lean_inc(v___x_41_);
v___y_35_ = v___x_41_;
goto v___jp_34_;
}
v___jp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_array_set(v_vts_27_, v_v1_25_, v___y_30_);
v___x_32_ = lean_array_set(v___x_31_, v_v2_26_, v___y_29_);
return v___x_32_;
}
v___jp_34_:
{
lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_36_ = lean_array_get_size(v_vts_27_);
v___x_37_ = lean_nat_dec_lt(v_v2_26_, v___x_36_);
if (v___x_37_ == 0)
{
v___y_29_ = v___y_35_;
v___y_30_ = v___x_33_;
goto v___jp_28_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_array_fget_borrowed(v_vts_27_, v_v2_26_);
lean_inc(v___x_38_);
v___y_29_ = v___y_35_;
v___y_30_ = v___x_38_;
goto v___jp_28_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___redArg___boxed(lean_object* v_v1_42_, lean_object* v_v2_43_, lean_object* v_vts_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_GraphCanonizationProofs_Graph_swapVTs___redArg(v_v1_42_, v_v2_43_, v_vts_44_);
lean_dec(v_v2_43_);
lean_dec(v_v1_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs(lean_object* v_n_46_, lean_object* v_v1_47_, lean_object* v_v2_48_, lean_object* v_vts_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_GraphCanonizationProofs_Graph_swapVTs___redArg(v_v1_47_, v_v2_48_, v_vts_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_swapVTs___boxed(lean_object* v_n_51_, lean_object* v_v1_52_, lean_object* v_v2_53_, lean_object* v_vts_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_GraphCanonizationProofs_Graph_swapVTs(v_n_51_, v_v1_52_, v_v2_53_, v_vts_54_);
lean_dec(v_v2_53_);
lean_dec(v_v1_52_);
lean_dec(v_n_51_);
return v_res_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GraphCanonizationProofs_LeanGraphCanonizerV4(uint8_t builtin);
lean_object* initialize_GraphCanonizationProofs_FullCorrectness_Basic(uint8_t builtin);
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
res = initialize_GraphCanonizationProofs_FullCorrectness_Basic(builtin);
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
