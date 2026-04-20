// Lean compiler output
// Module: GraphStructureAttempt1
// Imports: public import Init public meta import Init public import Mathlib.Tactic public import Aesop
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
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lp_mathlib_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Mathlib_Tactic_Linarith_instReprComp_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__0 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__0_value;
static const lean_string_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__1 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__1_value;
static const lean_ctor_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__1_value)}};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__2 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__2_value;
static const lean_ctor_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__3 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__3_value;
static const lean_string_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__4 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__4_value;
static lean_once_cell_t lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__5;
static lean_once_cell_t lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6;
static const lean_ctor_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__0_value)}};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__7 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__7_value;
static const lean_ctor_object lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__4_value)}};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__8 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__8_value;
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__0 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__0_value;
static const lean_string_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "adj"};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__1 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__1_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__1_value)}};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__2 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__2_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__2_value)}};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__3 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__3_value;
static const lean_string_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__4 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__4_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__4_value)}};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__5 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__5_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__3_value),((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__5_value)}};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__6 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__6_value;
static lean_once_cell_t lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__7;
static const lean_string_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__8 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__8_value;
static lean_once_cell_t lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__9;
static lean_once_cell_t lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__10;
static const lean_ctor_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__0_value)}};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__11 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__11_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__8_value)}};
static const lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__12 = (const lean_object*)&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix(lean_object*);
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___closed__0 = (const lean_object*)&lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___closed__0_value;
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Graph"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__0 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__0_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "AdjMatrix"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__1 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__1_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≃_"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__2 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__2_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 36, 206, 233, 246, 43, 71, 96)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_0),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 144, 243, 39, 60, 12, 127, 183)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_1),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 92, 145, 90, 179, 71, 65, 151)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__4 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__4_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__5 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__5_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≃ "};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__6 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__6_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__6_value)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__7 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__7_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__8 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__8_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__9 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__9_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__10 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__10_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__5_value),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__7_value),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__10_value)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__11 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__11_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__11_value)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__12 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__12_value;
LEAN_EXPORT const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_term___u2243__ = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__12_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_0),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_1),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_2),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Isomorphic"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value;
static lean_once_cell_t lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(240, 190, 20, 130, 109, 57, 74, 242)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 36, 206, 233, 246, 43, 71, 96)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_0),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 144, 243, 39, 60, 12, 127, 183)}};
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_1),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 168, 201, 31, 52, 68, 229)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12_value;
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14_value;
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value;
static const lean_ctor_object lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1_value;
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0_value;
static const lean_string_object lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1 = (const lean_object*)&lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1_value;
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_hello_x2dworld_Graph_AdjMatrix_adjToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* lp_hello_x2dworld_Graph_AdjMatrix_adjToString___closed__0 = (const lean_object*)&lp_hello_x2dworld_Graph_AdjMatrix_adjToString___closed__0_value;
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_adjToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_instToString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_instToString(lean_object*);
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__0(lean_object* v___x_1_, lean_object* v_n_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
if (lean_obj_tag(v_a_3_) == 0)
{
lean_object* v___x_5_; 
lean_dec(v_n_2_);
lean_dec_ref(v___x_1_);
v___x_5_ = l_List_reverse___redArg(v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_18_; 
v_head_6_ = lean_ctor_get(v_a_3_, 0);
v_tail_7_ = lean_ctor_get(v_a_3_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_18_ == 0)
{
v___x_9_ = v_a_3_;
v_isShared_10_ = v_isSharedCheck_18_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_tail_7_);
lean_inc(v_head_6_);
lean_dec(v_a_3_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_18_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_inc_ref(v___x_1_);
lean_inc(v_n_2_);
v___x_11_ = lean_apply_2(v___x_1_, v_n_2_, v_head_6_);
v___x_12_ = l_Nat_reprFast(v___x_11_);
v___x_13_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v_a_4_);
lean_ctor_set(v___x_9_, 0, v___x_13_);
v___x_15_ = v___x_9_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_a_4_);
v___x_15_ = v_reuseFailAlloc_17_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
v_a_3_ = v_tail_7_;
v_a_4_ = v___x_15_;
goto _start;
}
}
}
}
}
static lean_object* _init_lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__0));
v___x_28_ = lean_string_length(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_obj_once(&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__5, &lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__5_once, _init_lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__5);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1(lean_object* v_n_35_, lean_object* v___x_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
if (lean_obj_tag(v_a_37_) == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v___x_36_);
lean_dec(v_n_35_);
v___x_39_ = l_List_reverse___redArg(v_a_38_);
return v___x_39_;
}
else
{
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_62_; 
v_head_40_ = lean_ctor_get(v_a_37_, 0);
v_tail_41_ = lean_ctor_get(v_a_37_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_a_37_);
if (v_isSharedCheck_62_ == 0)
{
v___x_43_ = v_a_37_;
v_isShared_44_ = v_isSharedCheck_62_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_tail_41_);
lean_inc(v_head_40_);
lean_dec(v_a_37_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_62_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
lean_inc(v_n_35_);
v___x_45_ = l_List_finRange(v_n_35_);
v___x_46_ = lean_box(0);
lean_inc_ref(v___x_36_);
v___x_47_ = lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__0(v___x_36_, v_head_40_, v___x_45_, v___x_46_);
v___x_48_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__3));
v___x_49_ = lp_mathlib_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Mathlib_Tactic_Linarith_instReprComp_repr_spec__0_spec__0_spec__2(v___x_47_, v___x_48_);
v___x_50_ = lean_obj_once(&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6, &lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6_once, _init_lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6);
v___x_51_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__7));
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_49_);
v___x_53_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__8));
v___x_54_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_50_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = 0;
v___x_57_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_56_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 1, v_a_38_);
lean_ctor_set(v___x_43_, 0, v___x_57_);
v___x_59_ = v___x_43_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_a_38_);
v___x_59_ = v_reuseFailAlloc_61_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
v_a_37_ = v_tail_41_;
v_a_38_ = v___x_59_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1(lean_object* v___x_63_, lean_object* v_n_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
if (lean_obj_tag(v_a_65_) == 0)
{
lean_object* v___x_67_; 
lean_dec(v_n_64_);
lean_dec_ref(v___x_63_);
v___x_67_ = l_List_reverse___redArg(v_a_66_);
return v___x_67_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_90_; 
v_head_68_ = lean_ctor_get(v_a_65_, 0);
v_tail_69_ = lean_ctor_get(v_a_65_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_90_ == 0)
{
v___x_71_ = v_a_65_;
v_isShared_72_ = v_isSharedCheck_90_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_tail_69_);
lean_inc(v_head_68_);
lean_dec(v_a_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_90_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
lean_inc(v_n_64_);
v___x_73_ = l_List_finRange(v_n_64_);
v___x_74_ = lean_box(0);
lean_inc_ref(v___x_63_);
v___x_75_ = lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__0(v___x_63_, v_head_68_, v___x_73_, v___x_74_);
v___x_76_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__3));
v___x_77_ = lp_mathlib_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Mathlib_Tactic_Linarith_instReprComp_repr_spec__0_spec__0_spec__2(v___x_75_, v___x_76_);
v___x_78_ = lean_obj_once(&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6, &lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6_once, _init_lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6);
v___x_79_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__7));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_77_);
v___x_81_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__8));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_78_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = 0;
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_84_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v_a_66_);
lean_ctor_set(v___x_71_, 0, v___x_85_);
v___x_87_ = v___x_71_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_a_66_);
v___x_87_ = v_reuseFailAlloc_89_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; 
v___x_88_ = lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1(v_n_64_, v___x_63_, v_tail_69_, v___x_87_);
return v___x_88_;
}
}
}
}
}
static lean_object* _init_lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(7u);
v___x_105_ = lean_nat_to_int(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__0));
v___x_108_ = lean_string_length(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__9, &lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__9_once, _init_lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__9);
v___x_110_ = lean_nat_to_int(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg(lean_object* v_n_115_, lean_object* v_x_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_117_ = ((lean_object*)(lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__6));
v___x_118_ = lean_obj_once(&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__7, &lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__7_once, _init_lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__7);
lean_inc(v_n_115_);
v___x_119_ = l_List_finRange(v_n_115_);
v___x_120_ = lean_box(0);
v___x_121_ = lp_hello_x2dworld_List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1(v_x_116_, v_n_115_, v___x_119_, v___x_120_);
v___x_122_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__3));
v___x_123_ = lp_mathlib_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Mathlib_Tactic_Linarith_instReprComp_repr_spec__0_spec__0_spec__2(v___x_121_, v___x_122_);
v___x_124_ = lean_obj_once(&lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6, &lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6_once, _init_lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__6);
v___x_125_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__7));
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_123_);
v___x_127_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_instReprAdjMatrix_repr_spec__1_spec__1___closed__8));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_124_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_130_);
v___x_132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_118_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*1, v___x_130_);
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_117_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_obj_once(&lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__10, &lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__10_once, _init_lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__10);
v___x_136_ = ((lean_object*)(lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__11));
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_134_);
v___x_138_ = ((lean_object*)(lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg___closed__12));
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_135_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_130_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr(lean_object* v_n_142_, lean_object* v_x_143_, lean_object* v_prec_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___redArg(v_n_142_, v_x_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___boxed(lean_object* v_n_146_, lean_object* v_x_147_, lean_object* v_prec_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_hello_x2dworld_Graph_instReprAdjMatrix_repr(v_n_146_, v_x_147_, v_prec_148_);
lean_dec(v_prec_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instReprAdjMatrix(lean_object* v_n_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_closure((void*)(lp_hello_x2dworld_Graph_instReprAdjMatrix_repr___boxed), 3, 1);
lean_closure_set(v___x_151_, 0, v_n_150_);
return v___x_151_;
}
}
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__0(lean_object* v_a_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = lean_nat_dec_eq(v___y_153_, v___y_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__0___boxed(lean_object* v_a_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__0(v_a_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec(v___y_157_);
lean_dec(v_a_156_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__1(lean_object* v___f_161_, lean_object* v___x_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_161_, v___x_162_, v_a_164_, v_b_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__1___boxed(lean_object* v___f_167_, lean_object* v___x_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__1(v___f_167_, v___x_168_, v_a_169_, v_a_170_, v_b_171_);
lean_dec(v_a_169_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq(lean_object* v_n_175_, lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___f_180_; uint8_t v___x_181_; 
v___f_178_ = ((lean_object*)(lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___closed__0));
v___x_179_ = l_List_finRange(v_n_175_);
lean_inc(v___x_179_);
v___f_180_ = lean_alloc_closure((void*)(lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___lam__1___boxed), 5, 2);
lean_closure_set(v___f_180_, 0, v___f_178_);
lean_closure_set(v___f_180_, 1, v___x_179_);
v___x_181_ = lp_mathlib_Fintype_decidablePiFintype___redArg(v___f_180_, v___x_179_, v_x_176_, v_x_177_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq___boxed(lean_object* v_n_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq(v_n_182_, v_x_183_, v_x_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix(lean_object* v_n_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix_decEq(v_n_187_, v_x_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix___boxed(lean_object* v_n_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = lp_hello_x2dworld_Graph_instDecidableEqAdjMatrix(v_n_191_, v_x_192_, v_x_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___redArg___lam__0(lean_object* v_i_196_, lean_object* v_j_197_, lean_object* v_G_198_, lean_object* v_u_199_, lean_object* v_v_200_){
_start:
{
uint8_t v___x_201_; uint8_t v___x_202_; lean_object* v___y_204_; 
v___x_201_ = lean_nat_dec_eq(v_u_199_, v_i_196_);
v___x_202_ = lean_nat_dec_eq(v_v_200_, v_i_196_);
if (v___x_201_ == 0)
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_eq(v_u_199_, v_j_197_);
if (v___x_209_ == 0)
{
v___y_204_ = v_u_199_;
goto v___jp_203_;
}
else
{
lean_dec(v_u_199_);
lean_inc(v_i_196_);
v___y_204_ = v_i_196_;
goto v___jp_203_;
}
}
else
{
lean_dec(v_u_199_);
lean_inc(v_j_197_);
v___y_204_ = v_j_197_;
goto v___jp_203_;
}
v___jp_203_:
{
if (v___x_202_ == 0)
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_eq(v_v_200_, v_j_197_);
lean_dec(v_j_197_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec(v_i_196_);
v___x_206_ = lean_apply_2(v_G_198_, v___y_204_, v_v_200_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
lean_dec(v_v_200_);
v___x_207_ = lean_apply_2(v_G_198_, v___y_204_, v_i_196_);
return v___x_207_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec(v_v_200_);
lean_dec(v_i_196_);
v___x_208_ = lean_apply_2(v_G_198_, v___y_204_, v_j_197_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___redArg(lean_object* v_i_210_, lean_object* v_j_211_, lean_object* v_G_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v___f_213_, 0, v_i_210_);
lean_closure_set(v___f_213_, 1, v_j_211_);
lean_closure_set(v___f_213_, 2, v_G_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices(lean_object* v_n_214_, lean_object* v_i_215_, lean_object* v_j_216_, lean_object* v_G_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = lean_alloc_closure((void*)(lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v___f_218_, 0, v_i_215_);
lean_closure_set(v___f_218_, 1, v_j_216_);
lean_closure_set(v___f_218_, 2, v_G_217_);
return v___f_218_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_swapVertices___boxed(lean_object* v_n_219_, lean_object* v_i_220_, lean_object* v_j_221_, lean_object* v_G_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = lp_hello_x2dworld_Graph_AdjMatrix_swapVertices(v_n_219_, v_i_220_, v_j_221_, v_G_222_);
lean_dec(v_n_219_);
return v_res_223_;
}
}
static lean_object* _init_lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5));
v___x_263_ = l_String_toRawSubstring_x27(v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1(lean_object* v_x_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3));
lean_inc(v_x_284_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_x_284_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_x_284_);
v___x_289_ = lean_box(1);
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v_a_286_);
return v___x_290_;
}
else
{
lean_object* v_quotContext_291_; lean_object* v_currMacroScope_292_; lean_object* v_ref_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_quotContext_291_ = lean_ctor_get(v_a_285_, 1);
v_currMacroScope_292_ = lean_ctor_get(v_a_285_, 2);
v_ref_293_ = lean_ctor_get(v_a_285_, 5);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l_Lean_Syntax_getArg(v_x_284_, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(2u);
v___x_297_ = l_Lean_Syntax_getArg(v_x_284_, v___x_296_);
lean_dec(v_x_284_);
v___x_298_ = 0;
v___x_299_ = l_Lean_SourceInfo_fromRef(v_ref_293_, v___x_298_);
v___x_300_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4));
v___x_301_ = lean_obj_once(&lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6, &lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6_once, _init_lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6);
v___x_302_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7));
lean_inc(v_currMacroScope_292_);
lean_inc(v_quotContext_291_);
v___x_303_ = l_Lean_addMacroScope(v_quotContext_291_, v___x_302_, v_currMacroScope_292_);
v___x_304_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12));
lean_inc_n(v___x_299_, 2);
v___x_305_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_305_, 0, v___x_299_);
lean_ctor_set(v___x_305_, 1, v___x_301_);
lean_ctor_set(v___x_305_, 2, v___x_303_);
lean_ctor_set(v___x_305_, 3, v___x_304_);
v___x_306_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14));
v___x_307_ = l_Lean_Syntax_node2(v___x_299_, v___x_306_, v___x_295_, v___x_297_);
v___x_308_ = l_Lean_Syntax_node2(v___x_299_, v___x_300_, v___x_305_, v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_a_286_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___boxed(lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1(v_x_310_, v_a_311_, v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1(lean_object* v_x_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4));
lean_inc(v_x_317_);
v___x_321_ = l_Lean_Syntax_isOfKind(v_x_317_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_x_317_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_319_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Lean_Syntax_getArg(v_x_317_, v___x_324_);
v___x_326_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1));
lean_inc(v___x_325_);
v___x_327_ = l_Lean_Syntax_isOfKind(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v___x_325_);
lean_dec(v_x_317_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_319_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = l_Lean_Syntax_getArg(v_x_317_, v___x_330_);
lean_dec(v_x_317_);
v___x_332_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_331_);
v___x_333_ = l_Lean_Syntax_matchesNull(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec(v___x_331_);
lean_dec(v___x_325_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_a_319_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_ref_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_336_ = l_Lean_Syntax_getArg(v___x_331_, v___x_324_);
v___x_337_ = l_Lean_Syntax_getArg(v___x_331_, v___x_330_);
lean_dec(v___x_331_);
v_ref_338_ = l_Lean_replaceRef(v___x_325_, v_a_318_);
lean_dec(v___x_325_);
v___x_339_ = 0;
v___x_340_ = l_Lean_SourceInfo_fromRef(v_ref_338_, v___x_339_);
lean_dec(v_ref_338_);
v___x_341_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__3));
v___x_342_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix_term___u2243___00__closed__6));
lean_inc(v___x_340_);
v___x_343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_Syntax_node3(v___x_340_, v___x_341_, v___x_336_, v___x_343_, v___x_337_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_a_319_);
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___boxed(lean_object* v_x_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = lp_hello_x2dworld_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1(v_x_346_, v_a_347_, v_a_348_);
lean_dec(v_a_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(lean_object* v_G_350_, lean_object* v_i_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
if (lean_obj_tag(v_a_352_) == 0)
{
lean_object* v___x_354_; 
lean_dec(v_i_351_);
lean_dec_ref(v_G_350_);
v___x_354_ = l_List_reverse___redArg(v_a_353_);
return v___x_354_;
}
else
{
lean_object* v_head_355_; lean_object* v_tail_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
v_head_355_ = lean_ctor_get(v_a_352_, 0);
v_tail_356_ = lean_ctor_get(v_a_352_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_366_ == 0)
{
v___x_358_ = v_a_352_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_tail_356_);
lean_inc(v_head_355_);
lean_dec(v_a_352_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
lean_inc_ref(v_G_350_);
lean_inc(v_i_351_);
v___x_360_ = lean_apply_2(v_G_350_, v_i_351_, v_head_355_);
v___x_361_ = l_Nat_reprFast(v___x_360_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_a_353_);
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_a_353_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v_a_352_ = v_tail_356_;
v_a_353_ = v___x_363_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(lean_object* v_G_369_, lean_object* v_rows_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
if (lean_obj_tag(v_a_371_) == 0)
{
lean_object* v___x_373_; 
lean_dec(v_rows_370_);
lean_dec_ref(v_G_369_);
v___x_373_ = l_List_reverse___redArg(v_a_372_);
return v___x_373_;
}
else
{
lean_object* v_head_374_; lean_object* v_tail_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_389_; 
v_head_374_ = lean_ctor_get(v_a_371_, 0);
v_tail_375_ = lean_ctor_get(v_a_371_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_a_371_);
if (v_isSharedCheck_389_ == 0)
{
v___x_377_ = v_a_371_;
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_tail_375_);
lean_inc(v_head_374_);
lean_dec(v_a_371_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v_rowString_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_379_ = lean_box(0);
lean_inc(v_rows_370_);
lean_inc_ref(v_G_369_);
v_rowString_380_ = lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(v_G_369_, v_head_374_, v_rows_370_, v___x_379_);
v___x_381_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0));
v___x_382_ = l_List_intersperseTR___redArg(v___x_381_, v_rowString_380_);
v___x_383_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1));
v___x_384_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_383_, v___x_382_);
lean_dec(v___x_382_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_a_372_);
lean_ctor_set(v___x_377_, 0, v___x_384_);
v___x_386_ = v___x_377_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_a_372_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v_a_371_ = v_tail_375_;
v_a_372_ = v___x_386_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_adjToString(lean_object* v_n_391_, lean_object* v_G_392_){
_start:
{
lean_object* v_rows_393_; lean_object* v___x_394_; lean_object* v_rowStrings_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_rows_393_ = l_List_finRange(v_n_391_);
v___x_394_ = lean_box(0);
lean_inc(v_rows_393_);
v_rowStrings_395_ = lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(v_G_392_, v_rows_393_, v_rows_393_, v___x_394_);
v___x_396_ = ((lean_object*)(lp_hello_x2dworld_Graph_AdjMatrix_adjToString___closed__0));
v___x_397_ = l_List_intersperseTR___redArg(v___x_396_, v_rowStrings_395_);
v___x_398_ = ((lean_object*)(lp_hello_x2dworld_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1));
v___x_399_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_398_, v___x_397_);
lean_dec(v___x_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_instToString___lam__0(lean_object* v_n_400_, lean_object* v_G_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lp_hello_x2dworld_Graph_AdjMatrix_adjToString(v_n_400_, v_G_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* lp_hello_x2dworld_Graph_AdjMatrix_instToString(lean_object* v_n_403_){
_start:
{
lean_object* v___f_404_; 
v___f_404_ = lean_alloc_closure((void*)(lp_hello_x2dworld_Graph_AdjMatrix_instToString___lam__0), 2, 1);
lean_closure_set(v___f_404_, 0, v_n_403_);
return v___f_404_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_aesop_Aesop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_hello_x2dworld_GraphStructureAttempt1(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_aesop_Aesop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
