// Lean compiler output
// Module: LeanGraphCanonizerV4
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
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_range(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Graph"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__0_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "AdjMatrix"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__1_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≃_"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__2_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 36, 206, 233, 246, 43, 71, 96)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_0),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 144, 243, 39, 60, 12, 127, 183)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value_aux_1),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 92, 145, 90, 179, 71, 65, 151)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__4 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__4_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__5 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__5_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≃ "};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__6 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__6_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__6_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__7 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__7_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__8 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__8_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__9 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__9_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__10 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__10_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__5_value),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__7_value),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__10_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__11 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__11_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__11_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__12 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__12_value;
LEAN_EXPORT const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243__ = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__12_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_0),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_1),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_2),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Isomorphic"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(240, 190, 20, 130, 109, 57, 74, 242)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 36, 206, 233, 246, 43, 71, 96)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_0),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 144, 243, 39, 60, 12, 127, 183)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_1),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 168, 201, 31, 52, 68, 229)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0_value;
static const lean_string_object lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_instToString(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_bottom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_bottom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_inner_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_inner_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Graph.PathSegment.bottom"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__0_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__0_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__1_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__2_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Graph.PathSegment.inner"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__5 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__5_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__5_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__6 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__6_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__7 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__7_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GraphCanonizationProofs_Graph_instReprPathSegment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment___closed__0_value;
LEAN_EXPORT const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathSegment___closed__0_value;
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_instBEqPathSegment_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instBEqPathSegment_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GraphCanonizationProofs_Graph_instBEqPathSegment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GraphCanonizationProofs_Graph_instBEqPathSegment_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GraphCanonizationProofs_Graph_instBEqPathSegment___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instBEqPathSegment___closed__0_value;
LEAN_EXPORT const lean_object* lp_GraphCanonizationProofs_Graph_instBEqPathSegment = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instBEqPathSegment___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__0_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "depth"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__1_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__1_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__2_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__2_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__3 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__3_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__4 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__4_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__4_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__5 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__5_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__3_value),((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__5_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__6 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__6_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "startVertexIndex"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__8 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__8_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__8_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__9 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__9_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "endVertexIndex"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__11 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__11_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__11_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__12 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__12_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__13;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "connectedSubPaths"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__14 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__14_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__14_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__15 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__15_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__16;
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__17 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__17_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__18;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__0_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__20 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__20_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__17_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__21 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__21_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GraphCanonizationProofs_Graph_instReprPathsBetween___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween___closed__0_value;
LEAN_EXPORT const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsBetween___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "pathsToVertex"};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__0_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__0_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__1_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GraphCanonizationProofs_Graph_instReprPathsFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsFrom___closed__0_value;
LEAN_EXPORT const lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom = (const lean_object*)&lp_GraphCanonizationProofs_Graph_instReprPathsFrom___closed__0_value;
static const lean_array_object lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0_value;
static const lean_array_object lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getBetween(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getBetween___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getFrom(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_getArrayRank(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_insertSorted___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_insertSorted(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_sortBy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_sortBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0___boxed(lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "LeanGraphCanonizerV4"};
static const lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__0_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Graph.comparePathSegments"};
static const lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__1_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Cannot compare bottom and inner PathSegments"};
static const lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__2_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3;
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathSegments(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathsBetween(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathsBetween___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathsFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_initializePaths(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_assignRanks_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_assignRanks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_setBetween(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_setBetween___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__0(lean_object*, lean_object*);
static const lean_array_object lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_calculatePathRankings(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_convergeOnce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_convergeOnce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_convergeOnce(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_convergeLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_breakTie_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_breakTie_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderVertices_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderVertices(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___closed__0;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___closed__0_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_labelEdgesAccordingToRankings(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_labelEdgesAccordingToRankings___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0(lean_object* v_vertex1_1_, lean_object* v_vertex2_2_, lean_object* v_G_3_, lean_object* v_fromVertex_4_, lean_object* v_toVertex_5_){
_start:
{
uint8_t v___x_6_; uint8_t v___x_7_; lean_object* v___y_9_; 
v___x_6_ = lean_nat_dec_eq(v_fromVertex_4_, v_vertex1_1_);
v___x_7_ = lean_nat_dec_eq(v_toVertex_5_, v_vertex1_1_);
if (v___x_6_ == 0)
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_fromVertex_4_, v_vertex2_2_);
if (v___x_14_ == 0)
{
v___y_9_ = v_fromVertex_4_;
goto v___jp_8_;
}
else
{
lean_dec(v_fromVertex_4_);
lean_inc(v_vertex1_1_);
v___y_9_ = v_vertex1_1_;
goto v___jp_8_;
}
}
else
{
lean_dec(v_fromVertex_4_);
lean_inc(v_vertex2_2_);
v___y_9_ = v_vertex2_2_;
goto v___jp_8_;
}
v___jp_8_:
{
if (v___x_7_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_eq(v_toVertex_5_, v_vertex2_2_);
lean_dec(v_vertex2_2_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec(v_vertex1_1_);
v___x_11_ = lean_apply_2(v_G_3_, v___y_9_, v_toVertex_5_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
lean_dec(v_toVertex_5_);
v___x_12_ = lean_apply_2(v_G_3_, v___y_9_, v_vertex1_1_);
return v___x_12_;
}
}
else
{
lean_object* v___x_13_; 
lean_dec(v_toVertex_5_);
lean_dec(v_vertex1_1_);
v___x_13_ = lean_apply_2(v_G_3_, v___y_9_, v_vertex2_2_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg(lean_object* v_vertex1_15_, lean_object* v_vertex2_16_, lean_object* v_G_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v___f_18_, 0, v_vertex1_15_);
lean_closure_set(v___f_18_, 1, v_vertex2_16_);
lean_closure_set(v___f_18_, 2, v_G_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices(lean_object* v_vertexCount_19_, lean_object* v_vertex1_20_, lean_object* v_vertex2_21_, lean_object* v_G_22_){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v___f_23_, 0, v_vertex1_20_);
lean_closure_set(v___f_23_, 1, v_vertex2_21_);
lean_closure_set(v___f_23_, 2, v_G_22_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___boxed(lean_object* v_vertexCount_24_, lean_object* v_vertex1_25_, lean_object* v_vertex2_26_, lean_object* v_G_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices(v_vertexCount_24_, v_vertex1_25_, v_vertex2_26_, v_G_27_);
lean_dec(v_vertexCount_24_);
return v_res_28_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5));
v___x_68_ = l_String_toRawSubstring_x27(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1(lean_object* v_x_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3));
lean_inc(v_x_89_);
v___x_93_ = l_Lean_Syntax_isOfKind(v_x_89_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_x_89_);
v___x_94_ = lean_box(1);
v___x_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_a_91_);
return v___x_95_;
}
else
{
lean_object* v_quotContext_96_; lean_object* v_currMacroScope_97_; lean_object* v_ref_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_quotContext_96_ = lean_ctor_get(v_a_90_, 1);
v_currMacroScope_97_ = lean_ctor_get(v_a_90_, 2);
v_ref_98_ = lean_ctor_get(v_a_90_, 5);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_Lean_Syntax_getArg(v_x_89_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = l_Lean_Syntax_getArg(v_x_89_, v___x_101_);
lean_dec(v_x_89_);
v___x_103_ = 0;
v___x_104_ = l_Lean_SourceInfo_fromRef(v_ref_98_, v___x_103_);
v___x_105_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4));
v___x_106_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6, &lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6_once, _init_lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6);
v___x_107_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7));
lean_inc(v_currMacroScope_97_);
lean_inc(v_quotContext_96_);
v___x_108_ = l_Lean_addMacroScope(v_quotContext_96_, v___x_107_, v_currMacroScope_97_);
v___x_109_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12));
lean_inc_n(v___x_104_, 2);
v___x_110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_110_, 0, v___x_104_);
lean_ctor_set(v___x_110_, 1, v___x_106_);
lean_ctor_set(v___x_110_, 2, v___x_108_);
lean_ctor_set(v___x_110_, 3, v___x_109_);
v___x_111_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14));
v___x_112_ = l_Lean_Syntax_node2(v___x_104_, v___x_111_, v___x_100_, v___x_102_);
v___x_113_ = l_Lean_Syntax_node2(v___x_104_, v___x_105_, v___x_110_, v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_91_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___boxed(lean_object* v_x_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1(v_x_115_, v_a_116_, v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4));
lean_inc(v_x_122_);
v___x_126_ = l_Lean_Syntax_isOfKind(v_x_122_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_x_122_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Lean_Syntax_getArg(v_x_122_, v___x_129_);
v___x_131_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1));
lean_inc(v___x_130_);
v___x_132_ = l_Lean_Syntax_isOfKind(v___x_130_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v___x_130_);
lean_dec(v_x_122_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v_a_124_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_122_, v___x_135_);
lean_dec(v_x_122_);
v___x_137_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_136_);
v___x_138_ = l_Lean_Syntax_matchesNull(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_dec(v___x_136_);
lean_dec(v___x_130_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v_a_124_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_ref_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_141_ = l_Lean_Syntax_getArg(v___x_136_, v___x_129_);
v___x_142_ = l_Lean_Syntax_getArg(v___x_136_, v___x_135_);
lean_dec(v___x_136_);
v_ref_143_ = l_Lean_replaceRef(v___x_130_, v_a_123_);
lean_dec(v___x_130_);
v___x_144_ = 0;
v___x_145_ = l_Lean_SourceInfo_fromRef(v_ref_143_, v___x_144_);
lean_dec(v_ref_143_);
v___x_146_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__3));
v___x_147_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__6));
lean_inc(v___x_145_);
v___x_148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_145_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_Lean_Syntax_node3(v___x_145_, v___x_146_, v___x_141_, v___x_148_, v___x_142_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_124_);
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1___boxed(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__LeanGraphCanonizerV4______unexpand__Graph__AdjMatrix__Isomorphic__1(v_x_151_, v_a_152_, v_a_153_);
lean_dec(v_a_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(lean_object* v_G_155_, lean_object* v_rowIdx_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
if (lean_obj_tag(v_a_157_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_rowIdx_156_);
lean_dec_ref(v_G_155_);
v___x_159_ = l_List_reverse___redArg(v_a_158_);
return v___x_159_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_171_; 
v_head_160_ = lean_ctor_get(v_a_157_, 0);
v_tail_161_ = lean_ctor_get(v_a_157_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_171_ == 0)
{
v___x_163_ = v_a_157_;
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_tail_161_);
lean_inc(v_head_160_);
lean_dec(v_a_157_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_inc_ref(v_G_155_);
lean_inc(v_rowIdx_156_);
v___x_165_ = lean_apply_2(v_G_155_, v_rowIdx_156_, v_head_160_);
v___x_166_ = l_Int_repr(v___x_165_);
lean_dec(v___x_165_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v_a_158_);
lean_ctor_set(v___x_163_, 0, v___x_166_);
v___x_168_ = v___x_163_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_a_158_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_a_157_ = v_tail_161_;
v_a_158_ = v___x_168_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(lean_object* v_G_174_, lean_object* v_rowIndices_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_object* v___x_178_; 
lean_dec(v_rowIndices_175_);
lean_dec_ref(v_G_174_);
v___x_178_ = l_List_reverse___redArg(v_a_177_);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v_tail_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_194_; 
v_head_179_ = lean_ctor_get(v_a_176_, 0);
v_tail_180_ = lean_ctor_get(v_a_176_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_194_ == 0)
{
v___x_182_ = v_a_176_;
v_isShared_183_ = v_isSharedCheck_194_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_tail_180_);
lean_inc(v_head_179_);
lean_dec(v_a_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_194_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v_colValues_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_184_ = lean_box(0);
lean_inc(v_rowIndices_175_);
lean_inc_ref(v_G_174_);
v_colValues_185_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(v_G_174_, v_head_179_, v_rowIndices_175_, v___x_184_);
v___x_186_ = ((lean_object*)(lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0));
v___x_187_ = l_List_intersperseTR___redArg(v___x_186_, v_colValues_185_);
v___x_188_ = ((lean_object*)(lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1));
v___x_189_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_188_, v___x_187_);
lean_dec(v___x_187_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_a_177_);
lean_ctor_set(v___x_182_, 0, v___x_189_);
v___x_191_ = v___x_182_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_a_177_);
v___x_191_ = v_reuseFailAlloc_193_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
v_a_176_ = v_tail_180_;
v_a_177_ = v___x_191_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString(lean_object* v_vertexCount_196_, lean_object* v_G_197_){
_start:
{
lean_object* v_rowIndices_198_; lean_object* v___x_199_; lean_object* v_rowStrings_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_rowIndices_198_ = l_List_finRange(v_vertexCount_196_);
v___x_199_ = lean_box(0);
lean_inc(v_rowIndices_198_);
v_rowStrings_200_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(v_G_197_, v_rowIndices_198_, v_rowIndices_198_, v___x_199_);
v___x_201_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString___closed__0));
v___x_202_ = l_List_intersperseTR___redArg(v___x_201_, v_rowStrings_200_);
v___x_203_ = ((lean_object*)(lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1));
v___x_204_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_203_, v___x_202_);
lean_dec(v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_instToString(lean_object* v_vertexCount_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString), 2, 1);
lean_closure_set(v___x_206_, 0, v_vertexCount_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorIdx(lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
return v___x_208_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(1u);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorIdx___boxed(lean_object* v_x_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorIdx(v_x_210_);
lean_dec_ref(v_x_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(lean_object* v_t_212_, lean_object* v_k_213_){
_start:
{
if (lean_obj_tag(v_t_212_) == 0)
{
lean_object* v_vertexIndex_214_; lean_object* v___x_215_; 
v_vertexIndex_214_ = lean_ctor_get(v_t_212_, 0);
lean_inc(v_vertexIndex_214_);
lean_dec_ref(v_t_212_);
v___x_215_ = lean_apply_1(v_k_213_, v_vertexIndex_214_);
return v___x_215_;
}
else
{
lean_object* v_edgeType_216_; lean_object* v_subDepth_217_; lean_object* v_subStart_218_; lean_object* v_subEnd_219_; lean_object* v___x_220_; 
v_edgeType_216_ = lean_ctor_get(v_t_212_, 0);
lean_inc(v_edgeType_216_);
v_subDepth_217_ = lean_ctor_get(v_t_212_, 1);
lean_inc(v_subDepth_217_);
v_subStart_218_ = lean_ctor_get(v_t_212_, 2);
lean_inc(v_subStart_218_);
v_subEnd_219_ = lean_ctor_get(v_t_212_, 3);
lean_inc(v_subEnd_219_);
lean_dec_ref(v_t_212_);
v___x_220_ = lean_apply_4(v_k_213_, v_edgeType_216_, v_subDepth_217_, v_subStart_218_, v_subEnd_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim(lean_object* v_motive_221_, lean_object* v_ctorIdx_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_k_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(v_t_223_, v_k_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___boxed(lean_object* v_motive_227_, lean_object* v_ctorIdx_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim(v_motive_227_, v_ctorIdx_228_, v_t_229_, v_h_230_, v_k_231_);
lean_dec(v_ctorIdx_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_bottom_elim___redArg(lean_object* v_t_233_, lean_object* v_bottom_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(v_t_233_, v_bottom_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_bottom_elim(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_bottom_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(v_t_237_, v_bottom_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_inner_elim___redArg(lean_object* v_t_241_, lean_object* v_inner_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(v_t_241_, v_inner_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_PathSegment_inner_elim(lean_object* v_motive_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_inner_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lp_GraphCanonizationProofs_Graph_PathSegment_ctorElim___redArg(v_t_245_, v_inner_247_);
return v___x_248_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(2u);
v___x_256_ = lean_nat_to_int(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_to_int(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_nat_to_int(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr(lean_object* v_x_267_, lean_object* v_prec_268_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
lean_object* v_vertexIndex_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_289_; 
v_vertexIndex_269_ = lean_ctor_get(v_x_267_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_289_ == 0)
{
v___x_271_ = v_x_267_;
v_isShared_272_ = v_isSharedCheck_289_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_vertexIndex_269_);
lean_dec(v_x_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_289_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___y_274_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_286_ = lean_nat_dec_le(v___x_285_, v_prec_268_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3);
v___y_274_ = v___x_287_;
goto v___jp_273_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4);
v___y_274_ = v___x_288_;
goto v___jp_273_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__2));
v___x_276_ = l_Nat_reprFast(v_vertexIndex_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 3);
lean_ctor_set(v___x_271_, 0, v___x_276_);
v___x_278_ = v___x_271_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_284_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_275_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
lean_inc(v___y_274_);
v___x_280_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_280_, 0, v___y_274_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = 0;
v___x_282_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*1, v___x_281_);
v___x_283_ = l_Repr_addAppParen(v___x_282_, v_prec_268_);
return v___x_283_;
}
}
}
}
else
{
lean_object* v_edgeType_290_; lean_object* v_subDepth_291_; lean_object* v_subStart_292_; lean_object* v_subEnd_293_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_317_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_edgeType_290_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_edgeType_290_);
v_subDepth_291_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_subDepth_291_);
v_subStart_292_ = lean_ctor_get(v_x_267_, 2);
lean_inc(v_subStart_292_);
v_subEnd_293_ = lean_ctor_get(v_x_267_, 3);
lean_inc(v_subEnd_293_);
lean_dec_ref(v_x_267_);
v___x_328_ = lean_unsigned_to_nat(1024u);
v___x_329_ = lean_nat_dec_le(v___x_328_, v_prec_268_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3);
v___y_317_ = v___x_330_;
goto v___jp_316_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4);
v___y_317_ = v___x_331_;
goto v___jp_316_;
}
v___jp_294_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc(v___y_295_);
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_295_);
lean_ctor_set(v___x_299_, 1, v___y_298_);
lean_inc_n(v___y_297_, 3);
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___y_297_);
v___x_301_ = l_Nat_reprFast(v_subDepth_291_);
v___x_302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___y_297_);
v___x_305_ = l_Nat_reprFast(v_subStart_292_);
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___y_297_);
v___x_309_ = l_Nat_reprFast(v_subEnd_293_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_308_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
lean_inc(v___y_296_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___y_296_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = 0;
v___x_314_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*1, v___x_313_);
v___x_315_ = l_Repr_addAppParen(v___x_314_, v_prec_268_);
return v___x_315_;
}
v___jp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_box(1);
v___x_319_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__7));
v___x_320_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_321_ = lean_int_dec_lt(v_edgeType_290_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_Int_repr(v_edgeType_290_);
lean_dec(v_edgeType_290_);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___y_295_ = v___x_319_;
v___y_296_ = v___y_317_;
v___y_297_ = v___x_318_;
v___y_298_ = v___x_323_;
goto v___jp_294_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = lean_unsigned_to_nat(1024u);
v___x_325_ = l_Int_repr(v_edgeType_290_);
lean_dec(v_edgeType_290_);
v___x_326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___x_327_ = l_Repr_addAppParen(v___x_326_, v___x_324_);
v___y_295_ = v___x_319_;
v___y_296_ = v___y_317_;
v___y_297_ = v___x_318_;
v___y_298_ = v___x_327_;
goto v___jp_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___boxed(lean_object* v_x_332_, lean_object* v_prec_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr(v_x_332_, v_prec_333_);
lean_dec(v_prec_333_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_instBEqPathSegment_beq(lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v_vertexIndex_339_; lean_object* v_vertexIndex_340_; uint8_t v___x_341_; 
v_vertexIndex_339_ = lean_ctor_get(v_x_337_, 0);
v_vertexIndex_340_ = lean_ctor_get(v_x_338_, 0);
v___x_341_ = lean_nat_dec_eq(v_vertexIndex_339_, v_vertexIndex_340_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = 0;
return v___x_342_;
}
}
else
{
if (lean_obj_tag(v_x_338_) == 1)
{
lean_object* v_edgeType_343_; lean_object* v_subDepth_344_; lean_object* v_subStart_345_; lean_object* v_subEnd_346_; lean_object* v_edgeType_347_; lean_object* v_subDepth_348_; lean_object* v_subStart_349_; lean_object* v_subEnd_350_; uint8_t v___x_351_; 
v_edgeType_343_ = lean_ctor_get(v_x_337_, 0);
v_subDepth_344_ = lean_ctor_get(v_x_337_, 1);
v_subStart_345_ = lean_ctor_get(v_x_337_, 2);
v_subEnd_346_ = lean_ctor_get(v_x_337_, 3);
v_edgeType_347_ = lean_ctor_get(v_x_338_, 0);
v_subDepth_348_ = lean_ctor_get(v_x_338_, 1);
v_subStart_349_ = lean_ctor_get(v_x_338_, 2);
v_subEnd_350_ = lean_ctor_get(v_x_338_, 3);
v___x_351_ = lean_int_dec_eq(v_edgeType_343_, v_edgeType_347_);
if (v___x_351_ == 0)
{
return v___x_351_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_eq(v_subDepth_344_, v_subDepth_348_);
if (v___x_352_ == 0)
{
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = lean_nat_dec_eq(v_subStart_345_, v_subStart_349_);
if (v___x_353_ == 0)
{
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_eq(v_subEnd_346_, v_subEnd_350_);
return v___x_354_;
}
}
}
}
else
{
uint8_t v___x_355_; 
v___x_355_ = 0;
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instBEqPathSegment_beq___boxed(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = lp_GraphCanonizationProofs_Graph_instBEqPathSegment_beq(v_x_356_, v_x_357_);
lean_dec_ref(v_x_357_);
lean_dec_ref(v_x_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_dec(v_x_362_);
return v_x_363_;
}
else
{
lean_object* v_head_365_; lean_object* v_tail_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_377_; 
v_head_365_ = lean_ctor_get(v_x_364_, 0);
v_tail_366_ = lean_ctor_get(v_x_364_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_377_ == 0)
{
v___x_368_ = v_x_364_;
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_tail_366_);
lean_inc(v_head_365_);
lean_dec(v_x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_377_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
lean_inc(v_x_362_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 5);
lean_ctor_set(v___x_368_, 1, v_x_362_);
lean_ctor_set(v___x_368_, 0, v_x_363_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_x_363_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_x_362_);
v___x_371_ = v_reuseFailAlloc_376_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr(v_head_365_, v___x_372_);
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_371_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v_x_363_ = v___x_374_;
v_x_364_ = v_tail_366_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0_spec__1(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_dec(v_x_378_);
return v_x_379_;
}
else
{
lean_object* v_head_381_; lean_object* v_tail_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_393_; 
v_head_381_ = lean_ctor_get(v_x_380_, 0);
v_tail_382_ = lean_ctor_get(v_x_380_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_384_ = v_x_380_;
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_tail_382_);
lean_inc(v_head_381_);
lean_dec(v_x_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_393_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
lean_inc(v_x_378_);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 5);
lean_ctor_set(v___x_384_, 1, v_x_378_);
lean_ctor_set(v___x_384_, 0, v_x_379_);
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_x_379_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_x_378_);
v___x_387_ = v_reuseFailAlloc_392_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr(v_head_381_, v___x_388_);
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_387_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lp_GraphCanonizationProofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0_spec__1_spec__2(v_x_378_, v___x_390_, v_tail_382_);
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0___lam__0(lean_object* v___y_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr(v___y_394_, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0(lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_object* v___x_399_; 
lean_dec(v_x_398_);
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v_tail_400_; 
v_tail_400_ = lean_ctor_get(v_x_397_, 1);
if (lean_obj_tag(v_tail_400_) == 0)
{
lean_object* v_head_401_; lean_object* v___x_402_; 
lean_dec(v_x_398_);
v_head_401_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_head_401_);
lean_dec_ref(v_x_397_);
v___x_402_ = lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0___lam__0(v_head_401_);
return v___x_402_;
}
else
{
lean_object* v_head_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_inc(v_tail_400_);
v_head_403_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_head_403_);
lean_dec_ref(v_x_397_);
v___x_404_ = lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0___lam__0(v_head_403_);
v___x_405_ = lp_GraphCanonizationProofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0_spec__1(v_x_398_, v___x_404_, v_tail_400_);
return v___x_405_;
}
}
}
}
static lean_object* _init_lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__2));
v___x_418_ = lean_string_length(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__7, &lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__7_once, _init_lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__7);
v___x_420_ = lean_nat_to_int(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg(lean_object* v_a_425_){
_start:
{
if (lean_obj_tag(v_a_425_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__1));
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; 
v___x_427_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__5));
v___x_428_ = lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsBetween_repr_spec__0_spec__0(v_a_425_, v___x_427_);
v___x_429_ = lean_obj_once(&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8, &lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8_once, _init_lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8);
v___x_430_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__9));
v___x_431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___x_428_);
v___x_432_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__10));
v___x_433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_429_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = 0;
v___x_436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_435_);
return v___x_436_;
}
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(9u);
v___x_451_ = lean_nat_to_int(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(20u);
v___x_456_ = lean_nat_to_int(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(18u);
v___x_461_ = lean_nat_to_int(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(21u);
v___x_466_ = lean_nat_to_int(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__0));
v___x_469_ = lean_string_length(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__18, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__18_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__18);
v___x_471_ = lean_nat_to_int(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(lean_object* v_x_476_){
_start:
{
lean_object* v_depth_477_; lean_object* v_startVertexIndex_478_; lean_object* v_endVertexIndex_479_; lean_object* v_connectedSubPaths_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_depth_477_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_depth_477_);
v_startVertexIndex_478_ = lean_ctor_get(v_x_476_, 1);
lean_inc(v_startVertexIndex_478_);
v_endVertexIndex_479_ = lean_ctor_get(v_x_476_, 2);
lean_inc(v_endVertexIndex_479_);
v_connectedSubPaths_480_ = lean_ctor_get(v_x_476_, 3);
lean_inc(v_connectedSubPaths_480_);
lean_dec_ref(v_x_476_);
v___x_481_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__5));
v___x_482_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__6));
v___x_483_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7);
v___x_484_ = l_Nat_reprFast(v_depth_477_);
v___x_485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
v___x_486_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_483_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = 0;
v___x_488_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*1, v___x_487_);
v___x_489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_482_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__4));
v___x_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = lean_box(1);
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__9));
v___x_495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_481_);
v___x_497_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10);
v___x_498_ = l_Nat_reprFast(v_startVertexIndex_478_);
v___x_499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_497_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_487_);
v___x_502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_496_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_490_);
v___x_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_492_);
v___x_505_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__12));
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_481_);
v___x_508_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__13, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__13_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__13);
v___x_509_ = l_Nat_reprFast(v_endVertexIndex_479_);
v___x_510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_508_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_487_);
v___x_513_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_507_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_490_);
v___x_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_492_);
v___x_516_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__15));
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_481_);
v___x_519_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__16, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__16_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__16);
v___x_520_ = lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg(v_connectedSubPaths_480_);
v___x_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_487_);
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_518_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19);
v___x_525_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__20));
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_523_);
v___x_527_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__21));
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_524_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_487_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr(lean_object* v_x_531_, lean_object* v_prec_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(v_x_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___boxed(lean_object* v_x_534_, lean_object* v_prec_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr(v_x_534_, v_prec_535_);
lean_dec(v_prec_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0(lean_object* v_a_537_, lean_object* v_n_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg(v_a_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___boxed(lean_object* v_a_540_, lean_object* v_n_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0(v_a_540_, v_n_541_);
lean_dec(v_n_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_dec(v_x_545_);
return v_x_546_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_head_548_ = lean_ctor_get(v_x_547_, 0);
v_tail_549_ = lean_ctor_get(v_x_547_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_559_ == 0)
{
v___x_551_ = v_x_547_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_tail_549_);
lean_inc(v_head_548_);
lean_dec(v_x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
lean_inc(v_x_545_);
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 5);
lean_ctor_set(v___x_551_, 1, v_x_545_);
lean_ctor_set(v___x_551_, 0, v_x_546_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_x_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_x_545_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(v_head_548_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v_x_546_ = v___x_556_;
v_x_547_ = v_tail_549_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0_spec__1(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_dec(v_x_560_);
return v_x_561_;
}
else
{
lean_object* v_head_563_; lean_object* v_tail_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_574_; 
v_head_563_ = lean_ctor_get(v_x_562_, 0);
v_tail_564_ = lean_ctor_get(v_x_562_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_574_ == 0)
{
v___x_566_ = v_x_562_;
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_tail_564_);
lean_inc(v_head_563_);
lean_dec(v_x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_574_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
lean_inc(v_x_560_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 5);
lean_ctor_set(v___x_566_, 1, v_x_560_);
lean_ctor_set(v___x_566_, 0, v_x_561_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_x_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_x_560_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(v_head_563_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lp_GraphCanonizationProofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0_spec__1_spec__2(v_x_560_, v___x_571_, v_tail_564_);
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_577_; 
lean_dec(v_x_576_);
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v_tail_578_; 
v_tail_578_ = lean_ctor_get(v_x_575_, 1);
if (lean_obj_tag(v_tail_578_) == 0)
{
lean_object* v_head_579_; lean_object* v___x_580_; 
lean_dec(v_x_576_);
v_head_579_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_head_579_);
lean_dec_ref(v_x_575_);
v___x_580_ = lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(v_head_579_);
return v___x_580_;
}
else
{
lean_object* v_head_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc(v_tail_578_);
v_head_581_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_head_581_);
lean_dec_ref(v_x_575_);
v___x_582_ = lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg(v_head_581_);
v___x_583_ = lp_GraphCanonizationProofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0_spec__1(v_x_576_, v___x_582_, v_tail_578_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0___redArg(lean_object* v_a_584_){
_start:
{
if (lean_obj_tag(v_a_584_) == 0)
{
lean_object* v___x_585_; 
v___x_585_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__1));
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; 
v___x_586_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__5));
v___x_587_ = lp_GraphCanonizationProofs_Std_Format_joinSep___at___00List_repr___at___00Graph_instReprPathsFrom_repr_spec__0_spec__0(v_a_584_, v___x_586_);
v___x_588_ = lean_obj_once(&lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8, &lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8_once, _init_lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__8);
v___x_589_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__9));
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_587_);
v___x_591_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__10));
v___x_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_588_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = 0;
v___x_595_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*1, v___x_594_);
return v___x_595_;
}
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(17u);
v___x_600_ = lean_nat_to_int(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg(lean_object* v_x_601_){
_start:
{
lean_object* v_depth_602_; lean_object* v_startVertexIndex_603_; lean_object* v_pathsToVertex_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_depth_602_ = lean_ctor_get(v_x_601_, 0);
lean_inc(v_depth_602_);
v_startVertexIndex_603_ = lean_ctor_get(v_x_601_, 1);
lean_inc(v_startVertexIndex_603_);
v_pathsToVertex_604_ = lean_ctor_get(v_x_601_, 2);
lean_inc(v_pathsToVertex_604_);
lean_dec_ref(v_x_601_);
v___x_605_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__5));
v___x_606_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__6));
v___x_607_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__7);
v___x_608_ = l_Nat_reprFast(v_depth_602_);
v___x_609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___x_610_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_607_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = 0;
v___x_612_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*1, v___x_611_);
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_606_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = ((lean_object*)(lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsBetween_repr_spec__0___redArg___closed__4));
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_box(1);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__9));
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_605_);
v___x_621_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__10);
v___x_622_ = l_Nat_reprFast(v_startVertexIndex_603_);
v___x_623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___x_624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*1, v___x_611_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_620_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_614_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_616_);
v___x_629_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__1));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_605_);
v___x_632_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__2, &lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__2_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg___closed__2);
v___x_633_ = lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0___redArg(v_pathsToVertex_604_);
v___x_634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_611_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_631_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19, &lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__19);
v___x_638_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__20));
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_636_);
v___x_640_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_instReprPathsBetween_repr___redArg___closed__21));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_611_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr(lean_object* v_x_644_, lean_object* v_prec_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___redArg(v_x_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr___boxed(lean_object* v_x_647_, lean_object* v_prec_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = lp_GraphCanonizationProofs_Graph_instReprPathsFrom_repr(v_x_647_, v_prec_648_);
lean_dec(v_prec_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0(lean_object* v_a_650_, lean_object* v_n_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0___redArg(v_a_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0___boxed(lean_object* v_a_653_, lean_object* v_n_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = lp_GraphCanonizationProofs_List_repr___at___00Graph_instReprPathsFrom_repr_spec__0(v_a_653_, v_n_654_);
lean_dec(v_n_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getBetween(lean_object* v_rankState_662_, lean_object* v_depth_663_, lean_object* v_startIdx_664_, lean_object* v_endIdx_665_){
_start:
{
lean_object* v___y_667_; lean_object* v___y_673_; lean_object* v_betweenRanks_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_betweenRanks_678_ = lean_ctor_get(v_rankState_662_, 0);
v___x_679_ = lean_array_get_size(v_betweenRanks_678_);
v___x_680_ = lean_nat_dec_lt(v_depth_663_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1));
v___y_673_ = v___x_681_;
goto v___jp_672_;
}
else
{
lean_object* v___x_682_; 
v___x_682_ = lean_array_fget_borrowed(v_betweenRanks_678_, v_depth_663_);
v___y_673_ = v___x_682_;
goto v___jp_672_;
}
v___jp_666_:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_array_get_size(v___y_667_);
v___x_669_ = lean_nat_dec_lt(v_endIdx_665_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
return v___x_670_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_array_fget_borrowed(v___y_667_, v_endIdx_665_);
lean_inc(v___x_671_);
return v___x_671_;
}
}
v___jp_672_:
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_array_get_size(v___y_673_);
v___x_675_ = lean_nat_dec_lt(v_startIdx_664_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0));
v___y_667_ = v___x_676_;
goto v___jp_666_;
}
else
{
lean_object* v___x_677_; 
v___x_677_ = lean_array_fget_borrowed(v___y_673_, v_startIdx_664_);
v___y_667_ = v___x_677_;
goto v___jp_666_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getBetween___boxed(lean_object* v_rankState_683_, lean_object* v_depth_684_, lean_object* v_startIdx_685_, lean_object* v_endIdx_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = lp_GraphCanonizationProofs_Graph_RankState_getBetween(v_rankState_683_, v_depth_684_, v_startIdx_685_, v_endIdx_686_);
lean_dec(v_endIdx_686_);
lean_dec(v_startIdx_685_);
lean_dec(v_depth_684_);
lean_dec_ref(v_rankState_683_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getFrom(lean_object* v_rankState_688_, lean_object* v_depth_689_, lean_object* v_startIdx_690_){
_start:
{
lean_object* v___y_692_; lean_object* v_fromRanks_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_fromRanks_697_ = lean_ctor_get(v_rankState_688_, 1);
v___x_698_ = lean_array_get_size(v_fromRanks_697_);
v___x_699_ = lean_nat_dec_lt(v_depth_689_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0));
v___y_692_ = v___x_700_;
goto v___jp_691_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_array_fget_borrowed(v_fromRanks_697_, v_depth_689_);
v___y_692_ = v___x_701_;
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_array_get_size(v___y_692_);
v___x_694_ = lean_nat_dec_lt(v_startIdx_690_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
return v___x_695_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_array_fget_borrowed(v___y_692_, v_startIdx_690_);
lean_inc(v___x_696_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_RankState_getFrom___boxed(lean_object* v_rankState_702_, lean_object* v_depth_703_, lean_object* v_startIdx_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = lp_GraphCanonizationProofs_Graph_RankState_getFrom(v_rankState_702_, v_depth_703_, v_startIdx_704_);
lean_dec(v_startIdx_704_);
lean_dec(v_depth_703_);
lean_dec_ref(v_rankState_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(lean_object* v_x_706_, lean_object* v_as_707_, size_t v_i_708_, size_t v_stop_709_, lean_object* v_b_710_){
_start:
{
lean_object* v___y_712_; uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_eq(v_i_708_, v_stop_709_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_array_uget_borrowed(v_as_707_, v_i_708_);
v___x_718_ = lean_int_dec_lt(v___x_717_, v_x_706_);
if (v___x_718_ == 0)
{
v___y_712_ = v_b_710_;
goto v___jp_711_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4);
v___x_720_ = lean_int_add(v_b_710_, v___x_719_);
lean_dec(v_b_710_);
v___y_712_ = v___x_720_;
goto v___jp_711_;
}
}
else
{
return v_b_710_;
}
v___jp_711_:
{
size_t v___x_713_; size_t v___x_714_; 
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_add(v_i_708_, v___x_713_);
v_i_708_ = v___x_714_;
v_b_710_ = v___y_712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0___boxed(lean_object* v_x_721_, lean_object* v_as_722_, lean_object* v_i_723_, lean_object* v_stop_724_, lean_object* v_b_725_){
_start:
{
size_t v_i_boxed_726_; size_t v_stop_boxed_727_; lean_object* v_res_728_; 
v_i_boxed_726_ = lean_unbox_usize(v_i_723_);
lean_dec(v_i_723_);
v_stop_boxed_727_ = lean_unbox_usize(v_stop_724_);
lean_dec(v_stop_724_);
v_res_728_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(v_x_721_, v_as_722_, v_i_boxed_726_, v_stop_boxed_727_, v_b_725_);
lean_dec_ref(v_as_722_);
lean_dec(v_x_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(lean_object* v_arr_729_, size_t v_sz_730_, size_t v_i_731_, lean_object* v_bs_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = lean_usize_dec_lt(v_i_731_, v_sz_730_);
if (v___x_733_ == 0)
{
return v_bs_732_;
}
else
{
lean_object* v_v_734_; lean_object* v___x_735_; lean_object* v_bs_x27_736_; lean_object* v___y_738_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_v_734_ = lean_array_uget(v_bs_732_, v_i_731_);
v___x_735_ = lean_unsigned_to_nat(0u);
v_bs_x27_736_ = lean_array_uset(v_bs_732_, v_i_731_, v___x_735_);
v___x_743_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_744_ = lean_array_get_size(v_arr_729_);
v___x_745_ = lean_nat_dec_lt(v___x_735_, v___x_744_);
if (v___x_745_ == 0)
{
lean_dec(v_v_734_);
v___y_738_ = v___x_743_;
goto v___jp_737_;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_le(v___x_744_, v___x_744_);
if (v___x_746_ == 0)
{
if (v___x_745_ == 0)
{
lean_dec(v_v_734_);
v___y_738_ = v___x_743_;
goto v___jp_737_;
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_744_);
v___x_749_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(v_v_734_, v_arr_729_, v___x_747_, v___x_748_, v___x_743_);
lean_dec(v_v_734_);
v___y_738_ = v___x_749_;
goto v___jp_737_;
}
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_744_);
v___x_752_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(v_v_734_, v_arr_729_, v___x_750_, v___x_751_, v___x_743_);
lean_dec(v_v_734_);
v___y_738_ = v___x_752_;
goto v___jp_737_;
}
}
v___jp_737_:
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_731_, v___x_739_);
v___x_741_ = lean_array_uset(v_bs_x27_736_, v_i_731_, v___y_738_);
v_i_731_ = v___x_740_;
v_bs_732_ = v___x_741_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1___boxed(lean_object* v_arr_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_bs_756_){
_start:
{
size_t v_sz_boxed_757_; size_t v_i_boxed_758_; lean_object* v_res_759_; 
v_sz_boxed_757_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_758_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_759_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(v_arr_753_, v_sz_boxed_757_, v_i_boxed_758_, v_bs_756_);
lean_dec_ref(v_arr_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_getArrayRank(lean_object* v_arr_760_){
_start:
{
size_t v_sz_761_; size_t v___x_762_; lean_object* v___x_763_; 
v_sz_761_ = lean_array_size(v_arr_760_);
v___x_762_ = ((size_t)0ULL);
lean_inc_ref(v_arr_760_);
v___x_763_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(v_arr_760_, v_sz_761_, v___x_762_, v_arr_760_);
lean_dec_ref(v_arr_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_insertSorted___redArg(lean_object* v_cmp_764_, lean_object* v_newItem_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v___x_767_; 
lean_dec_ref(v_cmp_764_);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v_newItem_765_);
lean_ctor_set(v___x_767_, 1, v_x_766_);
return v___x_767_;
}
else
{
lean_object* v_head_768_; lean_object* v_tail_769_; lean_object* v___x_770_; uint8_t v___x_771_; uint8_t v___x_772_; uint8_t v___x_773_; 
v_head_768_ = lean_ctor_get(v_x_766_, 0);
v_tail_769_ = lean_ctor_get(v_x_766_, 1);
lean_inc_ref(v_cmp_764_);
lean_inc(v_head_768_);
lean_inc(v_newItem_765_);
v___x_770_ = lean_apply_2(v_cmp_764_, v_newItem_765_, v_head_768_);
v___x_771_ = 2;
v___x_772_ = lean_unbox(v___x_770_);
v___x_773_ = l_instDecidableEqOrdering(v___x_772_, v___x_771_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v_cmp_764_);
v___x_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_774_, 0, v_newItem_765_);
lean_ctor_set(v___x_774_, 1, v_x_766_);
return v___x_774_;
}
else
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
lean_inc(v_tail_769_);
lean_inc(v_head_768_);
v_isSharedCheck_782_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_783_ = lean_ctor_get(v_x_766_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_x_766_, 0);
lean_dec(v_unused_784_);
v___x_776_ = v_x_766_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_x_766_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lp_GraphCanonizationProofs_Graph_insertSorted___redArg(v_cmp_764_, v_newItem_765_, v_tail_769_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_head_768_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_insertSorted(lean_object* v_00_u03b1_785_, lean_object* v_cmp_786_, lean_object* v_newItem_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lp_GraphCanonizationProofs_Graph_insertSorted___redArg(v_cmp_786_, v_newItem_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_sortBy___redArg(lean_object* v_cmp_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
lean_dec_ref(v_cmp_790_);
return v_x_791_;
}
else
{
lean_object* v_head_792_; lean_object* v_tail_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_head_792_ = lean_ctor_get(v_x_791_, 0);
lean_inc(v_head_792_);
v_tail_793_ = lean_ctor_get(v_x_791_, 1);
lean_inc(v_tail_793_);
lean_dec_ref(v_x_791_);
lean_inc_ref(v_cmp_790_);
v___x_794_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_790_, v_tail_793_);
v___x_795_ = lp_GraphCanonizationProofs_Graph_insertSorted___redArg(v_cmp_790_, v_head_792_, v___x_794_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_sortBy(lean_object* v_00_u03b1_796_, lean_object* v_cmp_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(lean_object* v_cmp_800_, uint8_t v_x_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_dec_ref(v_cmp_800_);
return v_x_801_;
}
else
{
lean_object* v_head_803_; lean_object* v_tail_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; uint8_t v___x_807_; uint8_t v___x_808_; 
v_head_803_ = lean_ctor_get(v_x_802_, 0);
lean_inc(v_head_803_);
v_tail_804_ = lean_ctor_get(v_x_802_, 1);
lean_inc(v_tail_804_);
lean_dec_ref(v_x_802_);
v_fst_805_ = lean_ctor_get(v_head_803_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v_head_803_, 1);
lean_inc(v_snd_806_);
lean_dec(v_head_803_);
v___x_807_ = 1;
v___x_808_ = l_instDecidableEqOrdering(v_x_801_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec(v_snd_806_);
lean_dec(v_fst_805_);
v_x_802_ = v_tail_804_;
goto _start;
}
else
{
lean_object* v___x_810_; uint8_t v___x_811_; 
lean_inc_ref(v_cmp_800_);
v___x_810_ = lean_apply_2(v_cmp_800_, v_fst_805_, v_snd_806_);
v___x_811_ = lean_unbox(v___x_810_);
v_x_801_ = v___x_811_;
v_x_802_ = v_tail_804_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg___boxed(lean_object* v_cmp_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
uint8_t v_x_241__boxed_816_; uint8_t v_res_817_; lean_object* v_r_818_; 
v_x_241__boxed_816_ = lean_unbox(v_x_814_);
v_res_817_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(v_cmp_813_, v_x_241__boxed_816_, v_x_815_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(lean_object* v_cmp_819_, lean_object* v_list1_820_, lean_object* v_list2_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_822_ = l_List_lengthTR___redArg(v_list1_820_);
v___x_823_ = l_List_lengthTR___redArg(v_list2_821_);
v___x_824_ = lean_nat_dec_eq(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
lean_dec(v_list2_821_);
lean_dec(v_list1_820_);
lean_dec_ref(v_cmp_819_);
v___x_825_ = lean_nat_dec_lt(v___x_822_, v___x_823_);
lean_dec(v___x_823_);
lean_dec(v___x_822_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = 2;
return v___x_827_;
}
}
else
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
lean_dec(v___x_823_);
lean_dec(v___x_822_);
v___x_828_ = 1;
lean_inc_ref_n(v_cmp_819_, 2);
v___x_829_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_819_, v_list1_820_);
v___x_830_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_819_, v_list2_821_);
v___x_831_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v___x_829_, v___x_830_);
v___x_832_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(v_cmp_819_, v___x_828_, v___x_831_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg___boxed(lean_object* v_cmp_833_, lean_object* v_list1_834_, lean_object* v_list2_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v_cmp_833_, v_list1_834_, v_list2_835_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp(lean_object* v_00_u03b1_838_, lean_object* v_cmp_839_, lean_object* v_list1_840_, lean_object* v_list2_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v_cmp_839_, v_list1_840_, v_list2_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___boxed(lean_object* v_00_u03b1_843_, lean_object* v_cmp_844_, lean_object* v_list1_845_, lean_object* v_list2_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp(v_00_u03b1_843_, v_cmp_844_, v_list1_845_, v_list2_846_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0(lean_object* v_00_u03b1_849_, lean_object* v_cmp_850_, uint8_t v_x_851_, lean_object* v_x_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(v_cmp_850_, v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___boxed(lean_object* v_00_u03b1_854_, lean_object* v_cmp_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
uint8_t v_x_291__boxed_858_; uint8_t v_res_859_; lean_object* v_r_860_; 
v_x_291__boxed_858_ = lean_unbox(v_x_856_);
v_res_859_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0(v_00_u03b1_854_, v_cmp_855_, v_x_291__boxed_858_, v_x_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(lean_object* v_msg_861_){
_start:
{
uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_862_ = 0;
v___x_863_ = lean_box(v___x_862_);
v___x_864_ = lean_panic_fn_borrowed(v___x_863_, v_msg_861_);
lean_dec(v___x_863_);
v___x_865_ = lean_unbox(v___x_864_);
lean_dec(v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0___boxed(lean_object* v_msg_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(v_msg_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_872_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__2));
v___x_873_ = lean_unsigned_to_nat(12u);
v___x_874_ = lean_unsigned_to_nat(112u);
v___x_875_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__1));
v___x_876_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__0));
v___x_877_ = l_mkPanicMessageWithDecl(v___x_876_, v___x_875_, v___x_874_, v___x_873_, v___x_872_);
return v___x_877_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathSegments(lean_object* v_vertexTypes_878_, lean_object* v_betweenRanks_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___y_883_; lean_object* v___y_884_; 
if (lean_obj_tag(v_x_880_) == 0)
{
lean_dec_ref(v_betweenRanks_879_);
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v_vertexIndex_893_; lean_object* v_vertexIndex_894_; lean_object* v___x_895_; lean_object* v___y_897_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_vertexIndex_893_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_vertexIndex_893_);
lean_dec_ref(v_x_880_);
v_vertexIndex_894_ = lean_ctor_get(v_x_881_, 0);
lean_inc(v_vertexIndex_894_);
lean_dec_ref(v_x_881_);
v___x_895_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_901_ = lean_array_get_size(v_vertexTypes_878_);
v___x_902_ = lean_nat_dec_lt(v_vertexIndex_893_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec(v_vertexIndex_893_);
v___y_897_ = v___x_895_;
goto v___jp_896_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = lean_array_fget_borrowed(v_vertexTypes_878_, v_vertexIndex_893_);
lean_dec(v_vertexIndex_893_);
v___y_897_ = v___x_903_;
goto v___jp_896_;
}
v___jp_896_:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_array_get_size(v_vertexTypes_878_);
v___x_899_ = lean_nat_dec_lt(v_vertexIndex_894_, v___x_898_);
if (v___x_899_ == 0)
{
lean_dec(v_vertexIndex_894_);
v___y_883_ = v___y_897_;
v___y_884_ = v___x_895_;
goto v___jp_882_;
}
else
{
lean_object* v___x_900_; 
v___x_900_ = lean_array_fget_borrowed(v_vertexTypes_878_, v_vertexIndex_894_);
lean_dec(v_vertexIndex_894_);
v___y_883_ = v___y_897_;
v___y_884_ = v___x_900_;
goto v___jp_882_;
}
}
}
else
{
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_881_);
goto v___jp_890_;
}
}
else
{
if (lean_obj_tag(v_x_881_) == 1)
{
lean_object* v_edgeType_904_; lean_object* v_subDepth_905_; lean_object* v_subStart_906_; lean_object* v_subEnd_907_; lean_object* v_edgeType_908_; lean_object* v_subDepth_909_; lean_object* v_subStart_910_; lean_object* v_subEnd_911_; lean_object* v_xRank_912_; lean_object* v_yRank_913_; uint8_t v___x_914_; 
v_edgeType_904_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_edgeType_904_);
v_subDepth_905_ = lean_ctor_get(v_x_880_, 1);
lean_inc(v_subDepth_905_);
v_subStart_906_ = lean_ctor_get(v_x_880_, 2);
lean_inc(v_subStart_906_);
v_subEnd_907_ = lean_ctor_get(v_x_880_, 3);
lean_inc(v_subEnd_907_);
lean_dec_ref(v_x_880_);
v_edgeType_908_ = lean_ctor_get(v_x_881_, 0);
lean_inc(v_edgeType_908_);
v_subDepth_909_ = lean_ctor_get(v_x_881_, 1);
lean_inc(v_subDepth_909_);
v_subStart_910_ = lean_ctor_get(v_x_881_, 2);
lean_inc(v_subStart_910_);
v_subEnd_911_ = lean_ctor_get(v_x_881_, 3);
lean_inc(v_subEnd_911_);
lean_dec_ref(v_x_881_);
lean_inc_ref(v_betweenRanks_879_);
v_xRank_912_ = lean_apply_3(v_betweenRanks_879_, v_subDepth_905_, v_subStart_906_, v_subEnd_907_);
v_yRank_913_ = lean_apply_3(v_betweenRanks_879_, v_subDepth_909_, v_subStart_910_, v_subEnd_911_);
v___x_914_ = lean_int_dec_eq(v_xRank_912_, v_yRank_913_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; 
lean_dec(v_edgeType_908_);
lean_dec(v_edgeType_904_);
v___x_915_ = lean_int_dec_lt(v_yRank_913_, v_xRank_912_);
if (v___x_915_ == 0)
{
uint8_t v___x_916_; 
v___x_916_ = lean_int_dec_eq(v_yRank_913_, v_xRank_912_);
lean_dec(v_xRank_912_);
lean_dec(v_yRank_913_);
if (v___x_916_ == 0)
{
uint8_t v___x_917_; 
v___x_917_ = 2;
return v___x_917_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = 1;
return v___x_918_;
}
}
else
{
uint8_t v___x_919_; 
lean_dec(v_yRank_913_);
lean_dec(v_xRank_912_);
v___x_919_ = 0;
return v___x_919_;
}
}
else
{
uint8_t v___x_920_; 
lean_dec(v_yRank_913_);
lean_dec(v_xRank_912_);
v___x_920_ = lean_int_dec_eq(v_edgeType_904_, v_edgeType_908_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
v___x_921_ = lean_int_dec_lt(v_edgeType_908_, v_edgeType_904_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = lean_int_dec_eq(v_edgeType_908_, v_edgeType_904_);
lean_dec(v_edgeType_904_);
lean_dec(v_edgeType_908_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; 
v___x_923_ = 2;
return v___x_923_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = 1;
return v___x_924_;
}
}
else
{
uint8_t v___x_925_; 
lean_dec(v_edgeType_908_);
lean_dec(v_edgeType_904_);
v___x_925_ = 0;
return v___x_925_;
}
}
else
{
uint8_t v___x_926_; 
lean_dec(v_edgeType_908_);
lean_dec(v_edgeType_904_);
v___x_926_ = 1;
return v___x_926_;
}
}
}
else
{
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_881_);
lean_dec_ref(v_betweenRanks_879_);
goto v___jp_890_;
}
}
v___jp_882_:
{
uint8_t v___x_885_; 
v___x_885_ = lean_int_dec_lt(v___y_883_, v___y_884_);
if (v___x_885_ == 0)
{
uint8_t v___x_886_; 
v___x_886_ = lean_int_dec_eq(v___y_883_, v___y_884_);
if (v___x_886_ == 0)
{
uint8_t v___x_887_; 
v___x_887_ = 2;
return v___x_887_;
}
else
{
uint8_t v___x_888_; 
v___x_888_ = 1;
return v___x_888_;
}
}
else
{
uint8_t v___x_889_; 
v___x_889_ = 0;
return v___x_889_;
}
}
v___jp_890_:
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3, &lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3_once, _init_lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3);
v___x_892_ = lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___boxed(lean_object* v_vertexTypes_927_, lean_object* v_betweenRanks_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
uint8_t v_res_931_; lean_object* v_r_932_; 
v_res_931_ = lp_GraphCanonizationProofs_Graph_comparePathSegments(v_vertexTypes_927_, v_betweenRanks_928_, v_x_929_, v_x_930_);
lean_dec_ref(v_vertexTypes_927_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathsBetween(lean_object* v_vertexTypes_933_, lean_object* v_betweenRanks_934_, lean_object* v_pathX_935_, lean_object* v_pathY_936_){
_start:
{
lean_object* v_endVertexIndex_937_; lean_object* v_connectedSubPaths_938_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___x_950_; lean_object* v___y_952_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_endVertexIndex_937_ = lean_ctor_get(v_pathX_935_, 2);
lean_inc(v_endVertexIndex_937_);
v_connectedSubPaths_938_ = lean_ctor_get(v_pathX_935_, 3);
lean_inc(v_connectedSubPaths_938_);
lean_dec_ref(v_pathX_935_);
v___x_950_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_957_ = lean_array_get_size(v_vertexTypes_933_);
v___x_958_ = lean_nat_dec_lt(v_endVertexIndex_937_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_endVertexIndex_937_);
v___y_952_ = v___x_950_;
goto v___jp_951_;
}
else
{
lean_object* v___x_959_; 
v___x_959_ = lean_array_fget_borrowed(v_vertexTypes_933_, v_endVertexIndex_937_);
lean_dec(v_endVertexIndex_937_);
lean_inc(v___x_959_);
v___y_952_ = v___x_959_;
goto v___jp_951_;
}
v___jp_939_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_int_dec_eq(v___y_940_, v___y_941_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; 
lean_dec(v_connectedSubPaths_938_);
lean_dec_ref(v_pathY_936_);
lean_dec_ref(v_betweenRanks_934_);
lean_dec_ref(v_vertexTypes_933_);
v___x_943_ = lean_int_dec_lt(v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
if (v___x_943_ == 0)
{
if (v___x_942_ == 0)
{
uint8_t v___x_944_; 
v___x_944_ = 2;
return v___x_944_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = 1;
return v___x_945_;
}
}
else
{
uint8_t v___x_946_; 
v___x_946_ = 0;
return v___x_946_;
}
}
else
{
lean_object* v_connectedSubPaths_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
lean_dec(v___y_941_);
lean_dec(v___y_940_);
v_connectedSubPaths_947_ = lean_ctor_get(v_pathY_936_, 3);
lean_inc(v_connectedSubPaths_947_);
lean_dec_ref(v_pathY_936_);
v___x_948_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___boxed), 4, 2);
lean_closure_set(v___x_948_, 0, v_vertexTypes_933_);
lean_closure_set(v___x_948_, 1, v_betweenRanks_934_);
v___x_949_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v___x_948_, v_connectedSubPaths_938_, v_connectedSubPaths_947_);
return v___x_949_;
}
}
v___jp_951_:
{
lean_object* v_endVertexIndex_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v_endVertexIndex_953_ = lean_ctor_get(v_pathY_936_, 2);
v___x_954_ = lean_array_get_size(v_vertexTypes_933_);
v___x_955_ = lean_nat_dec_lt(v_endVertexIndex_953_, v___x_954_);
if (v___x_955_ == 0)
{
v___y_940_ = v___y_952_;
v___y_941_ = v___x_950_;
goto v___jp_939_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_array_fget_borrowed(v_vertexTypes_933_, v_endVertexIndex_953_);
lean_inc(v___x_956_);
v___y_940_ = v___y_952_;
v___y_941_ = v___x_956_;
goto v___jp_939_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathsBetween___boxed(lean_object* v_vertexTypes_960_, lean_object* v_betweenRanks_961_, lean_object* v_pathX_962_, lean_object* v_pathY_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = lp_GraphCanonizationProofs_Graph_comparePathsBetween(v_vertexTypes_960_, v_betweenRanks_961_, v_pathX_962_, v_pathY_963_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathsFrom(lean_object* v_vertexTypes_966_, lean_object* v_betweenRanks_967_, lean_object* v_pathX_968_, lean_object* v_pathY_969_){
_start:
{
lean_object* v_startVertexIndex_970_; lean_object* v_pathsToVertex_971_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___x_983_; lean_object* v___y_985_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_startVertexIndex_970_ = lean_ctor_get(v_pathX_968_, 1);
lean_inc(v_startVertexIndex_970_);
v_pathsToVertex_971_ = lean_ctor_get(v_pathX_968_, 2);
lean_inc(v_pathsToVertex_971_);
lean_dec_ref(v_pathX_968_);
v___x_983_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_990_ = lean_array_get_size(v_vertexTypes_966_);
v___x_991_ = lean_nat_dec_lt(v_startVertexIndex_970_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_startVertexIndex_970_);
v___y_985_ = v___x_983_;
goto v___jp_984_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_array_fget_borrowed(v_vertexTypes_966_, v_startVertexIndex_970_);
lean_dec(v_startVertexIndex_970_);
lean_inc(v___x_992_);
v___y_985_ = v___x_992_;
goto v___jp_984_;
}
v___jp_972_:
{
uint8_t v___x_975_; 
v___x_975_ = lean_int_dec_eq(v___y_973_, v___y_974_);
if (v___x_975_ == 0)
{
uint8_t v___x_976_; 
lean_dec(v_pathsToVertex_971_);
lean_dec_ref(v_pathY_969_);
lean_dec_ref(v_betweenRanks_967_);
lean_dec_ref(v_vertexTypes_966_);
v___x_976_ = lean_int_dec_lt(v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
if (v___x_976_ == 0)
{
if (v___x_975_ == 0)
{
uint8_t v___x_977_; 
v___x_977_ = 2;
return v___x_977_;
}
else
{
uint8_t v___x_978_; 
v___x_978_ = 1;
return v___x_978_;
}
}
else
{
uint8_t v___x_979_; 
v___x_979_ = 0;
return v___x_979_;
}
}
else
{
lean_object* v_pathsToVertex_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
lean_dec(v___y_974_);
lean_dec(v___y_973_);
v_pathsToVertex_980_ = lean_ctor_get(v_pathY_969_, 2);
lean_inc(v_pathsToVertex_980_);
lean_dec_ref(v_pathY_969_);
v___x_981_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_comparePathsBetween___boxed), 4, 2);
lean_closure_set(v___x_981_, 0, v_vertexTypes_966_);
lean_closure_set(v___x_981_, 1, v_betweenRanks_967_);
v___x_982_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v___x_981_, v_pathsToVertex_971_, v_pathsToVertex_980_);
return v___x_982_;
}
}
v___jp_984_:
{
lean_object* v_startVertexIndex_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_startVertexIndex_986_ = lean_ctor_get(v_pathY_969_, 1);
v___x_987_ = lean_array_get_size(v_vertexTypes_966_);
v___x_988_ = lean_nat_dec_lt(v_startVertexIndex_986_, v___x_987_);
if (v___x_988_ == 0)
{
v___y_973_ = v___y_985_;
v___y_974_ = v___x_983_;
goto v___jp_972_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_array_fget_borrowed(v_vertexTypes_966_, v_startVertexIndex_986_);
lean_inc(v___x_989_);
v___y_973_ = v___y_985_;
v___y_974_ = v___x_989_;
goto v___jp_972_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathsFrom___boxed(lean_object* v_vertexTypes_993_, lean_object* v_betweenRanks_994_, lean_object* v_pathX_995_, lean_object* v_pathY_996_){
_start:
{
uint8_t v_res_997_; lean_object* v_r_998_; 
v_res_997_ = lp_GraphCanonizationProofs_Graph_comparePathsFrom(v_vertexTypes_993_, v_betweenRanks_994_, v_pathX_995_, v_pathY_996_);
v_r_998_ = lean_box(v_res_997_);
return v_r_998_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0(lean_object* v_G_999_, lean_object* v_endFin_1000_, lean_object* v___x_1001_, lean_object* v___x_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
if (lean_obj_tag(v_a_1003_) == 0)
{
lean_object* v___x_1005_; 
lean_dec(v___x_1002_);
lean_dec(v_endFin_1000_);
lean_dec_ref(v_G_999_);
v___x_1005_ = l_List_reverse___redArg(v_a_1004_);
return v___x_1005_;
}
else
{
lean_object* v_head_1006_; lean_object* v_tail_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1019_; 
v_head_1006_ = lean_ctor_get(v_a_1003_, 0);
v_tail_1007_ = lean_ctor_get(v_a_1003_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_a_1003_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1009_ = v_a_1003_;
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_tail_1007_);
lean_inc(v_head_1006_);
lean_dec(v_a_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1019_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_inc_ref(v_G_999_);
lean_inc(v_endFin_1000_);
lean_inc(v_head_1006_);
v___x_1011_ = lean_apply_2(v_G_999_, v_head_1006_, v_endFin_1000_);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_sub(v___x_1001_, v___x_1012_);
lean_inc(v___x_1002_);
v___x_1014_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_ctor_set(v___x_1014_, 2, v___x_1002_);
lean_ctor_set(v___x_1014_, 3, v_head_1006_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_a_1004_);
lean_ctor_set(v___x_1009_, 0, v___x_1014_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_a_1004_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v_a_1003_ = v_tail_1007_;
v_a_1004_ = v___x_1016_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0___boxed(lean_object* v_G_1020_, lean_object* v_endFin_1021_, lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0(v_G_1020_, v_endFin_1021_, v___x_1022_, v___x_1023_, v_a_1024_, v_a_1025_);
lean_dec(v___x_1022_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg(lean_object* v___x_1027_, lean_object* v_G_1028_, lean_object* v___x_1029_, lean_object* v_vertices_1030_, lean_object* v_x_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
if (lean_obj_tag(v_a_1032_) == 0)
{
lean_object* v___x_1034_; 
lean_dec(v_vertices_1030_);
lean_dec(v___x_1029_);
lean_dec_ref(v_G_1028_);
lean_dec(v___x_1027_);
v___x_1034_ = l_List_reverse___redArg(v_a_1033_);
return v___x_1034_;
}
else
{
lean_object* v_head_1035_; lean_object* v_tail_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1058_; 
v_head_1035_ = lean_ctor_get(v_a_1032_, 0);
v_tail_1036_ = lean_ctor_get(v_a_1032_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_a_1032_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1038_ = v_a_1032_;
v_isShared_1039_ = v_isSharedCheck_1058_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_tail_1036_);
lean_inc(v_head_1035_);
lean_dec(v_a_1032_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1058_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___y_1041_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = lean_nat_dec_eq(v___x_1027_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(0);
lean_inc(v_vertices_1030_);
lean_inc_n(v___x_1029_, 2);
lean_inc(v_head_1035_);
lean_inc_ref(v_G_1028_);
v___x_1049_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0(v_G_1028_, v_head_1035_, v___x_1027_, v___x_1029_, v_vertices_1030_, v___x_1048_);
lean_inc(v___x_1027_);
v___x_1050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1027_);
lean_ctor_set(v___x_1050_, 1, v___x_1029_);
lean_ctor_set(v___x_1050_, 2, v_head_1035_);
lean_ctor_set(v___x_1050_, 3, v___x_1049_);
v___y_1041_ = v___x_1050_;
goto v___jp_1040_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_nat_dec_eq(v_x_1031_, v_head_1035_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
lean_inc(v___x_1029_);
lean_inc(v___x_1027_);
v___x_1053_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1027_);
lean_ctor_set(v___x_1053_, 1, v___x_1029_);
lean_ctor_set(v___x_1053_, 2, v_head_1035_);
lean_ctor_set(v___x_1053_, 3, v___x_1052_);
v___y_1041_ = v___x_1053_;
goto v___jp_1040_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_inc_n(v___x_1029_, 2);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1029_);
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_inc(v___x_1027_);
v___x_1057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1027_);
lean_ctor_set(v___x_1057_, 1, v___x_1029_);
lean_ctor_set(v___x_1057_, 2, v_head_1035_);
lean_ctor_set(v___x_1057_, 3, v___x_1056_);
v___y_1041_ = v___x_1057_;
goto v___jp_1040_;
}
}
v___jp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v_a_1033_);
lean_ctor_set(v___x_1038_, 0, v___y_1041_);
v___x_1043_ = v___x_1038_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___y_1041_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1033_);
v___x_1043_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
v_a_1032_ = v_tail_1036_;
v_a_1033_ = v___x_1043_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg___boxed(lean_object* v___x_1059_, lean_object* v_G_1060_, lean_object* v___x_1061_, lean_object* v_vertices_1062_, lean_object* v_x_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg(v___x_1059_, v_G_1060_, v___x_1061_, v_vertices_1062_, v_x_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_x_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__1(lean_object* v_G_1067_, lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v_vertices_1070_, lean_object* v_vertexCount_1071_, lean_object* v_x_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
if (lean_obj_tag(v_a_1073_) == 0)
{
lean_object* v___x_1075_; 
lean_dec(v_vertices_1070_);
lean_dec(v___x_1069_);
lean_dec(v___x_1068_);
lean_dec_ref(v_G_1067_);
v___x_1075_ = l_List_reverse___redArg(v_a_1074_);
return v___x_1075_;
}
else
{
lean_object* v_head_1076_; lean_object* v_tail_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1099_; 
v_head_1076_ = lean_ctor_get(v_a_1073_, 0);
v_tail_1077_ = lean_ctor_get(v_a_1073_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_1073_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1079_ = v_a_1073_;
v_isShared_1080_ = v_isSharedCheck_1099_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_tail_1077_);
lean_inc(v_head_1076_);
lean_dec(v_a_1073_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1099_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___y_1082_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_nat_dec_eq(v___x_1068_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
lean_inc(v_vertices_1070_);
lean_inc_n(v___x_1069_, 2);
lean_inc(v_head_1076_);
lean_inc_ref(v_G_1067_);
v___x_1090_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__0(v_G_1067_, v_head_1076_, v___x_1068_, v___x_1069_, v_vertices_1070_, v___x_1089_);
lean_inc(v___x_1068_);
v___x_1091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1068_);
lean_ctor_set(v___x_1091_, 1, v___x_1069_);
lean_ctor_set(v___x_1091_, 2, v_head_1076_);
lean_ctor_set(v___x_1091_, 3, v___x_1090_);
v___y_1082_ = v___x_1091_;
goto v___jp_1081_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = lean_nat_dec_eq(v_x_1072_, v_head_1076_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_box(0);
lean_inc(v___x_1069_);
lean_inc(v___x_1068_);
v___x_1094_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1068_);
lean_ctor_set(v___x_1094_, 1, v___x_1069_);
lean_ctor_set(v___x_1094_, 2, v_head_1076_);
lean_ctor_set(v___x_1094_, 3, v___x_1093_);
v___y_1082_ = v___x_1094_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_inc_n(v___x_1069_, 2);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1069_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_inc(v___x_1068_);
v___x_1098_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1068_);
lean_ctor_set(v___x_1098_, 1, v___x_1069_);
lean_ctor_set(v___x_1098_, 2, v_head_1076_);
lean_ctor_set(v___x_1098_, 3, v___x_1097_);
v___y_1082_ = v___x_1098_;
goto v___jp_1081_;
}
}
v___jp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v_a_1074_);
lean_ctor_set(v___x_1079_, 0, v___y_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___y_1082_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_a_1074_);
v___x_1084_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; 
v___x_1085_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg(v___x_1068_, v_G_1067_, v___x_1069_, v_vertices_1070_, v_x_1072_, v_tail_1077_, v___x_1084_);
return v___x_1085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__1___boxed(lean_object* v_G_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v_vertices_1103_, lean_object* v_vertexCount_1104_, lean_object* v_x_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__1(v_G_1100_, v___x_1101_, v___x_1102_, v_vertices_1103_, v_vertexCount_1104_, v_x_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_x_1105_);
lean_dec(v_vertexCount_1104_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2(lean_object* v_x_1109_, lean_object* v_G_1110_, lean_object* v_vertices_1111_, lean_object* v_vertexCount_1112_, size_t v_sz_1113_, size_t v_i_1114_, lean_object* v_bs_1115_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1114_, v_sz_1113_);
if (v___x_1116_ == 0)
{
lean_dec(v_vertices_1111_);
lean_dec_ref(v_G_1110_);
lean_dec(v_x_1109_);
return v_bs_1115_;
}
else
{
lean_object* v_v_1117_; lean_object* v___x_1118_; lean_object* v_bs_x27_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v_v_1117_ = lean_array_uget(v_bs_1115_, v_i_1114_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v_bs_x27_1119_ = lean_array_uset(v_bs_1115_, v_i_1114_, v___x_1118_);
v___x_1120_ = lean_box(0);
lean_inc_n(v_vertices_1111_, 2);
lean_inc(v_v_1117_);
lean_inc_n(v_x_1109_, 2);
lean_inc_ref(v_G_1110_);
v___x_1121_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_initializePaths_spec__1(v_G_1110_, v_x_1109_, v_v_1117_, v_vertices_1111_, v_vertexCount_1112_, v_v_1117_, v_vertices_1111_, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1122_, 0, v_x_1109_);
lean_ctor_set(v___x_1122_, 1, v_v_1117_);
lean_ctor_set(v___x_1122_, 2, v___x_1121_);
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1114_, v___x_1123_);
v___x_1125_ = lean_array_uset(v_bs_x27_1119_, v_i_1114_, v___x_1122_);
v_i_1114_ = v___x_1124_;
v_bs_1115_ = v___x_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2___boxed(lean_object* v_x_1127_, lean_object* v_G_1128_, lean_object* v_vertices_1129_, lean_object* v_vertexCount_1130_, lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_bs_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1136_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2(v_x_1127_, v_G_1128_, v_vertices_1129_, v_vertexCount_1130_, v_sz_boxed_1134_, v_i_boxed_1135_, v_bs_1133_);
lean_dec(v_vertexCount_1130_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3_spec__4(lean_object* v_vertices_1137_, lean_object* v_G_1138_, lean_object* v_vertexCount_1139_, size_t v_sz_1140_, size_t v_i_1141_, lean_object* v_bs_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_usize_dec_lt(v_i_1141_, v_sz_1140_);
if (v___x_1143_ == 0)
{
lean_dec_ref(v_G_1138_);
lean_dec(v_vertices_1137_);
return v_bs_1142_;
}
else
{
lean_object* v_v_1144_; lean_object* v___x_1145_; lean_object* v_bs_x27_1146_; lean_object* v___x_1147_; size_t v_sz_1148_; size_t v___x_1149_; lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v_v_1144_ = lean_array_uget(v_bs_1142_, v_i_1141_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v_bs_x27_1146_ = lean_array_uset(v_bs_1142_, v_i_1141_, v___x_1145_);
lean_inc_n(v_vertices_1137_, 2);
v___x_1147_ = lean_array_mk(v_vertices_1137_);
v_sz_1148_ = lean_array_size(v___x_1147_);
v___x_1149_ = ((size_t)0ULL);
lean_inc_ref(v_G_1138_);
v___x_1150_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2(v_v_1144_, v_G_1138_, v_vertices_1137_, v_vertexCount_1139_, v_sz_1148_, v___x_1149_, v___x_1147_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1141_, v___x_1151_);
v___x_1153_ = lean_array_uset(v_bs_x27_1146_, v_i_1141_, v___x_1150_);
v_i_1141_ = v___x_1152_;
v_bs_1142_ = v___x_1153_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3_spec__4___boxed(lean_object* v_vertices_1155_, lean_object* v_G_1156_, lean_object* v_vertexCount_1157_, lean_object* v_sz_1158_, lean_object* v_i_1159_, lean_object* v_bs_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1158_);
lean_dec(v_sz_1158_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_res_1163_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3_spec__4(v_vertices_1155_, v_G_1156_, v_vertexCount_1157_, v_sz_boxed_1161_, v_i_boxed_1162_, v_bs_1160_);
lean_dec(v_vertexCount_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3(lean_object* v_G_1164_, lean_object* v_vertices_1165_, lean_object* v_vertexCount_1166_, size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_bs_1169_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1170_ == 0)
{
lean_dec(v_vertices_1165_);
lean_dec_ref(v_G_1164_);
return v_bs_1169_;
}
else
{
lean_object* v_v_1171_; lean_object* v___x_1172_; lean_object* v_bs_x27_1173_; lean_object* v___x_1174_; size_t v_sz_1175_; size_t v___x_1176_; lean_object* v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_v_1171_ = lean_array_uget(v_bs_1169_, v_i_1168_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v_bs_x27_1173_ = lean_array_uset(v_bs_1169_, v_i_1168_, v___x_1172_);
lean_inc_n(v_vertices_1165_, 2);
v___x_1174_ = lean_array_mk(v_vertices_1165_);
v_sz_1175_ = lean_array_size(v___x_1174_);
v___x_1176_ = ((size_t)0ULL);
lean_inc_ref(v_G_1164_);
v___x_1177_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__2(v_v_1171_, v_G_1164_, v_vertices_1165_, v_vertexCount_1166_, v_sz_1175_, v___x_1176_, v___x_1174_);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1168_, v___x_1178_);
v___x_1180_ = lean_array_uset(v_bs_x27_1173_, v_i_1168_, v___x_1177_);
v___x_1181_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3_spec__4(v_vertices_1165_, v_G_1164_, v_vertexCount_1166_, v_sz_1167_, v___x_1179_, v___x_1180_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3___boxed(lean_object* v_G_1182_, lean_object* v_vertices_1183_, lean_object* v_vertexCount_1184_, lean_object* v_sz_1185_, lean_object* v_i_1186_, lean_object* v_bs_1187_){
_start:
{
size_t v_sz_boxed_1188_; size_t v_i_boxed_1189_; lean_object* v_res_1190_; 
v_sz_boxed_1188_ = lean_unbox_usize(v_sz_1185_);
lean_dec(v_sz_1185_);
v_i_boxed_1189_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_res_1190_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3(v_G_1182_, v_vertices_1183_, v_vertexCount_1184_, v_sz_boxed_1188_, v_i_boxed_1189_, v_bs_1187_);
lean_dec(v_vertexCount_1184_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_initializePaths(lean_object* v_vertexCount_1191_, lean_object* v_G_1192_){
_start:
{
lean_object* v_vertices_1193_; lean_object* v___x_1194_; size_t v_sz_1195_; size_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_inc(v_vertexCount_1191_);
v_vertices_1193_ = l_List_finRange(v_vertexCount_1191_);
lean_inc(v_vertices_1193_);
v___x_1194_ = lean_array_mk(v_vertices_1193_);
v_sz_1195_ = lean_array_size(v___x_1194_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_initializePaths_spec__3(v_G_1192_, v_vertices_1193_, v_vertexCount_1191_, v_sz_1195_, v___x_1196_, v___x_1194_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_vertexCount_1191_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1(lean_object* v___x_1199_, lean_object* v_G_1200_, lean_object* v___x_1201_, lean_object* v_vertices_1202_, lean_object* v_vertexCount_1203_, lean_object* v_x_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___redArg(v___x_1199_, v_G_1200_, v___x_1201_, v_vertices_1202_, v_x_1204_, v_a_1205_, v_a_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1___boxed(lean_object* v___x_1208_, lean_object* v_G_1209_, lean_object* v___x_1210_, lean_object* v_vertices_1211_, lean_object* v_vertexCount_1212_, lean_object* v_x_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00List_mapTR_loop___at___00Graph_initializePaths_spec__1_spec__1(v___x_1208_, v_G_1209_, v___x_1210_, v_vertices_1211_, v_vertexCount_1212_, v_x_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_x_1213_);
lean_dec(v_vertexCount_1212_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_assignRanks_spec__0___redArg(lean_object* v_cmp_1217_, lean_object* v_x_1218_, lean_object* v_x_1219_){
_start:
{
if (lean_obj_tag(v_x_1219_) == 0)
{
lean_dec_ref(v_cmp_1217_);
return v_x_1218_;
}
else
{
lean_object* v_head_1220_; lean_object* v_tail_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1252_; 
v_head_1220_ = lean_ctor_get(v_x_1219_, 0);
v_tail_1221_ = lean_ctor_get(v_x_1219_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_x_1219_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1223_ = v_x_1219_;
v_isShared_1224_ = v_isSharedCheck_1252_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_tail_1221_);
lean_inc(v_head_1220_);
lean_dec(v_x_1219_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1252_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_fst_1225_; lean_object* v_snd_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1251_; 
v_fst_1225_ = lean_ctor_get(v_x_1218_, 0);
v_snd_1226_ = lean_ctor_get(v_x_1218_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1218_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1228_ = v_x_1218_;
v_isShared_1229_ = v_isSharedCheck_1251_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_snd_1226_);
lean_inc(v_fst_1225_);
lean_dec(v_x_1218_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1251_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___y_1231_; 
if (lean_obj_tag(v_snd_1226_) == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___y_1231_ = v___x_1241_;
goto v___jp_1230_;
}
else
{
lean_object* v_val_1242_; lean_object* v_fst_1243_; lean_object* v_snd_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; uint8_t v___x_1247_; uint8_t v___x_1248_; 
v_val_1242_ = lean_ctor_get(v_snd_1226_, 0);
lean_inc(v_val_1242_);
lean_dec_ref(v_snd_1226_);
v_fst_1243_ = lean_ctor_get(v_val_1242_, 0);
lean_inc(v_fst_1243_);
v_snd_1244_ = lean_ctor_get(v_val_1242_, 1);
lean_inc(v_snd_1244_);
lean_dec(v_val_1242_);
lean_inc_ref(v_cmp_1217_);
lean_inc(v_head_1220_);
v___x_1245_ = lean_apply_2(v_cmp_1217_, v_fst_1243_, v_head_1220_);
v___x_1246_ = 1;
v___x_1247_ = lean_unbox(v___x_1245_);
v___x_1248_ = l_instDecidableEqOrdering(v___x_1247_, v___x_1246_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_snd_1244_);
v___x_1249_ = l_List_lengthTR___redArg(v_fst_1225_);
v___x_1250_ = lean_nat_to_int(v___x_1249_);
v___y_1231_ = v___x_1250_;
goto v___jp_1230_;
}
else
{
v___y_1231_ = v_snd_1244_;
goto v___jp_1230_;
}
}
v___jp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___y_1231_);
lean_ctor_set(v___x_1228_, 0, v_head_1220_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_head_1220_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___y_1231_);
v___x_1233_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1235_; 
lean_inc_ref(v___x_1233_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v_fst_1225_);
lean_ctor_set(v___x_1223_, 0, v___x_1233_);
v___x_1235_ = v___x_1223_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_fst_1225_);
v___x_1235_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1233_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v_x_1218_ = v___x_1237_;
v_x_1219_ = v_tail_1221_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg(lean_object* v_cmp_1256_, lean_object* v_sorted_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v___x_1261_; 
v___x_1258_ = ((lean_object*)(lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg___closed__0));
v___x_1259_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_assignRanks_spec__0___redArg(v_cmp_1256_, v___x_1258_, v_sorted_1257_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_fst_1260_);
lean_dec_ref(v___x_1259_);
v___x_1261_ = l_List_reverse___redArg(v_fst_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks(lean_object* v_00_u03b1_1262_, lean_object* v_cmp_1263_, lean_object* v_sorted_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg(v_cmp_1263_, v_sorted_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_assignRanks_spec__0(lean_object* v_00_u03b1_1266_, lean_object* v_cmp_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_assignRanks_spec__0___redArg(v_cmp_1267_, v_x_1268_, v_x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_setBetween(lean_object* v_betweenTable_1271_, lean_object* v_depth_1272_, lean_object* v_startIdx_1273_, lean_object* v_endIdx_1274_, lean_object* v_rank_1275_){
_start:
{
lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1283_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_array_get_size(v_betweenTable_1271_);
v___x_1289_ = lean_nat_dec_lt(v_depth_1272_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1));
v___y_1283_ = v___x_1290_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_array_fget_borrowed(v_betweenTable_1271_, v_depth_1272_);
lean_inc(v___x_1291_);
v___y_1283_ = v___x_1291_;
goto v___jp_1282_;
}
v___jp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_array_set(v___y_1278_, v_endIdx_1274_, v_rank_1275_);
v___x_1280_ = lean_array_set(v___y_1277_, v_startIdx_1273_, v___x_1279_);
v___x_1281_ = lean_array_set(v_betweenTable_1271_, v_depth_1272_, v___x_1280_);
return v___x_1281_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v___y_1283_);
v___x_1285_ = lean_nat_dec_lt(v_startIdx_1273_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0));
v___y_1277_ = v___y_1283_;
v___y_1278_ = v___x_1286_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_array_fget(v___y_1283_, v_startIdx_1273_);
v___y_1277_ = v___y_1283_;
v___y_1278_ = v___x_1287_;
goto v___jp_1276_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_setBetween___boxed(lean_object* v_betweenTable_1292_, lean_object* v_depth_1293_, lean_object* v_startIdx_1294_, lean_object* v_endIdx_1295_, lean_object* v_rank_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_setBetween(v_betweenTable_1292_, v_depth_1293_, v_startIdx_1294_, v_endIdx_1295_, v_rank_1296_);
lean_dec(v_endIdx_1295_);
lean_dec(v_startIdx_1294_);
lean_dec(v_depth_1293_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3(size_t v_sz_1298_, size_t v_i_1299_, lean_object* v_bs_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
if (v___x_1301_ == 0)
{
return v_bs_1300_;
}
else
{
lean_object* v___x_1302_; lean_object* v_bs_x27_1303_; lean_object* v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v_bs_x27_1303_ = lean_array_uset(v_bs_1300_, v_i_1299_, v___x_1302_);
v___x_1304_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1299_, v___x_1305_);
v___x_1307_ = lean_array_uset(v_bs_x27_1303_, v_i_1299_, v___x_1304_);
v_i_1299_ = v___x_1306_;
v_bs_1300_ = v___x_1307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3___boxed(lean_object* v_sz_1309_, lean_object* v_i_1310_, lean_object* v_bs_1311_){
_start:
{
size_t v_sz_boxed_1312_; size_t v_i_boxed_1313_; lean_object* v_res_1314_; 
v_sz_boxed_1312_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1313_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1314_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3(v_sz_boxed_1312_, v_i_boxed_1313_, v_bs_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__4(lean_object* v_numVertices_1315_, size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_bs_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
lean_dec(v_numVertices_1315_);
return v_bs_1318_;
}
else
{
lean_object* v___x_1320_; lean_object* v_bs_x27_1321_; lean_object* v___x_1322_; size_t v_sz_1323_; size_t v___x_1324_; lean_object* v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v_bs_x27_1321_ = lean_array_uset(v_bs_1318_, v_i_1317_, v___x_1320_);
lean_inc(v_numVertices_1315_);
v___x_1322_ = l_Array_range(v_numVertices_1315_);
v_sz_1323_ = lean_array_size(v___x_1322_);
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3(v_sz_1323_, v___x_1324_, v___x_1322_);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_add(v_i_1317_, v___x_1326_);
v___x_1328_ = lean_array_uset(v_bs_x27_1321_, v_i_1317_, v___x_1325_);
v_i_1317_ = v___x_1327_;
v_bs_1318_ = v___x_1328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__4___boxed(lean_object* v_numVertices_1330_, lean_object* v_sz_1331_, lean_object* v_i_1332_, lean_object* v_bs_1333_){
_start:
{
size_t v_sz_boxed_1334_; size_t v_i_boxed_1335_; lean_object* v_res_1336_; 
v_sz_boxed_1334_ = lean_unbox_usize(v_sz_1331_);
lean_dec(v_sz_1331_);
v_i_boxed_1335_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_res_1336_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__4(v_numVertices_1330_, v_sz_boxed_1334_, v_i_boxed_1335_, v_bs_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__5(lean_object* v_numVertices_1337_, size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
lean_dec(v_numVertices_1337_);
return v_bs_1340_;
}
else
{
lean_object* v___x_1342_; lean_object* v_bs_x27_1343_; lean_object* v___x_1344_; size_t v_sz_1345_; size_t v___x_1346_; lean_object* v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1342_ = lean_unsigned_to_nat(0u);
v_bs_x27_1343_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1342_);
lean_inc_n(v_numVertices_1337_, 2);
v___x_1344_ = l_Array_range(v_numVertices_1337_);
v_sz_1345_ = lean_array_size(v___x_1344_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__4(v_numVertices_1337_, v_sz_1345_, v___x_1346_, v___x_1344_);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1339_, v___x_1348_);
v___x_1350_ = lean_array_uset(v_bs_x27_1343_, v_i_1339_, v___x_1347_);
v_i_1339_ = v___x_1349_;
v_bs_1340_ = v___x_1350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__5___boxed(lean_object* v_numVertices_1352_, lean_object* v_sz_1353_, lean_object* v_i_1354_, lean_object* v_bs_1355_){
_start:
{
size_t v_sz_boxed_1356_; size_t v_i_boxed_1357_; lean_object* v_res_1358_; 
v_sz_boxed_1356_ = lean_unbox_usize(v_sz_1353_);
lean_dec(v_sz_1353_);
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_res_1358_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__5(v_numVertices_1352_, v_sz_boxed_1356_, v_i_boxed_1357_, v_bs_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__2(lean_object* v_depth_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 0)
{
return v_x_1360_;
}
else
{
lean_object* v_head_1362_; lean_object* v_tail_1363_; lean_object* v_fst_1364_; lean_object* v_snd_1365_; lean_object* v___y_1367_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_head_1362_ = lean_ctor_get(v_x_1361_, 0);
lean_inc(v_head_1362_);
v_tail_1363_ = lean_ctor_get(v_x_1361_, 1);
lean_inc(v_tail_1363_);
lean_dec_ref(v_x_1361_);
v_fst_1364_ = lean_ctor_get(v_head_1362_, 0);
lean_inc(v_fst_1364_);
v_snd_1365_ = lean_ctor_get(v_head_1362_, 1);
lean_inc(v_snd_1365_);
lean_dec(v_head_1362_);
v___x_1372_ = lean_array_get_size(v_x_1360_);
v___x_1373_ = lean_nat_dec_lt(v_depth_1359_, v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0));
v___y_1367_ = v___x_1374_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_array_fget_borrowed(v_x_1360_, v_depth_1359_);
lean_inc(v___x_1375_);
v___y_1367_ = v___x_1375_;
goto v___jp_1366_;
}
v___jp_1366_:
{
lean_object* v_startVertexIndex_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_startVertexIndex_1368_ = lean_ctor_get(v_fst_1364_, 1);
lean_inc(v_startVertexIndex_1368_);
lean_dec(v_fst_1364_);
v___x_1369_ = lean_array_set(v___y_1367_, v_startVertexIndex_1368_, v_snd_1365_);
lean_dec(v_startVertexIndex_1368_);
v___x_1370_ = lean_array_set(v_x_1360_, v_depth_1359_, v___x_1369_);
v_x_1360_ = v___x_1370_;
v_x_1361_ = v_tail_1363_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__2___boxed(lean_object* v_depth_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__2(v_depth_1376_, v_x_1377_, v_x_1378_);
lean_dec(v_depth_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__1(lean_object* v_depth_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
return v_x_1381_;
}
else
{
lean_object* v_head_1383_; lean_object* v_fst_1384_; lean_object* v_tail_1385_; lean_object* v_snd_1386_; lean_object* v_startVertexIndex_1387_; lean_object* v_endVertexIndex_1388_; lean_object* v___x_1389_; 
v_head_1383_ = lean_ctor_get(v_x_1382_, 0);
lean_inc(v_head_1383_);
v_fst_1384_ = lean_ctor_get(v_head_1383_, 0);
lean_inc(v_fst_1384_);
v_tail_1385_ = lean_ctor_get(v_x_1382_, 1);
lean_inc(v_tail_1385_);
lean_dec_ref(v_x_1382_);
v_snd_1386_ = lean_ctor_get(v_head_1383_, 1);
lean_inc(v_snd_1386_);
lean_dec(v_head_1383_);
v_startVertexIndex_1387_ = lean_ctor_get(v_fst_1384_, 1);
lean_inc(v_startVertexIndex_1387_);
v_endVertexIndex_1388_ = lean_ctor_get(v_fst_1384_, 2);
lean_inc(v_endVertexIndex_1388_);
lean_dec(v_fst_1384_);
v___x_1389_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_setBetween(v_x_1381_, v_depth_1380_, v_startVertexIndex_1387_, v_endVertexIndex_1388_, v_snd_1386_);
lean_dec(v_endVertexIndex_1388_);
lean_dec(v_startVertexIndex_1387_);
v_x_1381_ = v___x_1389_;
v_x_1382_ = v_tail_1385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__1___boxed(lean_object* v_depth_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__1(v_depth_1391_, v_x_1392_, v_x_1393_);
lean_dec(v_depth_1391_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__0(lean_object* v_fst_1395_, lean_object* v_rankDepth_1396_, lean_object* v_rankStart_1397_, lean_object* v_rankEnd_1398_){
_start:
{
lean_object* v___y_1400_; lean_object* v___y_1406_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1411_ = lean_array_get_size(v_fst_1395_);
v___x_1412_ = lean_nat_dec_lt(v_rankDepth_1396_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1));
v___y_1406_ = v___x_1413_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_array_fget_borrowed(v_fst_1395_, v_rankDepth_1396_);
v___y_1406_ = v___x_1414_;
goto v___jp_1405_;
}
v___jp_1399_:
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = lean_array_get_size(v___y_1400_);
v___x_1402_ = lean_nat_dec_lt(v_rankEnd_1398_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_array_fget_borrowed(v___y_1400_, v_rankEnd_1398_);
lean_inc(v___x_1404_);
return v___x_1404_;
}
}
v___jp_1405_:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = lean_array_get_size(v___y_1406_);
v___x_1408_ = lean_nat_dec_lt(v_rankStart_1397_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
v___x_1409_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0));
v___y_1400_ = v___x_1409_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_array_fget_borrowed(v___y_1406_, v_rankStart_1397_);
v___y_1400_ = v___x_1410_;
goto v___jp_1399_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__0___boxed(lean_object* v_fst_1415_, lean_object* v_rankDepth_1416_, lean_object* v_rankStart_1417_, lean_object* v_rankEnd_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__0(v_fst_1415_, v_rankDepth_1416_, v_rankStart_1417_, v_rankEnd_1418_);
lean_dec(v_rankEnd_1418_);
lean_dec(v_rankStart_1417_);
lean_dec(v_rankDepth_1416_);
lean_dec_ref(v_fst_1415_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__1(lean_object* v_updatedBetween_1420_, lean_object* v_rankDepth_1421_, lean_object* v_rankStart_1422_, lean_object* v_rankEnd_1423_){
_start:
{
lean_object* v___y_1425_; lean_object* v___y_1431_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_array_get_size(v_updatedBetween_1420_);
v___x_1437_ = lean_nat_dec_lt(v_rankDepth_1421_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__1));
v___y_1431_ = v___x_1438_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_array_fget_borrowed(v_updatedBetween_1420_, v_rankDepth_1421_);
v___y_1431_ = v___x_1439_;
goto v___jp_1430_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = lean_array_get_size(v___y_1425_);
v___x_1427_ = lean_nat_dec_lt(v_rankEnd_1423_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_array_fget_borrowed(v___y_1425_, v_rankEnd_1423_);
lean_inc(v___x_1429_);
return v___x_1429_;
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = lean_array_get_size(v___y_1431_);
v___x_1433_ = lean_nat_dec_lt(v_rankStart_1422_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_RankState_getBetween___closed__0));
v___y_1425_ = v___x_1434_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_array_fget_borrowed(v___y_1431_, v_rankStart_1422_);
v___y_1425_ = v___x_1435_;
goto v___jp_1424_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__1___boxed(lean_object* v_updatedBetween_1440_, lean_object* v_rankDepth_1441_, lean_object* v_rankStart_1442_, lean_object* v_rankEnd_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__1(v_updatedBetween_1440_, v_rankDepth_1441_, v_rankStart_1442_, v_rankEnd_1443_);
lean_dec(v_rankEnd_1443_);
lean_dec(v_rankStart_1442_);
lean_dec(v_rankDepth_1441_);
lean_dec_ref(v_updatedBetween_1440_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__0(lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
return v_x_1445_;
}
else
{
lean_object* v_head_1447_; lean_object* v_tail_1448_; lean_object* v_pathsToVertex_1449_; lean_object* v___x_1450_; 
v_head_1447_ = lean_ctor_get(v_x_1446_, 0);
lean_inc(v_head_1447_);
v_tail_1448_ = lean_ctor_get(v_x_1446_, 1);
lean_inc(v_tail_1448_);
lean_dec_ref(v_x_1446_);
v_pathsToVertex_1449_ = lean_ctor_get(v_head_1447_, 2);
lean_inc(v_pathsToVertex_1449_);
lean_dec(v_head_1447_);
v___x_1450_ = l_List_appendTR___redArg(v_x_1445_, v_pathsToVertex_1449_);
v_x_1445_ = v___x_1450_;
v_x_1446_ = v_tail_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7(lean_object* v_vertexTypes_1454_, lean_object* v_state_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
if (lean_obj_tag(v_x_1457_) == 0)
{
lean_dec_ref(v_vertexTypes_1454_);
return v_x_1456_;
}
else
{
lean_object* v_head_1458_; lean_object* v_tail_1459_; lean_object* v_fst_1460_; lean_object* v_snd_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1489_; 
v_head_1458_ = lean_ctor_get(v_x_1457_, 0);
v_tail_1459_ = lean_ctor_get(v_x_1457_, 1);
v_fst_1460_ = lean_ctor_get(v_x_1456_, 0);
v_snd_1461_ = lean_ctor_get(v_x_1456_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1456_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1463_ = v_x_1456_;
v_isShared_1464_ = v_isSharedCheck_1489_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snd_1461_);
lean_inc(v_fst_1460_);
lean_dec(v_x_1456_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1489_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_pathsOfLength_1465_; lean_object* v_betweenRankFn_1466_; lean_object* v___y_1468_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_pathsOfLength_1465_ = lean_ctor_get(v_state_1455_, 1);
lean_inc(v_fst_1460_);
v_betweenRankFn_1466_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__0___boxed), 4, 1);
lean_closure_set(v_betweenRankFn_1466_, 0, v_fst_1460_);
v___x_1485_ = lean_array_get_size(v_pathsOfLength_1465_);
v___x_1486_ = lean_nat_dec_lt(v_head_1458_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = ((lean_object*)(lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___closed__0));
v___y_1468_ = v___x_1487_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_array_fget_borrowed(v_pathsOfLength_1465_, v_head_1458_);
lean_inc(v___x_1488_);
v___y_1468_ = v___x_1488_;
goto v___jp_1467_;
}
v___jp_1467_:
{
lean_object* v_pathsAtDepth_1469_; lean_object* v___x_1470_; lean_object* v_allBetween_1471_; lean_object* v_compareBetween_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_updatedBetween_1475_; lean_object* v_updatedBetweenFn_1476_; lean_object* v_compareFrom_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_updatedFrom_1480_; lean_object* v___x_1482_; 
v_pathsAtDepth_1469_ = lean_array_to_list(v___y_1468_);
v___x_1470_ = lean_box(0);
lean_inc(v_pathsAtDepth_1469_);
v_allBetween_1471_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__0(v___x_1470_, v_pathsAtDepth_1469_);
lean_inc_ref_n(v_vertexTypes_1454_, 2);
v_compareBetween_1472_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_comparePathsBetween___boxed), 4, 2);
lean_closure_set(v_compareBetween_1472_, 0, v_vertexTypes_1454_);
lean_closure_set(v_compareBetween_1472_, 1, v_betweenRankFn_1466_);
lean_inc_ref(v_compareBetween_1472_);
v___x_1473_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_compareBetween_1472_, v_allBetween_1471_);
v___x_1474_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg(v_compareBetween_1472_, v___x_1473_);
v_updatedBetween_1475_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__1(v_head_1458_, v_fst_1460_, v___x_1474_);
lean_inc_ref(v_updatedBetween_1475_);
v_updatedBetweenFn_1476_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___lam__1___boxed), 4, 1);
lean_closure_set(v_updatedBetweenFn_1476_, 0, v_updatedBetween_1475_);
v_compareFrom_1477_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_comparePathsFrom___boxed), 4, 2);
lean_closure_set(v_compareFrom_1477_, 0, v_vertexTypes_1454_);
lean_closure_set(v_compareFrom_1477_, 1, v_updatedBetweenFn_1476_);
lean_inc_ref(v_compareFrom_1477_);
v___x_1478_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_compareFrom_1477_, v_pathsAtDepth_1469_);
v___x_1479_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_assignRanks___redArg(v_compareFrom_1477_, v___x_1478_);
v_updatedFrom_1480_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__2(v_head_1458_, v_snd_1461_, v___x_1479_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 1, v_updatedFrom_1480_);
lean_ctor_set(v___x_1463_, 0, v_updatedBetween_1475_);
v___x_1482_ = v___x_1463_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_updatedBetween_1475_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_updatedFrom_1480_);
v___x_1482_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
v_x_1456_ = v___x_1482_;
v_x_1457_ = v_tail_1459_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7___boxed(lean_object* v_vertexTypes_1490_, lean_object* v_state_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7(v_vertexTypes_1490_, v_state_1491_, v_x_1492_, v_x_1493_);
lean_dec(v_x_1493_);
lean_dec_ref(v_state_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__6(lean_object* v___x_1495_, size_t v_sz_1496_, size_t v_i_1497_, lean_object* v_bs_1498_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1497_, v_sz_1496_);
if (v___x_1499_ == 0)
{
lean_dec_ref(v___x_1495_);
return v_bs_1498_;
}
else
{
lean_object* v___x_1500_; lean_object* v_bs_x27_1501_; size_t v_sz_1502_; size_t v___x_1503_; lean_object* v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v_bs_x27_1501_ = lean_array_uset(v_bs_1498_, v_i_1497_, v___x_1500_);
v_sz_1502_ = lean_array_size(v___x_1495_);
v___x_1503_ = ((size_t)0ULL);
lean_inc_ref(v___x_1495_);
v___x_1504_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__3(v_sz_1502_, v___x_1503_, v___x_1495_);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1497_, v___x_1505_);
v___x_1507_ = lean_array_uset(v_bs_x27_1501_, v_i_1497_, v___x_1504_);
v_i_1497_ = v___x_1506_;
v_bs_1498_ = v___x_1507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__6___boxed(lean_object* v___x_1509_, lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_bs_1512_){
_start:
{
size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1515_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__6(v___x_1509_, v_sz_boxed_1513_, v_i_boxed_1514_, v_bs_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_calculatePathRankings(lean_object* v_state_1516_, lean_object* v_vertexTypes_1517_){
_start:
{
lean_object* v_vertexCount_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v_emptyBetweenTable_1522_; lean_object* v_emptyFromTable_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_vertexCount_1518_ = lean_ctor_get(v_state_1516_, 0);
lean_inc_n(v_vertexCount_1518_, 3);
v___x_1519_ = l_Array_range(v_vertexCount_1518_);
v_sz_1520_ = lean_array_size(v___x_1519_);
v___x_1521_ = ((size_t)0ULL);
lean_inc_ref_n(v___x_1519_, 2);
v_emptyBetweenTable_1522_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__5(v_vertexCount_1518_, v_sz_1520_, v___x_1521_, v___x_1519_);
v_emptyFromTable_1523_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_calculatePathRankings_spec__6(v___x_1519_, v_sz_1520_, v___x_1521_, v___x_1519_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_emptyBetweenTable_1522_);
lean_ctor_set(v___x_1524_, 1, v_emptyFromTable_1523_);
v___x_1525_ = l_List_range(v_vertexCount_1518_);
v___x_1526_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_calculatePathRankings_spec__7(v_vertexTypes_1517_, v_state_1516_, v___x_1524_, v___x_1525_);
lean_dec(v___x_1525_);
lean_dec_ref(v_state_1516_);
v_fst_1527_ = lean_ctor_get(v___x_1526_, 0);
v_snd_1528_ = lean_ctor_get(v___x_1526_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_inc(v_fst_1527_);
lean_dec(v___x_1526_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_fst_1527_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_snd_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_convergeOnce_spec__0(lean_object* v_numVertices_1536_, lean_object* v_rankState_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
return v_x_1538_;
}
else
{
lean_object* v_head_1540_; lean_object* v_tail_1541_; lean_object* v_fst_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_newRank_1545_; lean_object* v___y_1547_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_head_1540_ = lean_ctor_get(v_x_1539_, 0);
v_tail_1541_ = lean_ctor_get(v_x_1539_, 1);
v_fst_1542_ = lean_ctor_get(v_x_1538_, 0);
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_sub(v_numVertices_1536_, v___x_1543_);
v_newRank_1545_ = lp_GraphCanonizationProofs_Graph_RankState_getFrom(v_rankState_1537_, v___x_1544_, v_head_1540_);
lean_dec(v___x_1544_);
v___x_1563_ = lean_array_get_size(v_fst_1542_);
v___x_1564_ = lean_nat_dec_lt(v_head_1540_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___y_1547_ = v___x_1565_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_array_fget_borrowed(v_fst_1542_, v_head_1540_);
lean_inc(v___x_1566_);
v___y_1547_ = v___x_1566_;
goto v___jp_1546_;
}
v___jp_1546_:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_int_dec_eq(v_newRank_1545_, v___y_1547_);
lean_dec(v___y_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1559_; 
lean_inc(v_fst_1542_);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; 
v_unused_1560_ = lean_ctor_get(v_x_1538_, 1);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_x_1538_, 0);
lean_dec(v_unused_1561_);
v___x_1550_ = v_x_1538_;
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_x_1538_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1552_ = 1;
v___x_1553_ = lean_array_set(v_fst_1542_, v_head_1540_, v_newRank_1545_);
v___x_1554_ = lean_box(v___x_1552_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___x_1554_);
lean_ctor_set(v___x_1550_, 0, v___x_1553_);
v___x_1556_ = v___x_1550_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
v_x_1538_ = v___x_1556_;
v_x_1539_ = v_tail_1541_;
goto _start;
}
}
}
else
{
lean_dec(v_newRank_1545_);
v_x_1539_ = v_tail_1541_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_convergeOnce_spec__0___boxed(lean_object* v_numVertices_1567_, lean_object* v_rankState_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_convergeOnce_spec__0(v_numVertices_1567_, v_rankState_1568_, v_x_1569_, v_x_1570_);
lean_dec(v_x_1570_);
lean_dec_ref(v_rankState_1568_);
lean_dec(v_numVertices_1567_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_convergeOnce(lean_object* v_state_1572_, lean_object* v_vertexTypes_1573_){
_start:
{
lean_object* v_vertexCount_1574_; lean_object* v_rankState_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_vertexCount_1574_ = lean_ctor_get(v_state_1572_, 0);
lean_inc_n(v_vertexCount_1574_, 2);
lean_inc_ref(v_vertexTypes_1573_);
v_rankState_1575_ = lp_GraphCanonizationProofs_Graph_calculatePathRankings(v_state_1572_, v_vertexTypes_1573_);
v___x_1576_ = 0;
v___x_1577_ = lean_box(v___x_1576_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_vertexTypes_1573_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_List_range(v_vertexCount_1574_);
v___x_1580_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_convergeOnce_spec__0(v_vertexCount_1574_, v_rankState_1575_, v___x_1578_, v___x_1579_);
lean_dec(v___x_1579_);
lean_dec_ref(v_rankState_1575_);
lean_dec(v_vertexCount_1574_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_convergeLoop(lean_object* v_state_1581_, lean_object* v_vertexTypes_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v_zero_1584_; uint8_t v_isZero_1585_; 
v_zero_1584_ = lean_unsigned_to_nat(0u);
v_isZero_1585_ = lean_nat_dec_eq(v_x_1583_, v_zero_1584_);
if (v_isZero_1585_ == 1)
{
lean_dec(v_x_1583_);
lean_dec_ref(v_state_1581_);
return v_vertexTypes_1582_;
}
else
{
lean_object* v___x_1586_; lean_object* v_snd_1587_; uint8_t v___x_1588_; 
lean_inc_ref(v_state_1581_);
v___x_1586_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_convergeOnce(v_state_1581_, v_vertexTypes_1582_);
v_snd_1587_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_snd_1587_);
v___x_1588_ = lean_unbox(v_snd_1587_);
lean_dec(v_snd_1587_);
if (v___x_1588_ == 0)
{
lean_object* v_fst_1589_; 
lean_dec(v_x_1583_);
lean_dec_ref(v_state_1581_);
v_fst_1589_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_fst_1589_);
lean_dec_ref(v___x_1586_);
return v_fst_1589_;
}
else
{
lean_object* v_fst_1590_; lean_object* v_one_1591_; lean_object* v_n_1592_; 
v_fst_1590_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_fst_1590_);
lean_dec_ref(v___x_1586_);
v_one_1591_ = lean_unsigned_to_nat(1u);
v_n_1592_ = lean_nat_sub(v_x_1583_, v_one_1591_);
lean_dec(v_x_1583_);
v_vertexTypes_1582_ = v_fst_1590_;
v_x_1583_ = v_n_1592_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_breakTie_spec__0(lean_object* v_target_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
return v_x_1595_;
}
else
{
lean_object* v_snd_1597_; lean_object* v_head_1598_; lean_object* v_tail_1599_; lean_object* v_fst_1600_; lean_object* v_fst_1601_; lean_object* v_snd_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1641_; 
v_snd_1597_ = lean_ctor_get(v_x_1595_, 1);
lean_inc(v_snd_1597_);
v_head_1598_ = lean_ctor_get(v_x_1596_, 0);
v_tail_1599_ = lean_ctor_get(v_x_1596_, 1);
v_fst_1600_ = lean_ctor_get(v_x_1595_, 0);
v_fst_1601_ = lean_ctor_get(v_snd_1597_, 0);
v_snd_1602_ = lean_ctor_get(v_snd_1597_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_snd_1597_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1604_ = v_snd_1597_;
v_isShared_1605_ = v_isSharedCheck_1641_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snd_1602_);
lean_inc(v_fst_1601_);
lean_dec(v_snd_1597_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1641_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___y_1607_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_array_get_size(v_fst_1600_);
v___x_1638_ = lean_nat_dec_lt(v_head_1598_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___y_1607_ = v___x_1639_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_array_fget_borrowed(v_fst_1600_, v_head_1598_);
lean_inc(v___x_1640_);
v___y_1607_ = v___x_1640_;
goto v___jp_1606_;
}
v___jp_1606_:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_int_dec_eq(v___y_1607_, v_target_1594_);
lean_dec(v___y_1607_);
if (v___x_1608_ == 0)
{
lean_del_object(v___x_1604_);
lean_dec(v_snd_1602_);
lean_dec(v_fst_1601_);
v_x_1596_ = v_tail_1599_;
goto _start;
}
else
{
lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1634_; 
lean_inc(v_fst_1600_);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_x_1595_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1635_ = lean_ctor_get(v_x_1595_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_x_1595_, 0);
lean_dec(v_unused_1636_);
v___x_1611_ = v_x_1595_;
v_isShared_1612_ = v_isSharedCheck_1634_;
goto v_resetjp_1610_;
}
else
{
lean_dec(v_x_1595_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1634_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_unbox(v_fst_1601_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec(v_snd_1602_);
v___x_1614_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4);
v___x_1615_ = lean_int_add(v_target_1594_, v___x_1614_);
v___x_1616_ = lean_array_set(v_fst_1600_, v_head_1598_, v___x_1615_);
v___x_1617_ = lean_box(v___x_1608_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 1, v___x_1617_);
v___x_1619_ = v___x_1604_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_fst_1601_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v___x_1619_);
lean_ctor_set(v___x_1611_, 0, v___x_1616_);
v___x_1621_ = v___x_1611_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
v_x_1595_ = v___x_1621_;
v_x_1596_ = v_tail_1599_;
goto _start;
}
}
}
else
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec(v_fst_1601_);
v___x_1625_ = 0;
v___x_1626_ = lean_box(v___x_1625_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1626_);
v___x_1628_ = v___x_1604_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_snd_1602_);
v___x_1628_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1630_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 1, v___x_1628_);
v___x_1630_ = v___x_1611_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_fst_1600_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v_x_1595_ = v___x_1630_;
v_x_1596_ = v_tail_1599_;
goto _start;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_breakTie_spec__0___boxed(lean_object* v_target_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_breakTie_spec__0(v_target_1642_, v_x_1643_, v_x_1644_);
lean_dec(v_x_1644_);
lean_dec(v_target_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie(lean_object* v_vertexTypes_1651_, lean_object* v_target_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_result_1657_; lean_object* v_snd_1658_; lean_object* v_fst_1659_; lean_object* v_snd_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v___x_1653_ = ((lean_object*)(lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie___closed__0));
lean_inc_ref(v_vertexTypes_1651_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_vertexTypes_1651_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_array_get_size(v_vertexTypes_1651_);
lean_dec_ref(v_vertexTypes_1651_);
v___x_1656_ = l_List_range(v___x_1655_);
v_result_1657_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_breakTie_spec__0(v_target_1652_, v___x_1654_, v___x_1656_);
lean_dec(v___x_1656_);
v_snd_1658_ = lean_ctor_get(v_result_1657_, 1);
lean_inc(v_snd_1658_);
v_fst_1659_ = lean_ctor_get(v_result_1657_, 0);
lean_inc(v_fst_1659_);
lean_dec_ref(v_result_1657_);
v_snd_1660_ = lean_ctor_get(v_snd_1658_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_snd_1658_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v_snd_1658_, 0);
lean_dec(v_unused_1668_);
v___x_1662_ = v_snd_1658_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_snd_1660_);
lean_dec(v_snd_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v_fst_1659_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_fst_1659_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_snd_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie___boxed(lean_object* v_vertexTypes_1669_, lean_object* v_target_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie(v_vertexTypes_1669_, v_target_1670_);
lean_dec(v_target_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderVertices_spec__0(lean_object* v_state_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
if (lean_obj_tag(v_x_1674_) == 0)
{
lean_dec_ref(v_state_1672_);
return v_x_1673_;
}
else
{
lean_object* v_head_1675_; lean_object* v_tail_1676_; lean_object* v_vertexCount_1677_; lean_object* v_convergedTypes_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_fst_1681_; 
v_head_1675_ = lean_ctor_get(v_x_1674_, 0);
lean_inc(v_head_1675_);
v_tail_1676_ = lean_ctor_get(v_x_1674_, 1);
lean_inc(v_tail_1676_);
lean_dec_ref(v_x_1674_);
v_vertexCount_1677_ = lean_ctor_get(v_state_1672_, 0);
lean_inc(v_vertexCount_1677_);
lean_inc_ref(v_state_1672_);
v_convergedTypes_1678_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_convergeLoop(v_state_1672_, v_x_1673_, v_vertexCount_1677_);
v___x_1679_ = lean_nat_to_int(v_head_1675_);
v___x_1680_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_breakTie(v_convergedTypes_1678_, v___x_1679_);
lean_dec(v___x_1679_);
v_fst_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_fst_1681_);
lean_dec_ref(v___x_1680_);
v_x_1673_ = v_fst_1681_;
v_x_1674_ = v_tail_1676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderVertices(lean_object* v_state_1683_, lean_object* v_vertexTypes_1684_){
_start:
{
lean_object* v_vertexCount_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_vertexCount_1685_ = lean_ctor_get(v_state_1683_, 0);
lean_inc(v_vertexCount_1685_);
v___x_1686_ = l_List_range(v_vertexCount_1685_);
v___x_1687_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderVertices_spec__0(v_state_1683_, v_vertexTypes_1684_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___lam__0(lean_object* v_pair1_1688_, lean_object* v_pair2_1689_){
_start:
{
lean_object* v_fst_1690_; lean_object* v_snd_1691_; lean_object* v_fst_1692_; lean_object* v_snd_1693_; uint8_t v___x_1694_; 
v_fst_1690_ = lean_ctor_get(v_pair1_1688_, 0);
v_snd_1691_ = lean_ctor_get(v_pair1_1688_, 1);
v_fst_1692_ = lean_ctor_get(v_pair2_1689_, 0);
v_snd_1693_ = lean_ctor_get(v_pair2_1689_, 1);
v___x_1694_ = lean_int_dec_eq(v_fst_1690_, v_fst_1692_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_int_dec_lt(v_fst_1690_, v_fst_1692_);
if (v___x_1695_ == 0)
{
if (v___x_1694_ == 0)
{
uint8_t v___x_1696_; 
v___x_1696_ = 2;
return v___x_1696_;
}
else
{
uint8_t v___x_1697_; 
v___x_1697_ = 1;
return v___x_1697_;
}
}
else
{
uint8_t v___x_1698_; 
v___x_1698_ = 0;
return v___x_1698_;
}
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_nat_dec_lt(v_snd_1691_, v_snd_1693_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_eq(v_snd_1691_, v_snd_1693_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; 
v___x_1701_ = 2;
return v___x_1701_;
}
else
{
uint8_t v___x_1702_; 
v___x_1702_ = 1;
return v___x_1702_;
}
}
else
{
uint8_t v___x_1703_; 
v___x_1703_ = 0;
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___lam__0___boxed(lean_object* v_pair1_1704_, lean_object* v_pair2_1705_){
_start:
{
uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_res_1706_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___lam__0(v_pair1_1704_, v_pair2_1705_);
lean_dec_ref(v_pair2_1705_);
lean_dec_ref(v_pair1_1704_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___x_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2(lean_object* v_sorted_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
return v_x_1712_;
}
else
{
lean_object* v_head_1714_; lean_object* v_tail_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_snd_1718_; lean_object* v___x_1719_; 
v_head_1714_ = lean_ctor_get(v_x_1713_, 0);
lean_inc_n(v_head_1714_, 2);
v_tail_1715_ = lean_ctor_get(v_x_1713_, 1);
lean_inc(v_tail_1715_);
lean_dec_ref(v_x_1713_);
v___x_1716_ = lean_obj_once(&lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___closed__0, &lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___closed__0_once, _init_lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___closed__0);
v___x_1717_ = l_List_getD___redArg(v_sorted_1711_, v_head_1714_, v___x_1716_);
v_snd_1718_ = lean_ctor_get(v___x_1717_, 1);
lean_inc(v_snd_1718_);
lean_dec(v___x_1717_);
v___x_1719_ = lean_array_set(v_x_1712_, v_snd_1718_, v_head_1714_);
lean_dec(v_snd_1718_);
v_x_1712_ = v___x_1719_;
v_x_1713_ = v_tail_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2___boxed(lean_object* v_sorted_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2(v_sorted_1721_, v_x_1722_, v_x_1723_);
lean_dec(v_sorted_1721_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__0(lean_object* v_vertexRankings_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
if (lean_obj_tag(v_a_1726_) == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = l_List_reverse___redArg(v_a_1727_);
return v___x_1728_;
}
else
{
lean_object* v_head_1729_; lean_object* v_tail_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1746_; 
v_head_1729_ = lean_ctor_get(v_a_1726_, 0);
v_tail_1730_ = lean_ctor_get(v_a_1726_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_a_1726_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1732_ = v_a_1726_;
v_isShared_1733_ = v_isSharedCheck_1746_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_tail_1730_);
lean_inc(v_head_1729_);
lean_dec(v_a_1726_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1746_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___y_1735_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = lean_array_get_size(v_vertexRankings_1725_);
v___x_1741_ = lean_nat_dec_lt(v_head_1729_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v_head_1729_);
v___y_1735_ = v___x_1743_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_array_fget_borrowed(v_vertexRankings_1725_, v_head_1729_);
lean_inc(v___x_1744_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_head_1729_);
v___y_1735_ = v___x_1745_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v_a_1727_);
lean_ctor_set(v___x_1732_, 0, v___y_1735_);
v___x_1737_ = v___x_1732_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___y_1735_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1727_);
v___x_1737_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
v_a_1726_ = v_tail_1730_;
v_a_1727_ = v___x_1737_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__0___boxed(lean_object* v_vertexRankings_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__0(v_vertexRankings_1747_, v_a_1748_, v_a_1749_);
lean_dec_ref(v_vertexRankings_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__1(size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_bs_1753_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_lt(v_i_1752_, v_sz_1751_);
if (v___x_1754_ == 0)
{
return v_bs_1753_;
}
else
{
lean_object* v___x_1755_; lean_object* v_bs_x27_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v_bs_x27_1756_ = lean_array_uset(v_bs_1753_, v_i_1752_, v___x_1755_);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1752_, v___x_1757_);
v___x_1759_ = lean_array_uset(v_bs_x27_1756_, v_i_1752_, v___x_1755_);
v_i_1752_ = v___x_1758_;
v_bs_1753_ = v___x_1759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__1___boxed(lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_bs_1763_){
_start:
{
size_t v_sz_boxed_1764_; size_t v_i_boxed_1765_; lean_object* v_res_1766_; 
v_sz_boxed_1764_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1766_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__1(v_sz_boxed_1764_, v_i_boxed_1765_, v_bs_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks(lean_object* v_numVertices_1768_, lean_object* v_vertexRankings_1769_){
_start:
{
lean_object* v_cmp_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_pairs_1773_; lean_object* v_sorted_1774_; lean_object* v___x_1775_; size_t v_sz_1776_; size_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_cmp_1770_ = ((lean_object*)(lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___closed__0));
lean_inc(v_numVertices_1768_);
v___x_1771_ = l_List_range(v_numVertices_1768_);
v___x_1772_ = lean_box(0);
v_pairs_1773_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__0(v_vertexRankings_1769_, v___x_1771_, v___x_1772_);
v_sorted_1774_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_1770_, v_pairs_1773_);
v___x_1775_ = l_Array_range(v_numVertices_1768_);
v_sz_1776_ = lean_array_size(v___x_1775_);
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__1(v_sz_1776_, v___x_1777_, v___x_1775_);
v___x_1779_ = l_List_lengthTR___redArg(v_sorted_1774_);
v___x_1780_ = l_List_range(v___x_1779_);
v___x_1781_ = lp_GraphCanonizationProofs_List_foldl___at___00__private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks_spec__2(v_sorted_1774_, v___x_1778_, v___x_1780_);
lean_dec(v_sorted_1774_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks___boxed(lean_object* v_numVertices_1782_, lean_object* v_vertexRankings_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks(v_numVertices_1782_, v_vertexRankings_1783_);
lean_dec_ref(v_vertexRankings_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg___lam__0(lean_object* v_snd_1785_, lean_object* v_head_1786_, lean_object* v_searchFin_1787_){
_start:
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_array_get_size(v_snd_1785_);
v___x_1789_ = lean_nat_dec_lt(v_searchFin_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_eq(v___x_1790_, v_head_1786_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_array_fget_borrowed(v_snd_1785_, v_searchFin_1787_);
v___x_1793_ = lean_nat_dec_eq(v___x_1792_, v_head_1786_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1794_, lean_object* v_head_1795_, lean_object* v_searchFin_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg___lam__0(v_snd_1794_, v_head_1795_, v_searchFin_1796_);
lean_dec(v_searchFin_1796_);
lean_dec(v_head_1795_);
lean_dec_ref(v_snd_1794_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg(lean_object* v_vertices_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
if (lean_obj_tag(v_x_1801_) == 0)
{
lean_dec(v_vertices_1799_);
return v_x_1800_;
}
else
{
lean_object* v_head_1802_; lean_object* v_tail_1803_; lean_object* v_fst_1804_; lean_object* v_snd_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; 
v_head_1802_ = lean_ctor_get(v_x_1801_, 0);
lean_inc_n(v_head_1802_, 2);
v_tail_1803_ = lean_ctor_get(v_x_1801_, 1);
lean_inc(v_tail_1803_);
lean_dec_ref(v_x_1801_);
v_fst_1804_ = lean_ctor_get(v_x_1800_, 0);
v_snd_1805_ = lean_ctor_get(v_x_1800_, 1);
lean_inc(v_snd_1805_);
v___f_1806_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1806_, 0, v_snd_1805_);
lean_closure_set(v___f_1806_, 1, v_head_1802_);
lean_inc(v_vertices_1799_);
v___x_1807_ = l_List_find_x3f___redArg(v___f_1806_, v_vertices_1799_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_dec(v_head_1802_);
v_x_1801_ = v_tail_1803_;
goto _start;
}
else
{
lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1832_; 
lean_inc(v_snd_1805_);
lean_inc(v_fst_1804_);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_x_1800_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; lean_object* v_unused_1834_; 
v_unused_1833_ = lean_ctor_get(v_x_1800_, 1);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_x_1800_, 0);
lean_dec(v_unused_1834_);
v___x_1810_ = v_x_1800_;
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
else
{
lean_dec(v_x_1800_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1832_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_val_1812_; lean_object* v_swappedGraph_1813_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___x_1823_; lean_object* v___y_1825_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_val_1812_ = lean_ctor_get(v___x_1807_, 0);
lean_inc_n(v_val_1812_, 2);
lean_dec_ref(v___x_1807_);
lean_inc(v_head_1802_);
v_swappedGraph_1813_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v_swappedGraph_1813_, 0, v_head_1802_);
lean_closure_set(v_swappedGraph_1813_, 1, v_val_1812_);
lean_closure_set(v_swappedGraph_1813_, 2, v_fst_1804_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_array_get_size(v_snd_1805_);
v___x_1830_ = lean_nat_dec_lt(v_val_1812_, v___x_1829_);
if (v___x_1830_ == 0)
{
v___y_1825_ = v___x_1823_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_array_fget_borrowed(v_snd_1805_, v_val_1812_);
lean_inc(v___x_1831_);
v___y_1825_ = v___x_1831_;
goto v___jp_1824_;
}
v___jp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1817_ = lean_array_set(v_snd_1805_, v_val_1812_, v___y_1816_);
lean_dec(v_val_1812_);
v___x_1818_ = lean_array_set(v___x_1817_, v_head_1802_, v___y_1815_);
lean_dec(v_head_1802_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1818_);
lean_ctor_set(v___x_1810_, 0, v_swappedGraph_1813_);
v___x_1820_ = v___x_1810_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_swappedGraph_1813_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
v_x_1800_ = v___x_1820_;
v_x_1801_ = v_tail_1803_;
goto _start;
}
}
v___jp_1824_:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v_snd_1805_);
v___x_1827_ = lean_nat_dec_lt(v_head_1802_, v___x_1826_);
if (v___x_1827_ == 0)
{
v___y_1815_ = v___y_1825_;
v___y_1816_ = v___x_1823_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_array_fget_borrowed(v_snd_1805_, v_head_1802_);
lean_inc(v___x_1828_);
v___y_1815_ = v___y_1825_;
v___y_1816_ = v___x_1828_;
goto v___jp_1814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_labelEdgesAccordingToRankings(lean_object* v_vertexCount_1835_, lean_object* v_vertexRankings_1836_, lean_object* v_G_1837_){
_start:
{
lean_object* v_vertices_1838_; lean_object* v_denseRankings_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v_fst_1842_; 
lean_inc(v_vertexCount_1835_);
v_vertices_1838_ = l_List_finRange(v_vertexCount_1835_);
v_denseRankings_1839_ = lp_GraphCanonizationProofs___private_LeanGraphCanonizerV4_0__Graph_computeDenseRanks(v_vertexCount_1835_, v_vertexRankings_1836_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_G_1837_);
lean_ctor_set(v___x_1840_, 1, v_denseRankings_1839_);
lean_inc(v_vertices_1838_);
v___x_1841_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg(v_vertices_1838_, v___x_1840_, v_vertices_1838_);
v_fst_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_fst_1842_);
lean_dec_ref(v___x_1841_);
return v_fst_1842_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_labelEdgesAccordingToRankings___boxed(lean_object* v_vertexCount_1843_, lean_object* v_vertexRankings_1844_, lean_object* v_G_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = lp_GraphCanonizationProofs_Graph_labelEdgesAccordingToRankings(v_vertexCount_1843_, v_vertexRankings_1844_, v_G_1845_);
lean_dec_ref(v_vertexRankings_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0(lean_object* v_vertices_1847_, lean_object* v_vertexCount_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___redArg(v_vertices_1847_, v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0___boxed(lean_object* v_vertices_1852_, lean_object* v_vertexCount_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_labelEdgesAccordingToRankings_spec__0(v_vertices_1852_, v_vertexCount_1853_, v_x_1854_, v_x_1855_);
lean_dec(v_vertexCount_1853_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_run(lean_object* v_vertexCount_1857_, lean_object* v_vertexTypes_1858_, lean_object* v_G_1859_){
_start:
{
lean_object* v_vertexRanks_1860_; lean_object* v_state_1861_; lean_object* v_orderedRanks_1862_; lean_object* v___x_1863_; 
v_vertexRanks_1860_ = lp_GraphCanonizationProofs_Graph_getArrayRank(v_vertexTypes_1858_);
lean_inc_ref(v_G_1859_);
lean_inc(v_vertexCount_1857_);
v_state_1861_ = lp_GraphCanonizationProofs_Graph_initializePaths(v_vertexCount_1857_, v_G_1859_);
v_orderedRanks_1862_ = lp_GraphCanonizationProofs_Graph_orderVertices(v_state_1861_, v_vertexRanks_1860_);
v___x_1863_ = lp_GraphCanonizationProofs_Graph_labelEdgesAccordingToRankings(v_vertexCount_1857_, v_orderedRanks_1862_, v_G_1859_);
lean_dec_ref(v_orderedRanks_1862_);
return v___x_1863_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_aesop_Aesop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GraphCanonizationProofs_LeanGraphCanonizerV4(uint8_t builtin) {
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
