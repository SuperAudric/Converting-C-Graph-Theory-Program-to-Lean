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
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l_List_zipWith___at___00List_zip_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
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
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_0),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_1),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value_aux_2),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Isomorphic"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value;
static lean_once_cell_t lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(240, 190, 20, 130, 109, 57, 74, 242)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 36, 206, 233, 246, 43, 71, 96)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_0),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix_term___u2243___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 144, 243, 39, 60, 12, 127, 183)}};
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value_aux_1),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 168, 201, 31, 52, 68, 229)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__8_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__9_value),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__11_value)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12_value;
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value;
static const lean_ctor_object lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1 = (const lean_object*)&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1_value;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "GraphStructureAttempt1"};
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
static lean_once_cell_t lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt___closed__0;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt;
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_br(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_br___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0(lean_object* v_i_1_, lean_object* v_j_2_, lean_object* v_G_3_, lean_object* v_u_4_, lean_object* v_v_5_){
_start:
{
uint8_t v___x_6_; uint8_t v___x_7_; lean_object* v___y_9_; 
v___x_6_ = lean_nat_dec_eq(v_u_4_, v_i_1_);
v___x_7_ = lean_nat_dec_eq(v_v_5_, v_i_1_);
if (v___x_6_ == 0)
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_u_4_, v_j_2_);
if (v___x_14_ == 0)
{
v___y_9_ = v_u_4_;
goto v___jp_8_;
}
else
{
lean_dec(v_u_4_);
lean_inc(v_i_1_);
v___y_9_ = v_i_1_;
goto v___jp_8_;
}
}
else
{
lean_dec(v_u_4_);
lean_inc(v_j_2_);
v___y_9_ = v_j_2_;
goto v___jp_8_;
}
v___jp_8_:
{
if (v___x_7_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_eq(v_v_5_, v_j_2_);
lean_dec(v_j_2_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec(v_i_1_);
v___x_11_ = lean_apply_2(v_G_3_, v___y_9_, v_v_5_);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
lean_dec(v_v_5_);
v___x_12_ = lean_apply_2(v_G_3_, v___y_9_, v_i_1_);
return v___x_12_;
}
}
else
{
lean_object* v___x_13_; 
lean_dec(v_v_5_);
lean_dec(v_i_1_);
v___x_13_ = lean_apply_2(v_G_3_, v___y_9_, v_j_2_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg(lean_object* v_i_15_, lean_object* v_j_16_, lean_object* v_G_17_){
_start:
{
lean_object* v___f_18_; 
v___f_18_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v___f_18_, 0, v_i_15_);
lean_closure_set(v___f_18_, 1, v_j_16_);
lean_closure_set(v___f_18_, 2, v_G_17_);
return v___f_18_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices(lean_object* v_n_19_, lean_object* v_i_20_, lean_object* v_j_21_, lean_object* v_G_22_){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___redArg___lam__0), 5, 3);
lean_closure_set(v___f_23_, 0, v_i_20_);
lean_closure_set(v___f_23_, 1, v_j_21_);
lean_closure_set(v___f_23_, 2, v_G_22_);
return v___f_23_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices___boxed(lean_object* v_n_24_, lean_object* v_i_25_, lean_object* v_j_26_, lean_object* v_G_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GraphCanonizationProofs_Graph_AdjMatrix_swapVertices(v_n_24_, v_i_25_, v_j_26_, v_G_27_);
lean_dec(v_n_24_);
return v_res_28_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__5));
v___x_68_ = l_String_toRawSubstring_x27(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1(lean_object* v_x_89_, lean_object* v_a_90_, lean_object* v_a_91_){
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
v___x_105_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4));
v___x_106_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6, &lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6_once, _init_lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__6);
v___x_107_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__7));
lean_inc(v_currMacroScope_97_);
lean_inc(v_quotContext_96_);
v___x_108_ = l_Lean_addMacroScope(v_quotContext_96_, v___x_107_, v_currMacroScope_97_);
v___x_109_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__12));
lean_inc_n(v___x_104_, 2);
v___x_110_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_110_, 0, v___x_104_);
lean_ctor_set(v___x_110_, 1, v___x_106_);
lean_ctor_set(v___x_110_, 2, v___x_108_);
lean_ctor_set(v___x_110_, 3, v___x_109_);
v___x_111_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__14));
v___x_112_ = l_Lean_Syntax_node2(v___x_104_, v___x_111_, v___x_100_, v___x_102_);
v___x_113_ = l_Lean_Syntax_node2(v___x_104_, v___x_105_, v___x_110_, v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_91_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___boxed(lean_object* v_x_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1(v_x_115_, v_a_116_, v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______macroRules__Graph__AdjMatrix__term___u2243____1___closed__4));
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
v___x_131_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___closed__1));
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
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1___boxed(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = lp_GraphCanonizationProofs_Graph_AdjMatrix___aux__GraphStructureAttempt1______unexpand__Graph__AdjMatrix__Isomorphic__1(v_x_151_, v_a_152_, v_a_153_);
lean_dec(v_a_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(lean_object* v_G_155_, lean_object* v_i_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
if (lean_obj_tag(v_a_157_) == 0)
{
lean_object* v___x_159_; 
lean_dec(v_i_156_);
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
lean_inc(v_i_156_);
v___x_165_ = lean_apply_2(v_G_155_, v_i_156_, v_head_160_);
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
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(lean_object* v_G_174_, lean_object* v_rows_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_object* v___x_178_; 
lean_dec(v_rows_175_);
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
lean_object* v___x_184_; lean_object* v_rowString_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_184_ = lean_box(0);
lean_inc(v_rows_175_);
lean_inc_ref(v_G_174_);
v_rowString_185_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__0(v_G_174_, v_head_179_, v_rows_175_, v___x_184_);
v___x_186_ = ((lean_object*)(lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__0));
v___x_187_ = l_List_intersperseTR___redArg(v___x_186_, v_rowString_185_);
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
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString(lean_object* v_n_196_, lean_object* v_G_197_){
_start:
{
lean_object* v_rows_198_; lean_object* v___x_199_; lean_object* v_rowStrings_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_rows_198_ = l_List_finRange(v_n_196_);
v___x_199_ = lean_box(0);
lean_inc(v_rows_198_);
v_rowStrings_200_ = lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1(v_G_197_, v_rows_198_, v_rows_198_, v___x_199_);
v___x_201_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString___closed__0));
v___x_202_ = l_List_intersperseTR___redArg(v___x_201_, v_rowStrings_200_);
v___x_203_ = ((lean_object*)(lp_GraphCanonizationProofs_List_mapTR_loop___at___00Graph_AdjMatrix_adjToString_spec__1___closed__1));
v___x_204_ = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(v___x_203_, v___x_202_);
lean_dec(v___x_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_AdjMatrix_instToString(lean_object* v_n_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_AdjMatrix_adjToString), 2, 1);
lean_closure_set(v___x_206_, 0, v_n_205_);
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
lean_inc(v___y_296_);
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_296_);
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
lean_inc(v___y_295_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___y_295_);
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
v___y_295_ = v___y_317_;
v___y_296_ = v___x_319_;
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
v___y_295_ = v___y_317_;
v___y_296_ = v___x_319_;
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
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(lean_object* v_x_658_, lean_object* v_as_659_, size_t v_i_660_, size_t v_stop_661_, lean_object* v_b_662_){
_start:
{
lean_object* v___y_664_; uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_eq(v_i_660_, v_stop_661_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_array_uget_borrowed(v_as_659_, v_i_660_);
v___x_670_ = lean_int_dec_lt(v___x_669_, v_x_658_);
if (v___x_670_ == 0)
{
v___y_664_ = v_b_662_;
goto v___jp_663_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4);
v___x_672_ = lean_int_add(v_b_662_, v___x_671_);
lean_dec(v_b_662_);
v___y_664_ = v___x_672_;
goto v___jp_663_;
}
}
else
{
return v_b_662_;
}
v___jp_663_:
{
size_t v___x_665_; size_t v___x_666_; 
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_660_, v___x_665_);
v_i_660_ = v___x_666_;
v_b_662_ = v___y_664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0___boxed(lean_object* v_x_673_, lean_object* v_as_674_, lean_object* v_i_675_, lean_object* v_stop_676_, lean_object* v_b_677_){
_start:
{
size_t v_i_boxed_678_; size_t v_stop_boxed_679_; lean_object* v_res_680_; 
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_stop_boxed_679_ = lean_unbox_usize(v_stop_676_);
lean_dec(v_stop_676_);
v_res_680_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(v_x_673_, v_as_674_, v_i_boxed_678_, v_stop_boxed_679_, v_b_677_);
lean_dec_ref(v_as_674_);
lean_dec(v_x_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(lean_object* v_arr_681_, size_t v_sz_682_, size_t v_i_683_, lean_object* v_bs_684_){
_start:
{
uint8_t v___x_685_; 
v___x_685_ = lean_usize_dec_lt(v_i_683_, v_sz_682_);
if (v___x_685_ == 0)
{
return v_bs_684_;
}
else
{
lean_object* v_v_686_; lean_object* v___x_687_; lean_object* v_bs_x27_688_; lean_object* v___y_690_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_v_686_ = lean_array_uget(v_bs_684_, v_i_683_);
v___x_687_ = lean_unsigned_to_nat(0u);
v_bs_x27_688_ = lean_array_uset(v_bs_684_, v_i_683_, v___x_687_);
v___x_695_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_696_ = lean_array_get_size(v_arr_681_);
v___x_697_ = lean_nat_dec_lt(v___x_687_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec(v_v_686_);
v___y_690_ = v___x_695_;
goto v___jp_689_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_le(v___x_696_, v___x_696_);
if (v___x_698_ == 0)
{
if (v___x_697_ == 0)
{
lean_dec(v_v_686_);
v___y_690_ = v___x_695_;
goto v___jp_689_;
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_696_);
v___x_701_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(v_v_686_, v_arr_681_, v___x_699_, v___x_700_, v___x_695_);
lean_dec(v_v_686_);
v___y_690_ = v___x_701_;
goto v___jp_689_;
}
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((size_t)0ULL);
v___x_703_ = lean_usize_of_nat(v___x_696_);
v___x_704_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Graph_getArrayRank_spec__0(v_v_686_, v_arr_681_, v___x_702_, v___x_703_, v___x_695_);
lean_dec(v_v_686_);
v___y_690_ = v___x_704_;
goto v___jp_689_;
}
}
v___jp_689_:
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_683_, v___x_691_);
v___x_693_ = lean_array_uset(v_bs_x27_688_, v_i_683_, v___y_690_);
v_i_683_ = v___x_692_;
v_bs_684_ = v___x_693_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1___boxed(lean_object* v_arr_705_, lean_object* v_sz_706_, lean_object* v_i_707_, lean_object* v_bs_708_){
_start:
{
size_t v_sz_boxed_709_; size_t v_i_boxed_710_; lean_object* v_res_711_; 
v_sz_boxed_709_ = lean_unbox_usize(v_sz_706_);
lean_dec(v_sz_706_);
v_i_boxed_710_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_res_711_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(v_arr_705_, v_sz_boxed_709_, v_i_boxed_710_, v_bs_708_);
lean_dec_ref(v_arr_705_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_getArrayRank(lean_object* v_arr_712_){
_start:
{
size_t v_sz_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_sz_713_ = lean_array_size(v_arr_712_);
v___x_714_ = ((size_t)0ULL);
lean_inc_ref(v_arr_712_);
v___x_715_ = lp_GraphCanonizationProofs___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Graph_getArrayRank_spec__1(v_arr_712_, v_sz_713_, v___x_714_, v_arr_712_);
lean_dec_ref(v_arr_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_insertSorted___redArg(lean_object* v_cmp_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v_cmp_716_);
v___x_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_719_, 0, v_x_717_);
lean_ctor_set(v___x_719_, 1, v_x_718_);
return v___x_719_;
}
else
{
lean_object* v_head_720_; lean_object* v_tail_721_; lean_object* v___x_722_; uint8_t v___x_723_; uint8_t v___x_724_; uint8_t v___x_725_; 
v_head_720_ = lean_ctor_get(v_x_718_, 0);
v_tail_721_ = lean_ctor_get(v_x_718_, 1);
lean_inc_ref(v_cmp_716_);
lean_inc(v_head_720_);
lean_inc(v_x_717_);
v___x_722_ = lean_apply_2(v_cmp_716_, v_x_717_, v_head_720_);
v___x_723_ = 2;
v___x_724_ = lean_unbox(v___x_722_);
v___x_725_ = l_instDecidableEqOrdering(v___x_724_, v___x_723_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref(v_cmp_716_);
v___x_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_726_, 0, v_x_717_);
lean_ctor_set(v___x_726_, 1, v_x_718_);
return v___x_726_;
}
else
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
lean_inc(v_tail_721_);
lean_inc(v_head_720_);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_735_ = lean_ctor_get(v_x_718_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_x_718_, 0);
lean_dec(v_unused_736_);
v___x_728_ = v_x_718_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_x_718_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lp_GraphCanonizationProofs_Graph_insertSorted___redArg(v_cmp_716_, v_x_717_, v_tail_721_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_head_720_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_insertSorted(lean_object* v_00_u03b1_737_, lean_object* v_cmp_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lp_GraphCanonizationProofs_Graph_insertSorted___redArg(v_cmp_738_, v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_sortBy___redArg(lean_object* v_cmp_742_, lean_object* v_x_743_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_dec_ref(v_cmp_742_);
return v_x_743_;
}
else
{
lean_object* v_head_744_; lean_object* v_tail_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_head_744_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_head_744_);
v_tail_745_ = lean_ctor_get(v_x_743_, 1);
lean_inc(v_tail_745_);
lean_dec_ref(v_x_743_);
lean_inc_ref(v_cmp_742_);
v___x_746_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_742_, v_tail_745_);
v___x_747_ = lp_GraphCanonizationProofs_Graph_insertSorted___redArg(v_cmp_742_, v_head_744_, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_sortBy(lean_object* v_00_u03b1_748_, lean_object* v_cmp_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_749_, v_x_750_);
return v___x_751_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(lean_object* v_cmp_752_, uint8_t v_x_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_dec_ref(v_cmp_752_);
return v_x_753_;
}
else
{
lean_object* v_head_755_; lean_object* v_tail_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; uint8_t v___x_759_; uint8_t v___x_760_; 
v_head_755_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_head_755_);
v_tail_756_ = lean_ctor_get(v_x_754_, 1);
lean_inc(v_tail_756_);
lean_dec_ref(v_x_754_);
v_fst_757_ = lean_ctor_get(v_head_755_, 0);
lean_inc(v_fst_757_);
v_snd_758_ = lean_ctor_get(v_head_755_, 1);
lean_inc(v_snd_758_);
lean_dec(v_head_755_);
v___x_759_ = 1;
v___x_760_ = l_instDecidableEqOrdering(v_x_753_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_snd_758_);
lean_dec(v_fst_757_);
v_x_754_ = v_tail_756_;
goto _start;
}
else
{
lean_object* v___x_762_; uint8_t v___x_763_; 
lean_inc_ref(v_cmp_752_);
v___x_762_ = lean_apply_2(v_cmp_752_, v_fst_757_, v_snd_758_);
v___x_763_ = lean_unbox(v___x_762_);
v_x_753_ = v___x_763_;
v_x_754_ = v_tail_756_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg___boxed(lean_object* v_cmp_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_x_241__boxed_768_; uint8_t v_res_769_; lean_object* v_r_770_; 
v_x_241__boxed_768_ = lean_unbox(v_x_766_);
v_res_769_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(v_cmp_765_, v_x_241__boxed_768_, v_x_767_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(lean_object* v_cmp_771_, lean_object* v_l1_772_, lean_object* v_l2_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = l_List_lengthTR___redArg(v_l1_772_);
v___x_775_ = l_List_lengthTR___redArg(v_l2_773_);
v___x_776_ = lean_nat_dec_eq(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
uint8_t v___x_777_; 
lean_dec(v_l2_773_);
lean_dec(v_l1_772_);
lean_dec_ref(v_cmp_771_);
v___x_777_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
lean_dec(v___x_775_);
lean_dec(v___x_774_);
if (v___x_777_ == 0)
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = 2;
return v___x_779_;
}
}
else
{
uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
lean_dec(v___x_775_);
lean_dec(v___x_774_);
v___x_780_ = 1;
lean_inc_ref_n(v_cmp_771_, 2);
v___x_781_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_771_, v_l1_772_);
v___x_782_ = lp_GraphCanonizationProofs_Graph_sortBy___redArg(v_cmp_771_, v_l2_773_);
v___x_783_ = l_List_zipWith___at___00List_zip_spec__0___redArg(v___x_781_, v___x_782_);
v___x_784_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(v_cmp_771_, v___x_780_, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg___boxed(lean_object* v_cmp_785_, lean_object* v_l1_786_, lean_object* v_l2_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v_cmp_785_, v_l1_786_, v_l2_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp(lean_object* v_00_u03b1_790_, lean_object* v_cmp_791_, lean_object* v_l1_792_, lean_object* v_l2_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v_cmp_791_, v_l1_792_, v_l2_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___boxed(lean_object* v_00_u03b1_795_, lean_object* v_cmp_796_, lean_object* v_l1_797_, lean_object* v_l2_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp(v_00_u03b1_795_, v_cmp_796_, v_l1_797_, v_l2_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0(lean_object* v_00_u03b1_801_, lean_object* v_cmp_802_, uint8_t v_x_803_, lean_object* v_x_804_){
_start:
{
uint8_t v___x_805_; 
v___x_805_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___redArg(v_cmp_802_, v_x_803_, v_x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0___boxed(lean_object* v_00_u03b1_806_, lean_object* v_cmp_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
uint8_t v_x_291__boxed_810_; uint8_t v_res_811_; lean_object* v_r_812_; 
v_x_291__boxed_810_ = lean_unbox(v_x_808_);
v_res_811_ = lp_GraphCanonizationProofs_List_foldl___at___00Graph_orderInsensitiveListCmp_spec__0(v_00_u03b1_806_, v_cmp_807_, v_x_291__boxed_810_, v_x_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(lean_object* v_msg_813_){
_start:
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_814_ = 0;
v___x_815_ = lean_box(v___x_814_);
v___x_816_ = lean_panic_fn_borrowed(v___x_815_, v_msg_813_);
lean_dec(v___x_815_);
v___x_817_ = lean_unbox(v___x_816_);
lean_dec(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0___boxed(lean_object* v_msg_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(v_msg_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_824_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__2));
v___x_825_ = lean_unsigned_to_nat(12u);
v___x_826_ = lean_unsigned_to_nat(152u);
v___x_827_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__1));
v___x_828_ = ((lean_object*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__0));
v___x_829_ = l_mkPanicMessageWithDecl(v___x_828_, v___x_827_, v___x_826_, v___x_825_, v___x_824_);
return v___x_829_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathSegments(lean_object* v_vertexTypes_830_, lean_object* v_betweenRanks_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___y_835_; lean_object* v___y_836_; 
if (lean_obj_tag(v_x_832_) == 0)
{
lean_dec_ref(v_betweenRanks_831_);
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v_vertexIndex_845_; lean_object* v_vertexIndex_846_; lean_object* v___x_847_; lean_object* v___y_849_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_vertexIndex_845_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_vertexIndex_845_);
lean_dec_ref(v_x_832_);
v_vertexIndex_846_ = lean_ctor_get(v_x_833_, 0);
lean_inc(v_vertexIndex_846_);
lean_dec_ref(v_x_833_);
v___x_847_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_853_ = lean_array_get_size(v_vertexTypes_830_);
v___x_854_ = lean_nat_dec_lt(v_vertexIndex_845_, v___x_853_);
if (v___x_854_ == 0)
{
lean_dec(v_vertexIndex_845_);
v___y_849_ = v___x_847_;
goto v___jp_848_;
}
else
{
lean_object* v___x_855_; 
v___x_855_ = lean_array_fget_borrowed(v_vertexTypes_830_, v_vertexIndex_845_);
lean_dec(v_vertexIndex_845_);
v___y_849_ = v___x_855_;
goto v___jp_848_;
}
v___jp_848_:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_array_get_size(v_vertexTypes_830_);
v___x_851_ = lean_nat_dec_lt(v_vertexIndex_846_, v___x_850_);
if (v___x_851_ == 0)
{
lean_dec(v_vertexIndex_846_);
v___y_835_ = v___y_849_;
v___y_836_ = v___x_847_;
goto v___jp_834_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = lean_array_fget_borrowed(v_vertexTypes_830_, v_vertexIndex_846_);
lean_dec(v_vertexIndex_846_);
v___y_835_ = v___y_849_;
v___y_836_ = v___x_852_;
goto v___jp_834_;
}
}
}
else
{
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_833_);
goto v___jp_842_;
}
}
else
{
if (lean_obj_tag(v_x_833_) == 1)
{
lean_object* v_edgeType_856_; lean_object* v_subDepth_857_; lean_object* v_subStart_858_; lean_object* v_subEnd_859_; lean_object* v_edgeType_860_; lean_object* v_subDepth_861_; lean_object* v_subStart_862_; lean_object* v_subEnd_863_; lean_object* v_rx_864_; lean_object* v_ry_865_; uint8_t v___x_866_; 
v_edgeType_856_ = lean_ctor_get(v_x_832_, 0);
lean_inc(v_edgeType_856_);
v_subDepth_857_ = lean_ctor_get(v_x_832_, 1);
lean_inc(v_subDepth_857_);
v_subStart_858_ = lean_ctor_get(v_x_832_, 2);
lean_inc(v_subStart_858_);
v_subEnd_859_ = lean_ctor_get(v_x_832_, 3);
lean_inc(v_subEnd_859_);
lean_dec_ref(v_x_832_);
v_edgeType_860_ = lean_ctor_get(v_x_833_, 0);
lean_inc(v_edgeType_860_);
v_subDepth_861_ = lean_ctor_get(v_x_833_, 1);
lean_inc(v_subDepth_861_);
v_subStart_862_ = lean_ctor_get(v_x_833_, 2);
lean_inc(v_subStart_862_);
v_subEnd_863_ = lean_ctor_get(v_x_833_, 3);
lean_inc(v_subEnd_863_);
lean_dec_ref(v_x_833_);
lean_inc_ref(v_betweenRanks_831_);
v_rx_864_ = lean_apply_3(v_betweenRanks_831_, v_subDepth_857_, v_subStart_858_, v_subEnd_859_);
v_ry_865_ = lean_apply_3(v_betweenRanks_831_, v_subDepth_861_, v_subStart_862_, v_subEnd_863_);
v___x_866_ = lean_int_dec_eq(v_rx_864_, v_ry_865_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
lean_dec(v_edgeType_860_);
lean_dec(v_edgeType_856_);
v___x_867_ = lean_int_dec_lt(v_ry_865_, v_rx_864_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
v___x_868_ = lean_int_dec_eq(v_ry_865_, v_rx_864_);
lean_dec(v_rx_864_);
lean_dec(v_ry_865_);
if (v___x_868_ == 0)
{
uint8_t v___x_869_; 
v___x_869_ = 2;
return v___x_869_;
}
else
{
uint8_t v___x_870_; 
v___x_870_ = 1;
return v___x_870_;
}
}
else
{
uint8_t v___x_871_; 
lean_dec(v_ry_865_);
lean_dec(v_rx_864_);
v___x_871_ = 0;
return v___x_871_;
}
}
else
{
uint8_t v___x_872_; 
lean_dec(v_ry_865_);
lean_dec(v_rx_864_);
v___x_872_ = lean_int_dec_eq(v_edgeType_856_, v_edgeType_860_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = lean_int_dec_lt(v_edgeType_860_, v_edgeType_856_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = lean_int_dec_eq(v_edgeType_860_, v_edgeType_856_);
lean_dec(v_edgeType_856_);
lean_dec(v_edgeType_860_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = 2;
return v___x_875_;
}
else
{
uint8_t v___x_876_; 
v___x_876_ = 1;
return v___x_876_;
}
}
else
{
uint8_t v___x_877_; 
lean_dec(v_edgeType_860_);
lean_dec(v_edgeType_856_);
v___x_877_ = 0;
return v___x_877_;
}
}
else
{
uint8_t v___x_878_; 
lean_dec(v_edgeType_860_);
lean_dec(v_edgeType_856_);
v___x_878_ = 1;
return v___x_878_;
}
}
}
else
{
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_betweenRanks_831_);
goto v___jp_842_;
}
}
v___jp_834_:
{
uint8_t v___x_837_; 
v___x_837_ = lean_int_dec_lt(v___y_835_, v___y_836_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
v___x_838_ = lean_int_dec_eq(v___y_835_, v___y_836_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; 
v___x_839_ = 2;
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
v___x_840_ = 1;
return v___x_840_;
}
}
else
{
uint8_t v___x_841_; 
v___x_841_ = 0;
return v___x_841_;
}
}
v___jp_842_:
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3, &lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3_once, _init_lp_GraphCanonizationProofs_Graph_comparePathSegments___closed__3);
v___x_844_ = lp_GraphCanonizationProofs_panic___at___00Graph_comparePathSegments_spec__0(v___x_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathSegments___boxed(lean_object* v_vertexTypes_879_, lean_object* v_betweenRanks_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = lp_GraphCanonizationProofs_Graph_comparePathSegments(v_vertexTypes_879_, v_betweenRanks_880_, v_x_881_, v_x_882_);
lean_dec_ref(v_vertexTypes_879_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathsBetween(lean_object* v_vertexTypes_885_, lean_object* v_betweenRanks_886_, lean_object* v_x_887_, lean_object* v_y_888_){
_start:
{
lean_object* v_endVertexIndex_889_; lean_object* v_connectedSubPaths_890_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___x_902_; lean_object* v___y_904_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_endVertexIndex_889_ = lean_ctor_get(v_x_887_, 2);
lean_inc(v_endVertexIndex_889_);
v_connectedSubPaths_890_ = lean_ctor_get(v_x_887_, 3);
lean_inc(v_connectedSubPaths_890_);
lean_dec_ref(v_x_887_);
v___x_902_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_909_ = lean_array_get_size(v_vertexTypes_885_);
v___x_910_ = lean_nat_dec_lt(v_endVertexIndex_889_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec(v_endVertexIndex_889_);
v___y_904_ = v___x_902_;
goto v___jp_903_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_array_fget_borrowed(v_vertexTypes_885_, v_endVertexIndex_889_);
lean_dec(v_endVertexIndex_889_);
lean_inc(v___x_911_);
v___y_904_ = v___x_911_;
goto v___jp_903_;
}
v___jp_891_:
{
uint8_t v___x_894_; 
v___x_894_ = lean_int_dec_eq(v___y_892_, v___y_893_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
lean_dec(v_connectedSubPaths_890_);
lean_dec_ref(v_y_888_);
lean_dec_ref(v_betweenRanks_886_);
lean_dec_ref(v_vertexTypes_885_);
v___x_895_ = lean_int_dec_lt(v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
if (v___x_895_ == 0)
{
if (v___x_894_ == 0)
{
uint8_t v___x_896_; 
v___x_896_ = 2;
return v___x_896_;
}
else
{
uint8_t v___x_897_; 
v___x_897_ = 1;
return v___x_897_;
}
}
else
{
uint8_t v___x_898_; 
v___x_898_ = 0;
return v___x_898_;
}
}
else
{
lean_object* v_connectedSubPaths_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
lean_dec(v___y_893_);
lean_dec(v___y_892_);
v_connectedSubPaths_899_ = lean_ctor_get(v_y_888_, 3);
lean_inc(v_connectedSubPaths_899_);
lean_dec_ref(v_y_888_);
v___x_900_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_comparePathSegments___boxed), 4, 2);
lean_closure_set(v___x_900_, 0, v_vertexTypes_885_);
lean_closure_set(v___x_900_, 1, v_betweenRanks_886_);
v___x_901_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v___x_900_, v_connectedSubPaths_890_, v_connectedSubPaths_899_);
return v___x_901_;
}
}
v___jp_903_:
{
lean_object* v_endVertexIndex_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_endVertexIndex_905_ = lean_ctor_get(v_y_888_, 2);
v___x_906_ = lean_array_get_size(v_vertexTypes_885_);
v___x_907_ = lean_nat_dec_lt(v_endVertexIndex_905_, v___x_906_);
if (v___x_907_ == 0)
{
v___y_892_ = v___y_904_;
v___y_893_ = v___x_902_;
goto v___jp_891_;
}
else
{
lean_object* v___x_908_; 
v___x_908_ = lean_array_fget_borrowed(v_vertexTypes_885_, v_endVertexIndex_905_);
lean_inc(v___x_908_);
v___y_892_ = v___y_904_;
v___y_893_ = v___x_908_;
goto v___jp_891_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathsBetween___boxed(lean_object* v_vertexTypes_912_, lean_object* v_betweenRanks_913_, lean_object* v_x_914_, lean_object* v_y_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = lp_GraphCanonizationProofs_Graph_comparePathsBetween(v_vertexTypes_912_, v_betweenRanks_913_, v_x_914_, v_y_915_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT uint8_t lp_GraphCanonizationProofs_Graph_comparePathsFrom(lean_object* v_vertexTypes_918_, lean_object* v_betweenRanks_919_, lean_object* v_x_920_, lean_object* v_y_921_){
_start:
{
lean_object* v_startVertexIndex_922_; lean_object* v_pathsToVertex_923_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___x_935_; lean_object* v___y_937_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_startVertexIndex_922_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_startVertexIndex_922_);
v_pathsToVertex_923_ = lean_ctor_get(v_x_920_, 2);
lean_inc(v_pathsToVertex_923_);
lean_dec_ref(v_x_920_);
v___x_935_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_942_ = lean_array_get_size(v_vertexTypes_918_);
v___x_943_ = lean_nat_dec_lt(v_startVertexIndex_922_, v___x_942_);
if (v___x_943_ == 0)
{
lean_dec(v_startVertexIndex_922_);
v___y_937_ = v___x_935_;
goto v___jp_936_;
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_array_fget_borrowed(v_vertexTypes_918_, v_startVertexIndex_922_);
lean_dec(v_startVertexIndex_922_);
lean_inc(v___x_944_);
v___y_937_ = v___x_944_;
goto v___jp_936_;
}
v___jp_924_:
{
uint8_t v___x_927_; 
v___x_927_ = lean_int_dec_eq(v___y_925_, v___y_926_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
lean_dec(v_pathsToVertex_923_);
lean_dec_ref(v_y_921_);
lean_dec_ref(v_betweenRanks_919_);
lean_dec_ref(v_vertexTypes_918_);
v___x_928_ = lean_int_dec_lt(v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec(v___y_925_);
if (v___x_928_ == 0)
{
if (v___x_927_ == 0)
{
uint8_t v___x_929_; 
v___x_929_ = 2;
return v___x_929_;
}
else
{
uint8_t v___x_930_; 
v___x_930_ = 1;
return v___x_930_;
}
}
else
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
else
{
lean_object* v_pathsToVertex_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
lean_dec(v___y_926_);
lean_dec(v___y_925_);
v_pathsToVertex_932_ = lean_ctor_get(v_y_921_, 2);
lean_inc(v_pathsToVertex_932_);
lean_dec_ref(v_y_921_);
v___x_933_ = lean_alloc_closure((void*)(lp_GraphCanonizationProofs_Graph_comparePathsBetween___boxed), 4, 2);
lean_closure_set(v___x_933_, 0, v_vertexTypes_918_);
lean_closure_set(v___x_933_, 1, v_betweenRanks_919_);
v___x_934_ = lp_GraphCanonizationProofs_Graph_orderInsensitiveListCmp___redArg(v___x_933_, v_pathsToVertex_923_, v_pathsToVertex_932_);
return v___x_934_;
}
}
v___jp_936_:
{
lean_object* v_startVertexIndex_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_startVertexIndex_938_ = lean_ctor_get(v_y_921_, 1);
v___x_939_ = lean_array_get_size(v_vertexTypes_918_);
v___x_940_ = lean_nat_dec_lt(v_startVertexIndex_938_, v___x_939_);
if (v___x_940_ == 0)
{
v___y_925_ = v___y_937_;
v___y_926_ = v___x_935_;
goto v___jp_924_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = lean_array_fget_borrowed(v_vertexTypes_918_, v_startVertexIndex_938_);
lean_inc(v___x_941_);
v___y_925_ = v___y_937_;
v___y_926_ = v___x_941_;
goto v___jp_924_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs_Graph_comparePathsFrom___boxed(lean_object* v_vertexTypes_945_, lean_object* v_betweenRanks_946_, lean_object* v_x_947_, lean_object* v_y_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = lp_GraphCanonizationProofs_Graph_comparePathsFrom(v_vertexTypes_945_, v_betweenRanks_946_, v_x_947_, v_y_948_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt___closed__0(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_951_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__3);
v___x_952_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__4);
v___x_953_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
v___x_956_ = lean_array_push(v___x_955_, v___x_953_);
v___x_957_ = lean_array_push(v___x_956_, v___x_952_);
v___x_958_ = lean_array_push(v___x_957_, v___x_951_);
return v___x_958_;
}
}
static lean_object* _init_lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = lean_obj_once(&lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt___closed__0, &lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt___closed__0_once, _init_lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt___closed__0);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_br(lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8, &lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8_once, _init_lp_GraphCanonizationProofs_Graph_instReprPathSegment_repr___closed__8);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_br___boxed(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_br(v_x_964_, v_x_965_, v_x_966_);
lean_dec(v_x_966_);
lean_dec(v_x_965_);
lean_dec(v_x_964_);
return v_res_967_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_aesop_Aesop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GraphCanonizationProofs_GraphStructureAttempt1(uint8_t builtin) {
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
lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt = _init_lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt();
lean_mark_persistent(lp_GraphCanonizationProofs___private_GraphStructureAttempt1_0__Graph_vt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
