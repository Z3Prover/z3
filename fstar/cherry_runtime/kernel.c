#include "Z3Cherry.c"

void checker_drop_marshaled(Z3Cherry_marshaled value) {
    cherry_dec_Z3Cherry_marshaled(value);
}

void checker_drop_diagnostic(Z3ProofDocument_document_diagnostic value) {
    cherry_dec_Z3ProofDocument_document_diagnostic(value);
}

void checker_drop_sort(Z3AstTheory_sort value) {
    cherry_dec_Z3AstTheory_sort(value);
}

void checker_drop_native_sorts(Prims_list__native_sort value) {
    cherry_dec_Prims_list__native_sort(value);
}

void checker_drop_asts(Prims_list__ast value) {
    cherry_dec_Prims_list__ast(value);
}

void checker_drop_result(FStar_Pervasives_Native_option__int value) {
    cherry_dec_FStar_Pervasives_Native_option__int(value);
}

void checker_drop_ff_pac(FStar_Pervasives_Native_option__ff_pac_view value) {
    cherry_dec_FStar_Pervasives_Native_option__ff_pac_view(value);
}
