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

/* Z3NameUnits.scan_units (Z3NameUnits-c.cherry.fst), a TRUSTED runtime binding:
   FStar.String.strlen s when that is at most limit, else -1, for every nat limit.
   It steps over the characters as FStar.String's decoder does (one per lead byte,
   of width 1 below 0x80, 2 below 0xE0, 3 below 0xF0, otherwise 4; a width past
   the end ends the string) and stops before stepping over a character beyond
   limit. It reads one lead byte per step, at most min(strlen s, limit), never one
   at or past the end, and allocates nothing. The limit is compared numerically,
   whatever its representation; one at or above the byte size n counts fully. On
   the platforms build_cherry_checker.py admits (x86-64, AArch64) a string's n is
   below 2^57 < CHERRY_INT_MAX, so CHERRY_INT_SMALL(n) and the count are exact.
   Both arguments are borrowed. */
static size_t z3_name_width(unsigned char b) {
    return b < 0x80 ? 1 : b < 0xE0 ? 2 : b < 0xF0 ? 3 : 4;
}

intptr_t z3_name_units_scan_counted(cherry_string s, cherry_int limit, size_t *reads) {
    size_t n = cherry_str_size(s), cap = n, i = 0, k = 0;
    const unsigned char *bytes = (const unsigned char *)cherry_str_data(s);
    if (cherry_int_lt(limit, CHERRY_INT_SMALL((intptr_t)n)))
        cap = (size_t)cherry_int_to_u64(limit);
    while (i < n) {
        if (k == cap) {
            *reads = k;
            return -1;
        }
        size_t width = z3_name_width(bytes[i]);
        i = width < n - i ? i + width : n;
        k++;
    }
    *reads = k;
    return (intptr_t)k;
}

cherry_int z3_name_units_scan(cherry_string s, cherry_int limit) {
    size_t reads;
    return CHERRY_INT_SMALL(z3_name_units_scan_counted(s, limit, &reads));
}
