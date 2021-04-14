/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    api_seq.cpp

Abstract:

    API for sequences and regular expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2016-01-02.

Revision History:

--*/
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/ast_pp.h"

extern "C" {

    Z3_sort Z3_API Z3_mk_seq_sort(Z3_context c, Z3_sort domain) {
        Z3_TRY;
        LOG_Z3_mk_seq_sort(c, domain);
        RESET_ERROR_CODE();
        sort * ty =  mk_c(c)->sutil().str.mk_seq(to_sort(domain));
        mk_c(c)->save_ast_trail(ty);
        RETURN_Z3(of_sort(ty));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_mk_re_sort(Z3_context c, Z3_sort domain) {
        Z3_TRY;
        LOG_Z3_mk_re_sort(c, domain);
        RESET_ERROR_CODE();
        sort * ty =  mk_c(c)->sutil().re.mk_re(to_sort(domain));
        mk_c(c)->save_ast_trail(ty);
        RETURN_Z3(of_sort(ty));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_string(Z3_context c, Z3_string str) {
        Z3_TRY;
        LOG_Z3_mk_string(c, str);
        RESET_ERROR_CODE();
        zstring s(str);
        app* a = mk_c(c)->sutil().str.mk_string(s);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_ast Z3_API Z3_mk_lstring(Z3_context c, unsigned sz, Z3_string str) {
        Z3_TRY;
        LOG_Z3_mk_string(c, str);
        RESET_ERROR_CODE();
        unsigned_vector chs;
        for (unsigned i = 0; i < sz; ++i) chs.push_back((unsigned char)str[i]);
        zstring s(sz, chs.data());
        app* a = mk_c(c)->sutil().str.mk_string(s);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_mk_string_sort(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_string_sort(c);
        RESET_ERROR_CODE();
        sort* ty = mk_c(c)->sutil().str.mk_string_sort();
        mk_c(c)->save_ast_trail(ty);
        RETURN_Z3(of_sort(ty));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_is_seq_sort(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_is_seq_sort(c, s);
        RESET_ERROR_CODE();
        return mk_c(c)->sutil().is_seq(to_sort(s));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_is_re_sort(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_is_re_sort(c, s);
        RESET_ERROR_CODE();
        return mk_c(c)->sutil().is_re(to_sort(s));
        Z3_CATCH_RETURN(false);
    }

    Z3_sort Z3_API Z3_get_seq_sort_basis(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_get_seq_sort_basis(c, s);
        RESET_ERROR_CODE();
        sort* r = nullptr;
        if (!mk_c(c)->sutil().is_seq(to_sort(s), r)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "expected sequence sort");
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_sort(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_get_re_sort_basis(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_get_re_sort_basis(c, s);
        RESET_ERROR_CODE();
        sort* r = nullptr;
        if (!mk_c(c)->sutil().is_re(to_sort(s), r)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "expected regex sort");
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_sort(r));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_is_string_sort(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_is_string_sort(c, s);
        RESET_ERROR_CODE();
        return mk_c(c)->sutil().is_string(to_sort(s));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_is_string(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_is_string(c, s);
        RESET_ERROR_CODE();
        return mk_c(c)->sutil().str.is_string(to_expr(s));
        Z3_CATCH_RETURN(false);
    }

    Z3_string Z3_API Z3_get_string(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_get_string(c, s);
        RESET_ERROR_CODE();
        zstring str;
        if (!mk_c(c)->sutil().str.is_string(to_expr(s), str)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "expression is not a string literal");
            return "";
        }
        return mk_c(c)->mk_external_string(str.encode());
        Z3_CATCH_RETURN("");
    }

    Z3_char_ptr Z3_API Z3_get_lstring(Z3_context c, Z3_ast s, unsigned* length) {
        Z3_TRY;
        LOG_Z3_get_lstring(c, s, length);
        RESET_ERROR_CODE();
        zstring str;
        if (!length) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "length argument is null");
            return "";
        }
        if (!mk_c(c)->sutil().str.is_string(to_expr(s), str)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "expression is not a string literal");
            return "";
        }
        auto& buffer = mk_c(c)->m_char_buffer;
        buffer.reset();
        svector<char> buff;
        for (unsigned i = 0; i < str.length(); ++i) {
            unsigned ch = str[i];
            if (ch >= 256) {
                buff.reset();
                buffer.push_back('\\');
                buffer.push_back('\\');  // possibly replace by native non-escaped version?
                buffer.push_back('u');
                buffer.push_back('{');
                while (ch > 0) {
                    buff.push_back('0' + (ch & 0xF));
                    ch /= 16;
                }
                for (unsigned j = buff.size(); j-- > 0; ) {
                    buffer.push_back(buff[j]);
                }
                buffer.push_back('}');
            }
            else {
                buffer.push_back((char)ch);
            }
        }
        *length = buffer.size();
        return buffer.data();
        Z3_CATCH_RETURN("");
    }

#define MK_SORTED(NAME, FN )                                    \
    Z3_ast Z3_API NAME(Z3_context c, Z3_sort s) {               \
    Z3_TRY;                                                     \
    LOG_ ## NAME(c, s);                                         \
    RESET_ERROR_CODE();                                         \
    app* a = FN(to_sort(s));                                    \
    mk_c(c)->save_ast_trail(a);                                 \
    RETURN_Z3(of_ast(a));                                       \
    Z3_CATCH_RETURN(0);                                         \
    }

    MK_SORTED(Z3_mk_seq_empty, mk_c(c)->sutil().str.mk_empty);

    MK_UNARY(Z3_mk_seq_unit, mk_c(c)->get_seq_fid(), OP_SEQ_UNIT, SKIP);
    MK_NARY(Z3_mk_seq_concat, mk_c(c)->get_seq_fid(), OP_SEQ_CONCAT, SKIP);
    MK_BINARY(Z3_mk_seq_prefix, mk_c(c)->get_seq_fid(), OP_SEQ_PREFIX, SKIP);
    MK_BINARY(Z3_mk_seq_suffix, mk_c(c)->get_seq_fid(), OP_SEQ_SUFFIX, SKIP);
    MK_BINARY(Z3_mk_seq_contains, mk_c(c)->get_seq_fid(), OP_SEQ_CONTAINS, SKIP);
    MK_BINARY(Z3_mk_str_lt, mk_c(c)->get_seq_fid(), OP_STRING_LT, SKIP);
    MK_BINARY(Z3_mk_str_le, mk_c(c)->get_seq_fid(), OP_STRING_LE, SKIP);

    MK_TERNARY(Z3_mk_seq_extract, mk_c(c)->get_seq_fid(), OP_SEQ_EXTRACT, SKIP);
    MK_TERNARY(Z3_mk_seq_replace, mk_c(c)->get_seq_fid(), OP_SEQ_REPLACE, SKIP);
    MK_BINARY(Z3_mk_seq_at, mk_c(c)->get_seq_fid(), OP_SEQ_AT, SKIP);
    MK_BINARY(Z3_mk_seq_nth, mk_c(c)->get_seq_fid(), OP_SEQ_NTH, SKIP);
    MK_UNARY(Z3_mk_seq_length, mk_c(c)->get_seq_fid(), OP_SEQ_LENGTH, SKIP);
    MK_TERNARY(Z3_mk_seq_index, mk_c(c)->get_seq_fid(), OP_SEQ_INDEX, SKIP);
    MK_BINARY(Z3_mk_seq_last_index, mk_c(c)->get_seq_fid(), OP_SEQ_LAST_INDEX, SKIP);
    MK_UNARY(Z3_mk_seq_to_re, mk_c(c)->get_seq_fid(), OP_SEQ_TO_RE, SKIP);
    MK_BINARY(Z3_mk_seq_in_re, mk_c(c)->get_seq_fid(), OP_SEQ_IN_RE, SKIP);

    MK_UNARY(Z3_mk_int_to_str, mk_c(c)->get_seq_fid(), OP_STRING_ITOS, SKIP);
    MK_UNARY(Z3_mk_str_to_int, mk_c(c)->get_seq_fid(), OP_STRING_STOI, SKIP);


    Z3_ast Z3_API Z3_mk_re_loop(Z3_context c, Z3_ast r, unsigned lo, unsigned hi) {
        Z3_TRY;
        LOG_Z3_mk_re_loop(c, r, lo, hi);
        RESET_ERROR_CODE();
        app* a = hi == 0 ? mk_c(c)->sutil().re.mk_loop(to_expr(r), lo) : mk_c(c)->sutil().re.mk_loop(to_expr(r), lo, hi);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    MK_UNARY(Z3_mk_re_plus, mk_c(c)->get_seq_fid(), OP_RE_PLUS, SKIP);
    MK_UNARY(Z3_mk_re_star, mk_c(c)->get_seq_fid(), OP_RE_STAR, SKIP);
    MK_UNARY(Z3_mk_re_option, mk_c(c)->get_seq_fid(), OP_RE_OPTION, SKIP);
    MK_UNARY(Z3_mk_re_complement, mk_c(c)->get_seq_fid(), OP_RE_COMPLEMENT, SKIP);
    MK_NARY(Z3_mk_re_union, mk_c(c)->get_seq_fid(), OP_RE_UNION, SKIP);
    MK_NARY(Z3_mk_re_intersect, mk_c(c)->get_seq_fid(), OP_RE_INTERSECT, SKIP);
    MK_NARY(Z3_mk_re_concat, mk_c(c)->get_seq_fid(), OP_RE_CONCAT, SKIP);
    MK_BINARY(Z3_mk_re_range, mk_c(c)->get_seq_fid(), OP_RE_RANGE, SKIP);

    MK_SORTED(Z3_mk_re_empty, mk_c(c)->sutil().re.mk_empty);
    MK_SORTED(Z3_mk_re_full, mk_c(c)->sutil().re.mk_full_seq);



};
