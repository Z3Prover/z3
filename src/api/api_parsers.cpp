/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_parsers.cpp

Abstract:
    API for parsing different formats

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "api/api_ast_vector.h"
#include "cmd_context/cmd_context.h"
#include "smt/smt_solver.h"
#include "parsers/smt2/smt2parser.h"
#include "solver/solver_na2as.h"
#include "tactic/portfolio/smt_strategic_solver.h"


extern "C" {


    Z3_string Z3_API Z3_get_parser_error(Z3_context c) {        
        Z3_TRY;
        LOG_Z3_get_parser_error(c);
        RESET_ERROR_CODE(); 
        return mk_c(c)->m_parser_error_buffer.c_str();
        Z3_CATCH_RETURN("");
    }

    // ---------------
    // Support for SMTLIB2

    Z3_ast_vector parse_smtlib2_stream(bool exec, Z3_context c, std::istream& is,
                                unsigned num_sorts,
                                Z3_symbol const sort_names[],
                                Z3_sort const sorts[],
                                unsigned num_decls,
                                Z3_symbol const decl_names[],
                                Z3_func_decl const decls[]) {
        Z3_TRY;
        scoped_ptr<cmd_context> ctx = alloc(cmd_context, false, &(mk_c(c)->m()));
        ctx->set_ignore_check(true);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);        
        for (unsigned i = 0; i < num_decls; ++i) {
            ctx->insert(to_symbol(decl_names[i]), to_func_decl(decls[i]));
        }
        for (unsigned i = 0; i < num_sorts; ++i) {
            sort* srt = to_sort(sorts[i]);
            symbol name(to_symbol(sort_names[i]));
            if (!ctx->find_psort_decl(name)) {
                psort* ps = ctx->pm().mk_psort_cnst(srt);
                ctx->insert(ctx->pm().mk_psort_user_decl(0, name, ps));
            }
        }
        std::stringstream errstrm;
        ctx->set_regular_stream(errstrm);
        try {
            if (!parse_smt2_commands(*ctx.get(), is)) {
                ctx = nullptr;
                mk_c(c)->m_parser_error_buffer = errstrm.str();
                SET_ERROR_CODE(Z3_PARSER_ERROR);
                return of_ast_vector(v);
            }
        }
        catch (z3_exception& e) {
            errstrm << e.msg();
            mk_c(c)->m_parser_error_buffer = errstrm.str();            
            ctx = nullptr;
            SET_ERROR_CODE(Z3_PARSER_ERROR);
            return of_ast_vector(v);
        }
        ptr_vector<expr>::const_iterator it  = ctx->begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx->end_assertions();
        for (; it != end; ++it) {
            v->m_ast_vector.push_back(*it);
        }
        return of_ast_vector(v);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_parse_smtlib2_string(Z3_context c, Z3_string str,
                                          unsigned num_sorts,
                                          Z3_symbol const sort_names[],
                                          Z3_sort const sorts[],
                                          unsigned num_decls,
                                          Z3_symbol const decl_names[],
                                          Z3_func_decl const decls[]) {
        Z3_TRY;
        LOG_Z3_parse_smtlib2_string(c, str, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
        std::string s(str);
        std::istringstream is(s);
        Z3_ast_vector r = parse_smtlib2_stream(false, c, is, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_parse_smtlib2_file(Z3_context c, Z3_string file_name,
                                        unsigned num_sorts,
                                        Z3_symbol const sort_names[],
                                        Z3_sort const sorts[],
                                        unsigned num_decls,
                                        Z3_symbol const decl_names[],
                                        Z3_func_decl const decls[]) {
        Z3_TRY;
        LOG_Z3_parse_smtlib2_string(c, file_name, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
        std::ifstream is(file_name);
        if (!is) {
            SET_ERROR_CODE(Z3_FILE_ACCESS_ERROR);
            return nullptr;
        }
        Z3_ast_vector r = parse_smtlib2_stream(false, c, is, num_sorts, sort_names, sorts, num_decls, decl_names, decls);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_eval_smtlib2_string(Z3_context c, Z3_string str) {
        std::stringstream ous;
        Z3_TRY;
        LOG_Z3_eval_smtlib2_string(c, str);
        if (!mk_c(c)->cmd()) {
            mk_c(c)->cmd() = alloc(cmd_context, false, &(mk_c(c)->m()));
            mk_c(c)->cmd()->set_solver_factory(mk_smt_strategic_solver_factory());
        }
        scoped_ptr<cmd_context>& ctx = mk_c(c)->cmd();
        std::string s(str);
        std::istringstream is(s);
        ctx->set_regular_stream(ous);
        ctx->set_diagnostic_stream(ous);
        try {
            if (!parse_smt2_commands(*ctx.get(), is)) {
                mk_c(c)->m_parser_error_buffer = ous.str();
                SET_ERROR_CODE(Z3_PARSER_ERROR);
                RETURN_Z3(mk_c(c)->mk_external_string(ous.str()));
            }
        }
        catch (z3_exception& e) {
            if (ous.str().empty()) ous << e.msg();
            mk_c(c)->m_parser_error_buffer = ous.str();
            SET_ERROR_CODE(Z3_PARSER_ERROR);
            RETURN_Z3(mk_c(c)->mk_external_string(ous.str()));
        }
        RETURN_Z3(mk_c(c)->mk_external_string(ous.str()));
        Z3_CATCH_RETURN(mk_c(c)->mk_external_string(ous.str()));
    }
};
