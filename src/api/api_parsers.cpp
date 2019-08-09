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


extern "C" {

    // ---------------
    // Support for SMTLIB2

    Z3_ast_vector parse_smtlib2_stream(bool exec, Z3_context c, std::istream& is,
                                       unsigned num_sorts,
                                       Z3_symbol const _sort_names[],
                                       Z3_sort const _sorts[],
                                       unsigned num_decls,
                                       Z3_symbol const decl_names[],
                                       Z3_func_decl const decls[]) {
        Z3_TRY;
        ast_manager& m = mk_c(c)->m();
        scoped_ptr<cmd_context> ctx = alloc(cmd_context, false, &(m));
        ctx->set_ignore_check(true);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        
        vector<symbol> sort_names;
        ptr_vector<sort> sorts;
        for (unsigned i = 0; i < num_sorts; ++i) {
            sorts.push_back(to_sort(_sorts[i]));
            sort_names.push_back(to_symbol(_sort_names[i]));
        }
                    
        mk_c(c)->save_object(v);        
        for (unsigned i = 0; i < num_decls; ++i) {
            func_decl* d = to_func_decl(decls[i]);
            ctx->insert(to_symbol(decl_names[i]), d);
            sort_names.push_back(d->get_range()->get_name());
            sorts.push_back(d->get_range());
            for (sort* s : *d) {
                sort_names.push_back(s->get_name());
                sorts.push_back(s);
            }
        }
        datatype_util dt(m);
        for (unsigned i = 0; i < num_sorts; ++i) {
            sort* srt = sorts[i];
            symbol name = sort_names[i];
            if (ctx->find_psort_decl(name)) {
                continue;
            }
            psort* ps = ctx->pm().mk_psort_cnst(srt);
            ctx->insert(ctx->pm().mk_psort_user_decl(0, name, ps));
            if (!dt.is_datatype(srt)) {
                continue;
            }

            for (func_decl * c : *dt.get_datatype_constructors(srt)) {
                ctx->insert(c->get_name(), c);
                func_decl * r = dt.get_constructor_recognizer(c);
                ctx->insert(r->get_name(), r);
                for (func_decl * a : *dt.get_constructor_accessors(c)) {
                    ctx->insert(a->get_name(), a);
                }
            }            
        }
        std::stringstream errstrm;
        ctx->set_regular_stream(errstrm);
        try {
            if (!parse_smt2_commands(*ctx.get(), is)) {
                ctx = nullptr;
                SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str().c_str());
                return of_ast_vector(v);
            }
        }
        catch (z3_exception& e) {
            errstrm << e.msg();
            ctx = nullptr;
            SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str().c_str());
            return of_ast_vector(v);
        }
        for (expr * e : ctx->assertions()) {
            v->m_ast_vector.push_back(e);
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
            SET_ERROR_CODE(Z3_FILE_ACCESS_ERROR, nullptr);
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
                SET_ERROR_CODE(Z3_PARSER_ERROR, ous.str().c_str());
                RETURN_Z3(mk_c(c)->mk_external_string(ous.str()));
            }
        }
        catch (z3_exception& e) {
            if (ous.str().empty()) ous << e.msg();
            SET_ERROR_CODE(Z3_PARSER_ERROR, ous.str().c_str());
            RETURN_Z3(mk_c(c)->mk_external_string(ous.str()));
        }
        RETURN_Z3(mk_c(c)->mk_external_string(ous.str()));
        Z3_CATCH_RETURN(mk_c(c)->mk_external_string(ous.str()));
    }
};
