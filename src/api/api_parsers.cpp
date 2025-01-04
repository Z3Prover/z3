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
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "api/api_ast_vector.h"
#include "cmd_context/cmd_context.h"
#include "smt/smt_solver.h"
#include "smt/smt2_extra_cmds.h"
#include "parsers/smt2/smt2parser.h"
#include "solver/solver_na2as.h"
#include "muz/fp/dl_cmds.h"
#include "opt/opt_cmds.h"
#include "cmd_context/extra_cmds/proof_cmds.h"



extern "C" {

    // ---------------
    // Support for SMTLIB2

    struct Z3_parser_context_ref : public api::object {
        scoped_ptr<cmd_context> ctx;

        Z3_parser_context_ref(api::context& c): api::object(c) {
            ast_manager& m = c.m();
            ctx = alloc(cmd_context, false, &(m));
            install_dl_cmds(*ctx.get());
            install_proof_cmds(*ctx.get());
            install_opt_cmds(*ctx.get());
            install_smt2_extra_cmds(*ctx.get());            
            ctx->register_plist();
            ctx->set_ignore_check(true);
        }
    };

    inline Z3_parser_context_ref * to_parser_context(Z3_parser_context pc) { return reinterpret_cast<Z3_parser_context_ref*>(pc); }
    inline Z3_parser_context of_parser_context(Z3_parser_context_ref* pc) { return reinterpret_cast<Z3_parser_context>(pc); }    

    Z3_parser_context Z3_API Z3_mk_parser_context(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_parser_context(c);
        RESET_ERROR_CODE();
        Z3_parser_context_ref * pc = alloc(Z3_parser_context_ref, *mk_c(c));
        mk_c(c)->save_object(pc);
        Z3_parser_context r = of_parser_context(pc);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_parser_context_inc_ref(Z3_context c, Z3_parser_context pc) {
        Z3_TRY;
        LOG_Z3_parser_context_inc_ref(c, pc);
        RESET_ERROR_CODE();
        to_parser_context(pc)->inc_ref();
        Z3_CATCH;   
    }

    void Z3_API Z3_parser_context_dec_ref(Z3_context c, Z3_parser_context pc) {
        Z3_TRY;
        LOG_Z3_parser_context_dec_ref(c, pc);
        RESET_ERROR_CODE();
        to_parser_context(pc)->dec_ref();
        Z3_CATCH;   
    }

    static void insert_datatype(ast_manager& m, scoped_ptr<cmd_context>& ctx, sort* srt) {
        datatype_util dt(m);
        if (!dt.is_datatype(srt)) 
            return;

        for (func_decl * c : *dt.get_datatype_constructors(srt)) {
            ctx->insert(c->get_name(), c);
            func_decl * r = dt.get_constructor_recognizer(c);
            ctx->insert(r->get_name(), r);
            for (func_decl * a : *dt.get_constructor_accessors(c)) {
                ctx->insert(a->get_name(), a);
            }
        }            
    }

    static void insert_sort(ast_manager& m, scoped_ptr<cmd_context>& ctx, symbol const& name, sort* srt) {
        if (ctx->find_psort_decl(name)) 
            return;
        psort* ps = ctx->pm().mk_psort_cnst(srt);
        ctx->insert(ctx->pm().mk_psort_user_decl(0, name, ps));        
        insert_datatype(m, ctx, srt);
    }

    void Z3_API Z3_parser_context_add_sort(Z3_context c, Z3_parser_context pc, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_parser_context_add_sort(c, pc, s);
        RESET_ERROR_CODE();
        auto& ctx = to_parser_context(pc)->ctx;
        sort* srt = to_sort(s);
        symbol name = srt->get_name();
        insert_sort(mk_c(c)->m(), ctx, name, srt);
        Z3_CATCH;
    }

    void Z3_API Z3_parser_context_add_decl(Z3_context c, Z3_parser_context pc, Z3_func_decl f) {
        Z3_TRY;
        LOG_Z3_parser_context_add_decl(c, pc, f);
        RESET_ERROR_CODE();
        auto& ctx = *to_parser_context(pc)->ctx;
        func_decl* fn = to_func_decl(f);
        symbol name = fn->get_name();
        ctx.insert(name, fn);
        Z3_CATCH;
    }

    static Z3_ast_vector Z3_parser_context_parse_stream(Z3_context c, scoped_ptr<cmd_context>& ctx, bool owned, std::istream& is) {
        Z3_TRY;
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), m);        
        mk_c(c)->save_object(v);        
        std::stringstream errstrm;
        ctx->set_regular_stream(errstrm);
        try {
            if (!parse_smt2_commands(*ctx, is)) {
                if (owned)
                    ctx = nullptr;
                SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str());
                return of_ast_vector(v);
            }
        }
        catch (z3_exception& e) {
            if (owned)
                ctx = nullptr;
            errstrm << e.what();
            SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str());
            return of_ast_vector(v);
        }
        for (auto const& [asr, an] : ctx->tracked_assertions())
            if (an)
                v->m_ast_vector.push_back(m.mk_implies(an, asr));
            else
                v->m_ast_vector.push_back(asr);
        ctx->reset_tracked_assertions();        
        return of_ast_vector(v);
        Z3_CATCH_RETURN(nullptr);        
    }

    Z3_ast_vector Z3_API Z3_parser_context_from_string(Z3_context c, Z3_parser_context pc, Z3_string str) {
        Z3_TRY;
        LOG_Z3_parser_context_from_string(c, pc, str);
        std::istringstream is(str);
        auto& ctx = to_parser_context(pc)->ctx;
        Z3_ast_vector r = Z3_parser_context_parse_stream(c, ctx, false, is);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    static
    Z3_ast_vector parse_smtlib2_stream(bool exec, Z3_context c, std::istream& is,
                                       unsigned num_sorts,
                                       Z3_symbol const _sort_names[],
                                       Z3_sort const _sorts[],
                                       unsigned num_decls,
                                       Z3_symbol const decl_names[],
                                       Z3_func_decl const decls[]) {
        Z3_TRY;
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        scoped_ptr<cmd_context> ctx = alloc(cmd_context, false, &(m));
        install_dl_cmds(*ctx.get());
        install_proof_cmds(*ctx.get());
        install_opt_cmds(*ctx.get());
        install_smt2_extra_cmds(*ctx.get());
        ctx->register_plist();
        ctx->set_ignore_check(true);
                    
        for (unsigned i = 0; i < num_decls; ++i) 
            ctx->insert(to_symbol(decl_names[i]), to_func_decl(decls[i]));

        for (unsigned i = 0; i < num_sorts; ++i) 
            insert_sort(m, ctx, to_symbol(_sort_names[i]), to_sort(_sorts[i]));

        return Z3_parser_context_parse_stream(c, ctx, true, is);
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
        std::istringstream is(str);
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
        RESET_ERROR_CODE();
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
        RESET_ERROR_CODE();
        LOG_Z3_eval_smtlib2_string(c, str);
        Z3_TRY;
        if (!mk_c(c)->cmd()) {
            auto* ctx = alloc(cmd_context, false, &(mk_c(c)->m()));
            mk_c(c)->cmd() = ctx;
            install_dl_cmds(*ctx);
            install_proof_cmds(*ctx);
            install_opt_cmds(*ctx);
            install_smt2_extra_cmds(*ctx);
            ctx->register_plist();
            ctx->set_solver_factory(mk_smt_strategic_solver_factory());
        }
        scoped_ptr<cmd_context>& ctx = mk_c(c)->cmd();
        std::istringstream is(str);
        ctx->set_regular_stream(ous);
        ctx->set_diagnostic_stream(ous);
        cmd_context::scoped_redirect _redirect(*ctx);
        try {
            // See api::context::m_parser for a motivation about the reuse of the parser
            if (!parse_smt2_commands_with_parser(mk_c(c)->m_parser, *ctx.get(), is)) {
                SET_ERROR_CODE(Z3_PARSER_ERROR, ous.str());
            }
        }
        catch (z3_exception& e) {
            if (ous.str().empty()) ous << e.what();
            SET_ERROR_CODE(Z3_PARSER_ERROR, ous.str());
        }
        Z3_CATCH_CORE({});
        RETURN_Z3(mk_c(c)->mk_external_string(std::move(ous).str()));
    }
}
