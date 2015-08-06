/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ast_pp_util.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2015-8-6.

Revision History:

--*/
#ifndef AST_PP_UTIL_H_
#define AST_PP_UTIL_H_

#include "decl_collector.h"
#include "ast_smt2_pp.h"
#include "ast_smt_pp.h"

class ast_pp_util {
    ast_manager&        m;
 public:        

    decl_collector      coll;

    ast_pp_util(ast_manager& m): m(m), coll(m, false) {}

    void collect(expr* e) {
        coll.visit(e);
    }

    void collect(unsigned n, expr* const* es) {
        for (unsigned i = 0; i < n; ++i) {
            coll.visit(es[i]);
        }
    }

    void collect(expr_ref_vector const& es) {
        collect(es.size(), es.c_ptr());
    }

    void display_decls(std::ostream& out) {
        smt2_pp_environment_dbg env(m);
        unsigned n = coll.get_num_sorts();
        for (unsigned i = 0; i < n; ++i) {
            ast_smt2_pp(out, coll.get_sorts()[i], env);
        }
        n = coll.get_num_decls();
        for (unsigned i = 0; i < n; ++i) {
            ast_smt2_pp(out, coll.get_func_decls()[i], env);
            out << "\n";
        }
    }

    void display_asserts(std::ostream& out, expr_ref_vector const& fmls, bool neat = true) {
        if (neat) {
            smt2_pp_environment_dbg env(m);
            for (unsigned i = 0; i < fmls.size(); ++i) {
                out << "(assert ";
                ast_smt2_pp(out, fmls[i], env);
                out << ")\n";
            }
        }
        else {
            ast_smt_pp ll_smt2_pp(m);
            for (unsigned i = 0; i < fmls.size(); ++i) {
                out << "(assert ";
                ll_smt2_pp.display_expr_smt2(out, fmls[i]);
                out << ")\n";
            }
        }
    }
};

#endif /* AST_PP_UTIL_H_ */
