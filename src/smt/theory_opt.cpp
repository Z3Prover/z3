/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_opt.cpp

Abstract:

    Interface utilities used by optimization providing 
    theory solvers.

Author:

    Nikolaj Bjorner (nbjorner) 2013-10-18

Notes:

--*/

#include "ast/arith_decl_plugin.h"
#include "smt/smt_types.h"
#include "smt/smt_theory.h"
#include "smt/theory_opt.h"

namespace smt {
    bool theory_opt::is_linear(ast_manager& m, expr* term) {
        arith_util a(m);
        ptr_vector<expr> todo;
        ast_mark mark;
        todo.push_back(term);
        expr* t1, *t2;
        while (!todo.empty()) {
            term = todo.back();
            todo.pop_back();
            if (mark.is_marked(term)) {
                continue;
            }
            mark.mark(term, true);
            if (!is_app(term)) {
                return false;
            }
            app* t = to_app(term);
            if (t->get_family_id() != a.get_family_id()) {
                // done
            }
            else if (a.is_add(t) || a.is_to_real(t) || a.is_to_int(t) ||
                a.is_uminus(t) || a.is_numeral(t) || a.is_sub(t)) {
                todo.append(t->get_num_args(), t->get_args());
            }
            else if (a.is_mul(t, t1, t2)) {
                if (is_numeral(a, t1)) {
                    todo.push_back(t2);
                }
                else if (is_numeral(a, t2)) {
                    todo.push_back(t1);
                }
                else {
                    return false;
                }
            }
            else {
                return false;
            } 
        }
        return true;
    }

    
    bool theory_opt::is_numeral(arith_util& a, expr* term) {
        while (a.is_uminus(term) || a.is_to_real(term) || a.is_to_int(term)) {
            term = to_app(term)->get_arg(0);
        }
        return a.is_numeral(term);
    }

};
