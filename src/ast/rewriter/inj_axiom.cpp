/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inj_axiom.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-23.

Revision History:

--*/
#include "ast/rewriter/inj_axiom.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/has_free_vars.h"
#include "ast/well_sorted.h"

/**
   \brief Little HACK for simplifying injectivity axioms
   
   \remark It is not covering all possible cases.
*/
bool simplify_inj_axiom(ast_manager & m, quantifier * q, expr_ref & result) {
    expr * n = q->get_expr();
    expr* arg1 = nullptr, * arg2 = nullptr, *narg = nullptr;
    expr* app1 = nullptr, * app2 = nullptr;
    expr* var1 = nullptr, * var2 = nullptr;
    if (is_forall(q) && m.is_or(n, arg1, arg2)) {
        if (m.is_not(arg2)) 
            std::swap(arg1, arg2);
        if (m.is_not(arg1, narg) && 
            m.is_eq(narg, app1, app2) && 
            m.is_eq(arg2, var1, var2)) {
            if (is_app(app1) &&
                is_app(app2) && 
                to_app(app1)->get_decl() == to_app(app2)->get_decl() &&
                to_app(app1)->get_num_args() == to_app(app2)->get_num_args() &&
                to_app(app1)->get_family_id() == null_family_id &&
                to_app(app1)->get_num_args() > 0 &&
                is_var(var1) && 
                is_var(var2) && 
                var1 != var2) {
                app * f1          = to_app(app1);
                app * f2          = to_app(app2);
                bool found_vars   = false;
                unsigned num      = f1->get_num_args();
                unsigned idx      = UINT_MAX;
                unsigned num_vars = 1;
                for (unsigned i = 0; i < num; i++) {
                    expr  * c1 = f1->get_arg(i);
                    expr  * c2 = f2->get_arg(i);
                    if (!is_var(c1) && !is_uninterp_const(c1))
                        return false;
                    if ((c1 == var1 && c2 == var2) || (c1 == var2 && c2 == var1)) {
                        if (found_vars)
                            return false;
                        found_vars = true;
                        idx = i;
                    }
                    else if (c1 == c2 && c1 != var1 && c1 != var2) {
                        if (is_var(c1)) {
                            ++num_vars;
                        }
                    }
                    else {
                        return false;
                    }
                }
                if (found_vars && !has_free_vars(q)) {
                    TRACE("inj_axiom", 
                          tout << "Cadidate for simplification:\n" << mk_ll_pp(q, m) << mk_pp(app1, m) << "\n" << mk_pp(app2, m) << "\n" <<
                          mk_pp(var1, m) << "\n" << mk_pp(var2, m) << "\nnum_vars: " << num_vars << "\n";);
                    // Building new (optimized) axiom
                    func_decl * decl      = f1->get_decl();
                    unsigned var_idx      = 0;
                    ptr_buffer<expr> f_args, inv_vars;
                    ptr_buffer<sort> decls;
                    buffer<symbol>   names;
                    
                    expr * var            = nullptr;
                    for (unsigned i = 0; i < num; i++) {
                        expr * c = f1->get_arg(i);
                        if (is_var(c)) {
                            names.push_back(symbol(i));
                            sort * s = decl->get_domain(i);
                            decls.push_back(s);
                            expr * new_c = m.mk_var(var_idx, s);
                            var_idx++;
                            f_args.push_back(new_c);
                            if (i == idx) {
                                var = new_c;
                            }
                            else {
                                inv_vars.push_back(new_c);
                            }
                        }
                        else {
                            SASSERT(is_uninterp_const(c));
                            f_args.push_back(c);
                        }
                    }
                    SASSERT(var != 0);
                    app * f    = m.mk_app(decl, f_args.size(), f_args.data());

                    ptr_vector<sort>  domain;
                    inv_vars.push_back(f);
                    for (unsigned i = 0; i < inv_vars.size(); ++i) {
                        domain.push_back(inv_vars[i]->get_sort());
                    }
                    sort * d              = decl->get_domain(idx);
                    func_decl * inv_decl  = m.mk_fresh_func_decl("inj", domain.size(), domain.data(), d);
                    
                    expr * proj = m.mk_app(inv_decl, inv_vars.size(), inv_vars.data());
                    expr * eq   = m.mk_eq(proj, var);
                    expr * p    = m.mk_pattern(f);
                    
                    // decls are in the wrong order...
                    // Remark: the sort of the var 0 must be in the last position.
                    std::reverse(decls.begin(), decls.end());
                    
                    result = m.mk_forall(decls.size(), decls.data(), names.data(), eq,
                                         0, symbol(), symbol(), 1, &p);
                    TRACE("inj_axiom", tout << "new axiom:\n" << mk_pp(result, m) << "\n";);
                    SASSERT(is_well_sorted(m, result));
                    return true;
                }
            }
        }
    }
    return false;
}

