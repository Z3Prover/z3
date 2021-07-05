/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    pull_quant.cpp

Abstract:

    Pull nested quantifiers.

Author:

    Leonardo (leonardo) 2008-01-20

Notes:

--*/
#include "ast/normal_forms/pull_quant.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"

struct pull_quant::imp {
    
    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;
        shift_vars    m_shift;
        
        rw_cfg(ast_manager & m):
            m(m), 
            m_shift(m) {
        }

        bool pull_quant1_core(func_decl * d, unsigned num_children, expr * const * children, expr_ref & result) {
            ptr_buffer<sort>  var_sorts;
            buffer<symbol>    var_names;
            symbol            qid;
            int               w = INT_MAX;
            
            // The input formula is in Skolem normal form...
            // So all children are forall (positive context) or exists (negative context).
            // Remark: (AND a1 ...) may be represented (NOT (OR (NOT a1) ...)))
            // So, when pulling a quantifier over a NOT, it becomes an exists.
            
            if (m.is_not(d)) {
                SASSERT(num_children == 1);
                expr * child = children[0];
                if (is_quantifier(child) && (is_forall(child) || is_exists(child))) {
                    quantifier * q = to_quantifier(child);
                    expr * body = q->get_expr();
                    quantifier_kind k = q->get_kind() == forall_k ? exists_k : forall_k;
                    result = m.update_quantifier(q, k, m.mk_not(body));
                    return true;
                }
                else {
                    return false;
                }
            }
            
            bool found_quantifier = false;
            bool forall_children = false;
            
            for (unsigned i = 0; i < num_children; i++) {
                expr * child = children[i];
                if (is_quantifier(child) && !is_lambda(child)) {
                    
                    if (!found_quantifier && (is_forall(child) || is_exists(child))) {
                        found_quantifier = true;
                        forall_children = is_forall(child);
                    }
                    else if (forall_children != is_forall(child))
                        return false;
                    
                    quantifier * nested_q = to_quantifier(child);
                    if (var_sorts.empty()) {
                        // use the qid of one of the nested quantifiers.
                        qid = nested_q->get_qid();
                    }
                    w = std::min(w, nested_q->get_weight());
                    unsigned j = nested_q->get_num_decls();
                    while (j > 0) {
                        --j;
                        var_sorts.push_back(nested_q->get_decl_sort(j));
                        symbol s = nested_q->get_decl_name(j);
                        if (std::find(var_names.begin(), var_names.end(), s) != var_names.end())
                            var_names.push_back(m.mk_fresh_var_name(s.is_numerical() ? nullptr : s.bare_str()));
                        else
                            var_names.push_back(s);
                    }
                }
            }
            
            if (!var_sorts.empty()) {
                SASSERT(found_quantifier);
                // adjust the variable ids in formulas in new_children
                expr_ref_buffer   new_adjusted_children(m);
                expr_ref          adjusted_child(m);
                unsigned          num_decls = var_sorts.size();
                unsigned          shift_amount = 0;
                TRACE("pull_quant", tout << "Result num decls:" << num_decls << "\n";);
                for (unsigned i = 0; i < num_children; i++) {
                    expr * child = children[i];
                    if (!is_quantifier(child)) {
                        // increment the free variables in child by num_decls because
                        // child will be in the scope of num_decls bound variables.
                        m_shift(child, num_decls, adjusted_child);
                        TRACE("pull_quant", tout << "shifted by: " << num_decls << "\n" << 
                              mk_pp(child, m) << "\n---->\n" << mk_pp(adjusted_child, m) << "\n";);
                    }
                    else {
                        quantifier * nested_q = to_quantifier(child);
                        SASSERT(num_decls >= nested_q->get_num_decls());
                        // Assume nested_q is of the form 
                        // forall xs. P(xs, ys)
                        // where xs (ys) represents the set of bound (free) variables.
                        //
                        // - the index of the variables xs must be increased by shift_amount.
                        //   That is, the number of new bound variables that will precede the bound
                        //   variables xs.
                        //
                        // - the index of the variables ys must be increased by num_decls - nested_q->get_num_decls. 
                        //   That is, the total number of new bound variables that will be in the scope
                        //   of nested_q->get_expr().
                        m_shift(nested_q->get_expr(), 
                                nested_q->get_num_decls(),             // bound for shift1/shift2
                                num_decls - nested_q->get_num_decls(), // shift1  (shift by this amount if var idx >= bound)
                                shift_amount,                          // shift2  (shift by this amount if var idx < bound)
                                adjusted_child);
                        TRACE("pull_quant", tout << "shifted  bound: " << nested_q->get_num_decls() << " shift1: " << shift_amount <<
                              " shift2: " << (num_decls - nested_q->get_num_decls()) << "\n" << mk_pp(nested_q->get_expr(), m) << 
                              "\n---->\n" << mk_pp(adjusted_child, m) << "\n";);
                        shift_amount += nested_q->get_num_decls();
                    }
                    new_adjusted_children.push_back(adjusted_child);
                }
                
                // Remark: patterns are ignored.
                // This is ok, since this functor is used in one of the following cases:
                //
                // 1) Superposition calculus is being used, so the
                // patterns are useless.
                //
                // 2) No patterns were provided, and the functor is used
                // to increase the effectiveness of the pattern inference
                // procedure.
                //
                // 3) MBQI 
                std::reverse(var_sorts.begin(), var_sorts.end());
                std::reverse(var_names.begin(), var_names.end());
                result = m.mk_quantifier(forall_children ? forall_k : exists_k,
                                                 var_sorts.size(),
                                                 var_sorts.data(),
                                                 var_names.data(),
                                                 m.mk_app(d, new_adjusted_children.size(), new_adjusted_children.data()),
                                                 w,
                                                 qid);
                return true;
            }
            else {
                SASSERT(!found_quantifier);
                return false;
            }
        }

        void pull_quant1(func_decl * d, unsigned num_children, expr * const * children, expr_ref & result) {
            if (!pull_quant1_core(d, num_children, children, result)) {
                result = m.mk_app(d, num_children, children);
            }
        }


        void pull_quant1_core(quantifier * q, expr * new_expr, expr_ref & result) {
            // The original formula was in SNF, so the original quantifiers must be universal.
            SASSERT(is_forall(q));
            SASSERT(is_forall(new_expr));
            quantifier * nested_q = to_quantifier(new_expr);
            ptr_buffer<sort> var_sorts;
            buffer<symbol>   var_names;
            var_sorts.append(q->get_num_decls(), const_cast<sort**>(q->get_decl_sorts()));
            var_sorts.append(nested_q->get_num_decls(), const_cast<sort**>(nested_q->get_decl_sorts()));
            var_names.append(q->get_num_decls(), const_cast<symbol*>(q->get_decl_names()));
            var_names.append(nested_q->get_num_decls(), const_cast<symbol*>(nested_q->get_decl_names()));
            // Remark: patterns are ignored.
            // See comment in reduce1_app
            result = m.mk_forall(var_sorts.size(),
				 var_sorts.data(),
				 var_names.data(),
				 nested_q->get_expr(),
				 std::min(q->get_weight(), nested_q->get_weight()),
				 m.is_lambda_def(q) ? symbol("pulled-lambda") : q->get_qid());
        }

        void pull_quant1(quantifier * q, expr * new_expr, expr_ref & result) {
            // The original formula was in SNF, so the original quantifiers must be universal.
            SASSERT(is_forall(q));
            if (is_forall(new_expr)) { 
                pull_quant1_core(q, new_expr, result);
            }
            else {
                SASSERT(!is_quantifier(new_expr));
                result = m.update_quantifier(q, new_expr);
            }
        }

        void pull_quant1(expr * n, expr_ref & result) {
            if (is_app(n))
                pull_quant1(to_app(n)->get_decl(), to_app(n)->get_num_args(), to_app(n)->get_args(), result);
            else if (is_quantifier(n))
                pull_quant1(to_quantifier(n), to_quantifier(n)->get_expr(), result);
            else
                result = n;
        }
        
        // Code for proof generation...
        void pull_quant2(expr * n, expr_ref & r, proof_ref & pr) {
            pr = nullptr;
            if (is_app(n)) {
                expr_ref_buffer   new_args(m);
                expr_ref          new_arg(m);
                ptr_buffer<proof> proofs;
                for (expr * arg : *to_app(n)) {
                    pull_quant1(arg , new_arg);
                    new_args.push_back(new_arg);
                    if (new_arg != arg)
                        proofs.push_back(m.mk_pull_quant(arg, to_quantifier(new_arg)));
                }
                pull_quant1(to_app(n)->get_decl(), new_args.size(), new_args.data(), r);
                if (m.proofs_enabled()) {
                    app   * r1 = m.mk_app(to_app(n)->get_decl(), new_args.size(), new_args.data());
                    proof * p1 = proofs.empty() ? nullptr : m.mk_congruence(to_app(n), r1, proofs.size(), proofs.data());
                    proof * p2 = r1 == r ? nullptr : m.mk_pull_quant(r1, to_quantifier(r));
                    pr = m.mk_transitivity(p1, p2);
                }
            }
            else if (is_quantifier(n)) {
                expr_ref new_expr(m);
                pull_quant1(to_quantifier(n)->get_expr(), new_expr);
                pull_quant1(to_quantifier(n), new_expr, r);
                if (m.proofs_enabled()) {
                    quantifier * q1 = m.update_quantifier(to_quantifier(n), new_expr);
                    proof * p1 = nullptr;
                    if (n != q1) {
                        proof * p0 = m.mk_pull_quant(n, to_quantifier(new_expr));
                        p1 = m.mk_quant_intro(to_quantifier(n), q1, p0);
                    }
                    proof * p2 = q1 == r ? nullptr : m.mk_pull_quant(q1, to_quantifier(r));
                    pr = m.mk_transitivity(p1, p2);
                }
            }
            else {
                r  = n;
            }
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if (!m.is_or(f) && !m.is_and(f) && !m.is_not(f))
                return BR_FAILED;

            if (!pull_quant1_core(f, num, args, result))
                return BR_FAILED;

            if (m.proofs_enabled()) {
                result_pr = m.mk_pull_quant(m.mk_app(f, num, args), 
                                                    to_quantifier(result.get()));
            }
            return BR_DONE;
        }

        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {

            if (is_exists(old_q)) {
                result = m.mk_not(new_body);
                result = m.mk_not(m.update_quantifier(old_q, forall_k, result));
                if (m.proofs_enabled()) 
                    m.mk_rewrite(old_q, result);
                return true;
            }
            if (is_lambda(old_q)) {
                return false;
            }

            if (!is_forall(new_body))
                return false;

            pull_quant1_core(old_q, new_body, result);
            if (m.proofs_enabled())
                result_pr = m.mk_pull_quant(old_q, to_quantifier(result.get()));
            return true;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m) {
        }
    };
    
    rw m_rw;

    imp(ast_manager & m):
        m_rw(m) {
    }
    
    void operator()(expr * n, expr_ref & r, proof_ref & p) {
        m_rw(n, r, p);
    }
};

pull_quant::pull_quant(ast_manager & m) {
    m_imp = alloc(imp, m);
}

pull_quant::~pull_quant() {
    dealloc(m_imp);
}

void pull_quant::operator()(expr * n, expr_ref & r, proof_ref & p) {
    (*m_imp)(n, r, p);
}

void pull_quant::reset() {
    m_imp->m_rw.reset();
}

void pull_quant::pull_quant2(expr * n, expr_ref & r, proof_ref & pr) {
    m_imp->m_rw.cfg().pull_quant2(n, r, pr);
}

struct pull_nested_quant::imp {
    
    struct rw_cfg : public default_rewriter_cfg {
        pull_quant m_pull;
        expr_ref   m_r;
        proof_ref  m_pr;

        rw_cfg(ast_manager & m):m_pull(m), m_r(m), m_pr(m) {}
        
        bool get_subst(expr * s, expr * & t, proof * & t_pr) { 
            if (!is_quantifier(s))
                return false;
            m_pull(to_quantifier(s), m_r, m_pr);
            t    = m_r.get();
            t_pr = m_pr.get();
            return true;
        }
    };
    
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager & m):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m) {
        }
    };
    
    rw m_rw;

    imp(ast_manager & m):
        m_rw(m) {
    }
    
    void operator()(expr * n, expr_ref & r, proof_ref & p) {
        m_rw(n, r, p);
    }
};

pull_nested_quant::pull_nested_quant(ast_manager & m) {
    m_imp = alloc(imp, m);
}

pull_nested_quant::~pull_nested_quant() {
    dealloc(m_imp);
}

void pull_nested_quant::operator()(expr * n, expr_ref & r, proof_ref & p) {
    (*m_imp)(n, r, p);
}

void pull_nested_quant::reset() {
    m_imp->m_rw.reset();
}


