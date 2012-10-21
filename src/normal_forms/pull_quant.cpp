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
#include"pull_quant.h"
#include"ast_pp.h"
#include"for_each_expr.h"

void pull_quant::pull_quant1(func_decl * d, unsigned num_children, expr * const * children, expr_ref & result) {
    ptr_buffer<sort>  var_sorts;
    buffer<symbol>    var_names;
    symbol            qid;
    int               w = INT_MAX;

    // The input formula is in Skolem normal form...
    // So all children are forall (positive context) or exists (negative context).
    // Remark: (AND a1 ...) may be represented (NOT (OR (NOT a1) ...)))
    // So, when pulling a quantifier over a NOT, it becomes an exists.
    
    if (m_manager.is_not(d)) {
        SASSERT(num_children == 1);
        expr * child = children[0];
        if (is_quantifier(child)) {
            quantifier * q = to_quantifier(child);
            expr * body = q->get_expr();
            result = m_manager.update_quantifier(q, !q->is_forall(), m_manager.mk_not(body));
        }
        else {
            result = m_manager.mk_not(child);
        }
        return;
    }

    bool found_quantifier = false;
    bool forall_children;

    for (unsigned i = 0; i < num_children; i++) {
        expr * child = children[i];
        if (is_quantifier(child)) {
            
            if (!found_quantifier) {
                found_quantifier = true;
                forall_children  = is_forall(child);
            }
            else {
                // Since the initial formula was in SNF, all children must be EXISTS or FORALL.
                SASSERT(forall_children == is_forall(child));
            }
            
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
                    var_names.push_back(m_manager.mk_fresh_var_name(s.is_numerical() ? 0 : s.bare_str()));
                else
                    var_names.push_back(s);
            }
        }
    }

    if (!var_sorts.empty()) {
        SASSERT(found_quantifier);
        // adjust the variable ids in formulas in new_children
        expr_ref_buffer   new_adjusted_children(m_manager);
        expr_ref          adjusted_child(m_manager);
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
                      mk_pp(child, m_manager) << "\n---->\n" << mk_pp(adjusted_child, m_manager) << "\n";);
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
                        num_decls - nested_q->get_num_decls(), // shift1  (shift by this ammount if var idx >= bound)
                        shift_amount,                          // shift2  (shift by this ammount if var idx < bound)
                        adjusted_child);
                TRACE("pull_quant", tout << "shifted  bound: " << nested_q->get_num_decls() << " shift1: " << shift_amount <<
                      " shift2: " << (num_decls - nested_q->get_num_decls()) << "\n" << mk_pp(nested_q->get_expr(), m_manager) << 
                      "\n---->\n" << mk_pp(adjusted_child, m_manager) << "\n";);
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
        result = m_manager.mk_quantifier(forall_children,
                                         var_sorts.size(),
                                         var_sorts.c_ptr(),
                                         var_names.c_ptr(),
                                         m_manager.mk_app(d, new_adjusted_children.size(), new_adjusted_children.c_ptr()),
                                         w,
                                         qid);
    }
    else {
        SASSERT(!found_quantifier);
        result = m_manager.mk_app(d, num_children, children);
    }
}

void pull_quant::pull_quant1(quantifier * q, expr * new_expr, expr_ref & result) {
    // The original formula was in SNF, so the original quantifiers must be universal.
    SASSERT(is_forall(q));
    if (is_forall(new_expr)) { 
        quantifier * nested_q = to_quantifier(new_expr);
        ptr_buffer<sort> var_sorts;
        buffer<symbol>   var_names;
        var_sorts.append(q->get_num_decls(), const_cast<sort**>(q->get_decl_sorts()));
        var_sorts.append(nested_q->get_num_decls(), const_cast<sort**>(nested_q->get_decl_sorts()));
        var_names.append(q->get_num_decls(), const_cast<symbol*>(q->get_decl_names()));
        var_names.append(nested_q->get_num_decls(), const_cast<symbol*>(nested_q->get_decl_names()));
        // Remark: patterns are ignored.
        // See comment in reduce1_app
        result = m_manager.mk_forall(var_sorts.size(),
                                     var_sorts.c_ptr(),
                                     var_names.c_ptr(),
                                     nested_q->get_expr(),
                                     std::min(q->get_weight(), nested_q->get_weight()),
                                     q->get_qid());
    }
    else {
        SASSERT(!is_quantifier(new_expr));
        result = m_manager.update_quantifier(q, new_expr);
    }
}

void pull_quant::pull_quant1(expr * n, expr_ref & result) {
    if (is_app(n))
        pull_quant1(to_app(n)->get_decl(), to_app(n)->get_num_args(), to_app(n)->get_args(), result);
    else if (is_quantifier(n))
        pull_quant1(to_quantifier(n), to_quantifier(n)->get_expr(), result);
    else
        result = n;
}

// Code for proof generation...
void pull_quant::pull_quant2(expr * n, expr_ref & r, proof_ref & pr) {
    pr = 0;
    if (is_app(n)) {
        expr_ref_buffer   new_args(m_manager);
        expr_ref          new_arg(m_manager);
        ptr_buffer<proof> proofs;
        unsigned num = to_app(n)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            expr * arg = to_app(n)->get_arg(i); 
            pull_quant1(arg , new_arg);
            new_args.push_back(new_arg);
            if (new_arg != arg)
                proofs.push_back(m_manager.mk_pull_quant(arg, to_quantifier(new_arg)));
        }
        pull_quant1(to_app(n)->get_decl(), new_args.size(), new_args.c_ptr(), r);
        if (m_manager.fine_grain_proofs()) {
            app   * r1 = m_manager.mk_app(to_app(n)->get_decl(), new_args.size(), new_args.c_ptr());
            proof * p1 = proofs.empty() ? 0 : m_manager.mk_congruence(to_app(n), r1, proofs.size(), proofs.c_ptr());
            proof * p2 = r1 == r ? 0 : m_manager.mk_pull_quant(r1, to_quantifier(r));
            pr = m_manager.mk_transitivity(p1, p2);
        }
    }
    else if (is_quantifier(n)) {
        expr_ref new_expr(m_manager);
        pull_quant1(to_quantifier(n)->get_expr(), new_expr);
        pull_quant1(to_quantifier(n), new_expr, r);
        if (m_manager.fine_grain_proofs()) {
            quantifier * q1 = m_manager.update_quantifier(to_quantifier(n), new_expr);
            proof * p1 = 0;
            if (n != q1) {
                proof * p0 = m_manager.mk_pull_quant(to_quantifier(n)->get_expr(), to_quantifier(new_expr));
                p1 = m_manager.mk_quant_intro(to_quantifier(n), q1, p0);
            }
            proof * p2 = q1 == r ? 0 : m_manager.mk_pull_quant(q1, to_quantifier(r));
            pr = m_manager.mk_transitivity(p1, p2);
        }
    }
    else {
        r  = n;
    }
}

bool pull_quant::visit_children(expr * n) {
    bool visited = true;
    unsigned j;
    switch(n->get_kind()) {
    case AST_APP:
        // This transformation is also applied after the formula
        // has been converted into a SNF using only OR and NOT.
        if (m_manager.is_or(n) || m_manager.is_and(n) || m_manager.is_not(n)) {
            j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                visit(to_app(n)->get_arg(j), visited);
            }
        }
        else {
            // This class assumes the formula is in skolem normal form.
            SASSERT(!has_quantifiers(n));
        }
        break;
    case AST_QUANTIFIER:
        if (to_quantifier(n)->is_forall())
            visit(to_quantifier(n)->get_expr(), visited);
        break;
    default:
        break;
    }
    return visited;
}

void pull_quant::reduce1(expr * n) {
    switch(n->get_kind()) {
    case AST_APP:
        reduce1_app(to_app(n));
        break;
    case AST_VAR: 
        cache_result(n, n, 0); 
        break;
    case AST_QUANTIFIER: 
        reduce1_quantifier(to_quantifier(n));
        break;
    default:
        UNREACHABLE();
        break;
    }
}

void pull_quant::reduce1_app(app * n) {
    if (m_manager.is_or(n) || m_manager.is_and(n) || m_manager.is_not(n)) {
        ptr_buffer<expr>  new_children;
        ptr_buffer<proof> new_children_proofs;
        unsigned num = n->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            expr *  new_child = 0;
            proof * new_child_pr = 0;
            get_cached(n->get_arg(i), new_child, new_child_pr);
            new_children.push_back(new_child);
            if (new_child_pr) {
                new_children_proofs.push_back(new_child_pr);
            }
        }

        expr_ref r(m_manager);
        pull_quant1(n->get_decl(), new_children.size(), new_children.c_ptr(), r);
        proof * pr = 0;
        if (m_manager.fine_grain_proofs()) {
            app * n_prime = m_manager.mk_app(n->get_decl(), new_children.size(), new_children.c_ptr());
            TRACE("proof_bug", tout << mk_pp(n, m_manager) << "\n";
                  tout << mk_pp(n_prime, m_manager) << "\n";);
            proof * p1 = n == n_prime ? 0 : m_manager.mk_congruence(n, n_prime, 
                                                                    new_children_proofs.size(), new_children_proofs.c_ptr());
            proof * p2 = n_prime == r ? 0 : m_manager.mk_pull_quant(n_prime, to_quantifier(r));
            pr         = m_manager.mk_transitivity(p1, p2);
        }
        cache_result(n, r, pr);
        return;
    }
    TRACE("proof_bug", tout << mk_pp(n, m_manager) << "\n";);
    cache_result(n, n, 0);
}

void pull_quant::reduce1_quantifier(quantifier * q) {
    if (q->is_forall()) {
        expr * new_expr;
        proof * new_expr_pr;
        get_cached(q->get_expr(), new_expr, new_expr_pr);
        expr_ref r(m_manager);
        pull_quant1(q, new_expr, r);
        proof * pr = 0;
        if (m_manager.fine_grain_proofs()) {
            quantifier * q_prime = m_manager.update_quantifier(q, new_expr);
            proof * p1 = q == q_prime ? 0 : m_manager.mk_quant_intro(q, q_prime, new_expr_pr);
            proof * p2 = q_prime == r ? 0 : m_manager.mk_pull_quant(q_prime, to_quantifier(r));
            pr         = m_manager.mk_transitivity(p1, p2);
        }
        cache_result(q, r, pr);
        return;
    }
    // should be unreachable, right?
    UNREACHABLE();
    cache_result(q, q, 0);
}
    
pull_quant::pull_quant(ast_manager & m):
    base_simplifier(m),
    m_shift(m) {
}

void pull_quant::operator()(expr * n, expr_ref & r, proof_ref & p) {
    flush_cache();
    m_todo.push_back(n);
    while (!m_todo.empty()) {
        expr * n = m_todo.back();
        if (is_cached(n))
            m_todo.pop_back();
        else if (visit_children(n)) {
            m_todo.pop_back();
            reduce1(n);
        }
    }

    expr  * result;
    proof * result_proof;
    get_cached(n, result, result_proof);
    
    r = result;
    
    switch (m_manager.proof_mode()) {
    case PGM_DISABLED:
        p = m_manager.mk_undef_proof();
        break;
    case PGM_COARSE:
        if (result == n) 
            p = m_manager.mk_reflexivity(n);
        else
            p = m_manager.mk_pull_quant_star(n, to_quantifier(result));
        break;
    case PGM_FINE:
        SASSERT(result_proof || result == n);
        p = result_proof ? result_proof : m_manager.mk_reflexivity(n);
        break;
    }
}

bool pull_nested_quant::visit_quantifier(quantifier * q) {
    // do not recurse.
    return true;
}

void pull_nested_quant::reduce1_quantifier(quantifier * q) {
    expr_ref r(m_manager);
    proof_ref pr(m_manager);
    m_pull(q, r, pr);
    cache_result(q, r, pr);
}
