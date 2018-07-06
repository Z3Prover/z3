/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_quick_checker.cpp

Abstract:

    Incomplete model checker.

Author:

    Leonardo de Moura (leonardo) 2008-06-20.

Revision History:

--*/
#include "smt/smt_context.h"
#include "smt/smt_quick_checker.h"
#include "ast/ast_pp.h"
#include <tuple>

namespace smt {

    quick_checker::collector::collector(context & c):
        m_context(c),
        m_manager(c.get_manager()),
        m_conservative(true) {
    }

    void quick_checker::collector::init(quantifier * q) {
        m_num_vars = q->get_num_decls();
        m_already_found.reserve(m_num_vars+1, false);
        m_candidates.reserve(m_num_vars+1);
        m_tmp_candidates.reserve(m_num_vars+1);
        for (unsigned i = 0; i < m_num_vars; i++) {
            m_already_found[i] = false;
            m_candidates[i].reset();
        }
        m_cache.reset();
    }

    /**
       \brief Returns true if there is a term (f ... n' ...) in the logical 
       context such that n' is the i-th argument of f, and n and n' are in the
       same equivalence class.

       If f == 0 then true is returned (f == 0 means there is no parent to check)

    */
    bool quick_checker::collector::check_arg(enode * n, func_decl * f, unsigned i) {
        if (!f || !m_conservative)
            return true;
        for (enode * curr : m_context.enodes_of(f)) {
            if (m_context.is_relevant(curr) && curr->is_cgr() && i < curr->get_num_args() && curr->get_arg(i)->get_root() == n->get_root())
                return true;
        }
        return false;
    }

    void quick_checker::collector::collect_core(app * n, func_decl * p, unsigned i) {
        func_decl * f     = n->get_decl();
        unsigned num_args = n->get_num_args();
        for (unsigned j = 0; j < num_args; j++) {
            expr * arg = n->get_arg(j);
            if (is_var(arg)) {
                unsigned idx = to_var(arg)->get_idx();
                if (idx >= m_num_vars)
                    return;
                if (m_already_found[idx] && m_conservative) {
                    enode_set & s  = m_candidates[idx];
                    enode_set & ns = m_tmp_candidates[idx];
                    if (s.empty())
                        continue;
                    ns.reset();
                    for (enode * curr : m_context.enodes_of(f)) {
                        if (m_context.is_relevant(curr) && curr->is_cgr() && check_arg(curr, p, i) && j < curr->get_num_args()) {
                            enode * arg = curr->get_arg(j)->get_root();
                            // intersection
                            if (s.contains(arg))
                                ns.insert(arg);
                        }
                    }
                    SASSERT(m_conservative);
                    s.swap(ns);
                }
                else {
                    m_already_found[idx] = true;
                    enode_set & s  = m_candidates[idx];
                    for (enode * curr : m_context.enodes_of(f)) {
                        if (m_context.is_relevant(curr) && curr->is_cgr() && check_arg(curr, p, i) && j < curr->get_num_args()) {
                            enode * arg = curr->get_arg(j)->get_root();
                            s.insert(arg);
                        }
                    }
                }
            }
            else {
                if (n->get_family_id() != m_manager.get_basic_family_id())
                    collect(arg, n->get_decl(), j);
                else
                    collect(arg, nullptr, 0);
            }
        }
    }

    void quick_checker::collector::collect(expr * n, func_decl * f, unsigned idx) {
        if (is_quantifier(n))
            return;
        if (is_var(n))
            return;
        if (is_ground(n))
            return;
        entry e(n, f, idx);
        if (m_cache.contains(e))
            return;
        m_cache.insert(e);
        collect_core(to_app(n), f, idx);
    }

    void quick_checker::collector::save_result(vector<enode_vector> & candidates) {
        candidates.reserve(m_num_vars+1);
        for (unsigned i = 0; i < m_num_vars; i++) {
            enode_vector & v        = candidates[i];
            v.reset();
            enode_set & s           = m_candidates[i];
            for (enode * curr : s) {
                v.push_back(curr);
            }
        }
        TRACE("collector", 
              tout << "candidates:\n";
              for (unsigned i = 0; i < m_num_vars; i++) {
                  tout << "var " << i << ":";
                  enode_vector & v           = candidates[i];
                  for (enode * n : v) 
                      tout << " #" << n->get_owner_id();
                  tout << "\n";
              });
    }

    void quick_checker::collector::operator()(quantifier * q, bool conservative, vector<enode_vector> & candidates) {
        flet<bool> l(m_conservative, conservative);
        init(q);
        TRACE("collector", tout << "model checking: #" << q->get_id() << "\n" << mk_pp(q, m_manager) << "\n";);
        collect(q->get_expr(), nullptr, 0);
        save_result(candidates);
    }

    quick_checker::quick_checker(context & c):
        m_context(c),
        m_manager(c.get_manager()),
        m_collector(c),
        m_new_exprs(m_manager) {
    }

    /**
       \brief Instantiate instances unsatisfied by the current model. Return true if new instances were generated.
    */
    bool quick_checker::instantiate_unsat(quantifier * q) {
        TRACE("quick_checker", tout << "instantiate instances unsatisfied by current model\n" << mk_pp(q, m_manager) << "\n";);
        m_candidate_vectors.reset();
        m_collector(q, true, m_candidate_vectors);
        m_num_bindings = q->get_num_decls();
        return process_candidates(q, true);
    }

    /**
       \brief Instantiate instances not satisfied by the current model. Return true if new instances were generated.
    */
    bool quick_checker::instantiate_not_sat(quantifier * q) {
        TRACE("quick_checker", tout << "instantiate instances not satisfied by current model\n" << mk_pp(q, m_manager) << "\n";);
        m_candidate_vectors.reset();
        m_collector(q, false, m_candidate_vectors);
        m_num_bindings = q->get_num_decls();
        return process_candidates(q, false);
    }

    bool quick_checker::instantiate_not_sat(quantifier * q, unsigned num_candidates, expr * const * candidates) {
        // initialize m_candidates using the given set of candidates.
        m_candidate_vectors.reset();
        m_num_bindings = q->get_num_decls();
        m_candidate_vectors.reserve(m_num_bindings+1);
        for (unsigned i = 0; i < m_num_bindings; i++) {
            m_candidate_vectors[i].reset();
            sort * s = q->get_decl_sort(i);
            for (unsigned j = 0; j < num_candidates; j++) {
                if (m_manager.get_sort(candidates[j]) == s) {
                    expr * n = candidates[j];
                    m_context.internalize(n, false);
                    enode * e = m_context.get_enode(n);
                    m_candidate_vectors[i].push_back(e);
                }
            }
        }
        return process_candidates(q, false);
    }

    bool quick_checker::process_candidates(quantifier * q, bool unsat) {
        vector<std::tuple<enode *, enode *>> empty_used_enodes;
        buffer<unsigned> szs;
        buffer<unsigned> it;
        for (unsigned i = 0; i < m_num_bindings; i++) {
            unsigned sz = m_candidate_vectors[i].size();
            if (sz == 0)
                return false;
            szs.push_back(sz);
            it.push_back(0);
        }
        TRACE("quick_checker_sizes", tout << mk_pp(q, m_manager) << "\n"; for (unsigned i = 0; i < szs.size(); i++) tout << szs[i] << " "; tout << "\n";);
        TRACE("quick_checker_candidates", 
              tout << "candidates:\n";
              for (unsigned i = 0; i < m_num_bindings; i++) {
                  enode_vector & v           = m_candidate_vectors[i];
                  for (enode * n : v) 
                      tout << "#" << n->get_owner_id() << " ";
                  tout << "\n";
              });
        bool result = false;
        m_bindings.reserve(m_num_bindings+1, 0);
        do {
            for (unsigned i = 0; i < m_num_bindings; i++)
                m_bindings[m_num_bindings - i - 1] = m_candidate_vectors[i][it[i]];
            if (!m_context.contains_instance(q, m_num_bindings, m_bindings.c_ptr())) {
                bool is_candidate = false;
                TRACE("quick_checker", tout << "processing bindings:";
                      for (unsigned i = 0; i < m_num_bindings; i++) tout << " #" << m_bindings[i]->get_owner_id();
                      tout << "\n";);
                if (unsat)
                    is_candidate = check_quantifier(q, false);
                else
                    is_candidate = !check_quantifier(q, true);
                if (is_candidate) {
                    TRACE("quick_checker", tout << "found new candidate\n";);
                    TRACE("quick_checker_sizes", tout << "found new candidate\n"; 
                          for (unsigned i = 0; i < m_num_bindings; i++) tout << "#" << m_bindings[i]->get_owner_id() << " "; tout << "\n";);
                    unsigned max_generation = get_max_generation(m_num_bindings, m_bindings.c_ptr());
                    if (m_context.add_instance(q, nullptr /* no pattern was used */, m_num_bindings, m_bindings.c_ptr(), nullptr, 
                                               max_generation,
                                               0,  // min_top_generation is only available for instances created by the MAM
                                               0,  // max_top_generation is only available for instances created by the MAM
                                               empty_used_enodes))
                        result = true;
                }
            }
        }
        while (product_iterator_next(szs.size(), szs.c_ptr(), it.c_ptr()));
        return result;
    }

    bool quick_checker::check_quantifier(quantifier * n, bool is_true) {
        bool r = check(n->get_expr(), is_true);
        m_new_exprs.reset();
        m_check_cache.reset();
        m_canonize_cache.reset();
        return r;
    }

    bool quick_checker::all_args(app * a, bool is_true) {
        unsigned num_args = a->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            if (!check(a->get_arg(i), is_true))
                return false;
        return true;
    }

    bool quick_checker::any_arg(app * a, bool is_true) {
        unsigned num_args = a->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            if (check(a->get_arg(i), is_true))
                return true;
        return false;
    }

    bool quick_checker::check_core(expr * n, bool is_true) {
        SASSERT(m_manager.is_bool(n));
        if (m_context.b_internalized(n) && m_context.is_relevant(n)) {
            lbool val = m_context.get_assignment(n);
            if (val != l_undef && is_true == (val == l_true))
                return true;
            else 
                return false;
        }
        if (!is_app(n))
            return false;
        app * a = to_app(n);
        if (a->get_family_id() == m_manager.get_basic_family_id()) {
            switch (a->get_decl_kind()) {
            case OP_TRUE:
                return is_true;
            case OP_FALSE:
                return !is_true;
            case OP_NOT:
                return check(a->get_arg(0), !is_true);
            case OP_OR:
                return is_true ? any_arg(a, true) : all_args(a, false);
            case OP_AND:
                return is_true ? all_args(a, true) : any_arg(a, false);
            case OP_ITE: 
                if (check(a->get_arg(0), true))
                    return check(a->get_arg(1), is_true);
                else if (check(a->get_arg(0), false))
                    return check(a->get_arg(2), is_true);
                else 
                    return check(a->get_arg(1), is_true) && check(a->get_arg(2), is_true);
            case OP_EQ: 
                if (m_manager.is_iff(a)) {
                    if (is_true)
                        return (check(a->get_arg(0), true)  && check(a->get_arg(1), true))  || (check(a->get_arg(0), false) && check(a->get_arg(1), false));
                    else
                        return (check(a->get_arg(0), true)  && check(a->get_arg(1), false)) || (check(a->get_arg(0), false) && check(a->get_arg(1), true));
                }

                if (is_true) {
                    return canonize(a->get_arg(0)) == canonize(a->get_arg(1));
                }
                else {
                    expr * lhs = canonize(a->get_arg(0));
                    expr * rhs = canonize(a->get_arg(1));
                    if (m_context.e_internalized(lhs) && m_context.is_relevant(lhs) && 
                        m_context.e_internalized(rhs) && m_context.is_relevant(rhs) &&
                        m_context.get_enode(lhs)->get_root() != m_context.get_enode(rhs)->get_root())
                        return true;
                    return m_manager.are_distinct(lhs, rhs);
                }
            default:
                break;
            }
        }
        expr * new_a = canonize(a);
        TRACE("quick_checker_canonizer", tout << "before:\n" << mk_pp(a, m_manager) << "\nafter:\n" << mk_pp(new_a, m_manager) << "\n";);
        if (m_context.lit_internalized(new_a) && m_context.is_relevant(new_a)) {
            lbool val = m_context.get_assignment(new_a);
            if (val != l_undef)
                return is_true == (val == l_true);
        }
        if (is_true && m_manager.is_true(new_a))
            return true;
        if (!is_true && m_manager.is_false(new_a))
            return true;
        return false;
    }

    bool quick_checker::check(expr * n, bool is_true) {
        expr_bool_pair p(n, is_true);
        bool r;
        if (m_check_cache.find(p, r))
            return r;
        r = check_core(n, is_true);
        m_check_cache.insert(p, r);
        return r;
    }

    expr * quick_checker::canonize(expr * n) {
        if (is_var(n)) {
            unsigned idx = to_var(n)->get_idx();
            if (idx >= m_num_bindings)
                return n;
            // VAR 0 is stored in the last position of m_bindings
            return m_bindings[m_num_bindings - idx - 1]->get_root()->get_owner();
        }
        if (m_context.e_internalized(n))
            return m_context.get_enode(n)->get_root()->get_owner();
        if (!is_app(n) || to_app(n)->get_num_args() == 0)
            return n;
        expr * r;
        if (m_canonize_cache.find(n, r))
            return r;
        bool has_arg_enodes = true;
        ptr_buffer<expr>  new_args;
        ptr_buffer<enode> new_arg_enodes;
        unsigned num_args = to_app(n)->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = canonize(to_app(n)->get_arg(i));
            new_args.push_back(arg);
            if (m_context.e_internalized(arg))
                new_arg_enodes.push_back(m_context.get_enode(arg));
            else
                has_arg_enodes = false;
        }
        if (has_arg_enodes) {
            enode * e = m_context.get_enode_eq_to(to_app(n)->get_decl(), num_args, new_arg_enodes.c_ptr());
            if (e) {
                m_canonize_cache.insert(n, e->get_root()->get_owner());
                return e->get_root()->get_owner();
            }
        }
        // substitute by values in the model
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = new_args[i];
            if (m_context.e_internalized(arg)) {
                expr_ref new_value(m_manager);
                if (m_context.get_value(m_context.get_enode(arg), new_value)) {
                    new_args[i] = new_value;
                    m_new_exprs.push_back(new_value);
                }
            }
        }
        expr_ref new_expr(m_manager);
        new_expr = m_context.get_rewriter().mk_app(to_app(n)->get_decl(), num_args, new_args.c_ptr());
        m_new_exprs.push_back(new_expr);
        m_canonize_cache.insert(n, new_expr);
        return new_expr;
    }

};

