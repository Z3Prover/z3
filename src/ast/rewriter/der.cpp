/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    der.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-27.

Revision History:

    Christoph Wintersteiger, 2010-03-30: Added Destr. Multi-Equality Resolution

--*/
#include "ast/rewriter/der.h"
#include "ast/occurs.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"

static bool is_var(expr * e, unsigned num_decls) {
    return is_var(e) && to_var(e)->get_idx() < num_decls;
}

static bool is_neg_var(ast_manager & m, expr * e, unsigned num_decls) {
    return m.is_not(e) && is_var(to_app(e)->get_arg(0)) && to_var(to_app(e)->get_arg(0))->get_idx() < num_decls;
}

/**
   \brief Return true if \c e is of the form (not (= VAR t)) or (not (iff VAR t)) or (iff VAR t) or (iff (not VAR) t) or (VAR IDX) or (not (VAR IDX)).
   The last case can be viewed
*/
bool der::is_var_diseq(expr * e, unsigned num_decls, var * & v, expr_ref & t) {
    // (not (= VAR t)) and (not (iff VAR t)) cases
    if (m_manager.is_not(e) && (m_manager.is_eq(to_app(e)->get_arg(0)) || m_manager.is_iff(to_app(e)->get_arg(0)))) {
        app * eq   = to_app(to_app(e)->get_arg(0));
        SASSERT(m_manager.is_eq(eq) || m_manager.is_iff(eq));
        expr * lhs = eq->get_arg(0);
        expr * rhs = eq->get_arg(1);
        if (!is_var(lhs, num_decls) && !is_var(rhs, num_decls))
            return false;
        if (!is_var(lhs, num_decls))
            std::swap(lhs, rhs);
        SASSERT(is_var(lhs, num_decls));
        // Remark: Occurs check is not necessary here... the top-sort procedure will check for cycles...
        // if (occurs(lhs, rhs)) {
        //  return false;
        // }
        v = to_var(lhs);
        t = rhs;
        TRACE("der", tout << mk_pp(e, m_manager) << "\n";);
        return true;
    }
    // (iff VAR t) and (iff (not VAR) t) cases
    else if (m_manager.is_iff(e)) {
        expr * lhs = to_app(e)->get_arg(0);
        expr * rhs = to_app(e)->get_arg(1);
        // (iff VAR t) case
        if (is_var(lhs, num_decls) || is_var(rhs, num_decls)) {
            if (!is_var(lhs, num_decls))
                std::swap(lhs, rhs);
            SASSERT(is_var(lhs, num_decls));
            // Remark: Occurs check is not necessary here... the top-sort procedure will check for cycles...
            // if (occurs(lhs, rhs)) {
            //    return false;
            // }
            v = to_var(lhs);
            t = m_manager.mk_not(rhs);
            m_new_exprs.push_back(t);
            TRACE("der", tout << mk_pp(e, m_manager) << "\n";);
            return true;
        }
        // (iff (not VAR) t) case
        else if (is_neg_var(m_manager, lhs, num_decls) || is_neg_var(m_manager, rhs, num_decls)) {
            if (!is_neg_var(m_manager, lhs, num_decls))
                std::swap(lhs, rhs);
            SASSERT(is_neg_var(m_manager, lhs, num_decls));
            expr * lhs_var = to_app(lhs)->get_arg(0);
            // Remark: Occurs check is not necessary here... the top-sort procedure will check for cycles...
            // if (occurs(lhs_var, rhs)) {
            //    return false;
            // }
            v = to_var(lhs_var);
            t = rhs;
            TRACE("der", tout << mk_pp(e, m_manager) << "\n";);
            return true;
        }
        else {
            return false;
        }
    }
    // VAR != false case
    else if (is_var(e, num_decls)) {
        t = m_manager.mk_false();
        v = to_var(e);
        TRACE("der", tout << mk_pp(e, m_manager) << "\n";);
        return true;
    }
    // VAR != true case
    else if (is_neg_var(m_manager, e, num_decls)) {
        t = m_manager.mk_true();
        v = to_var(to_app(e)->get_arg(0));
        TRACE("der", tout << mk_pp(e, m_manager) << "\n";);
        return true;
    }
    else {
        return false;
    }
}

void der::operator()(quantifier * q, expr_ref & r, proof_ref & pr) {
    bool reduced = false;
    pr = nullptr;
    r  = q;

    TRACE("der", tout << mk_pp(q, m_manager) << "\n";);

    // Keep applying it until r doesn't change anymore
    do {
        proof_ref curr_pr(m_manager);
        q  = to_quantifier(r);
        reduce1(q, r, curr_pr);
        if (q != r)
            reduced = true;
        if (m_manager.proofs_enabled()) {
            pr = m_manager.mk_transitivity(pr, curr_pr);
        }
    } while (q != r && is_quantifier(r));

    // Eliminate variables that have become unused
    if (reduced && is_forall(r)) {
        quantifier * q = to_quantifier(r);
        elim_unused_vars(m_manager, q, params_ref(), r);
        if (m_manager.proofs_enabled()) {
            proof * p1 = m_manager.mk_elim_unused_vars(q, r);
            pr = m_manager.mk_transitivity(pr, p1);
        }
    }
    m_new_exprs.reset();
}

void der::reduce1(quantifier * q, expr_ref & r, proof_ref & pr) {
    if (!is_forall(q)) {
        pr = nullptr;
        r  = q;
        return;
    }

    expr * e = q->get_expr();
    unsigned num_decls = q->get_num_decls();
    var * v = nullptr;
    expr_ref t(m_manager);

    if (m_manager.is_or(e)) {
        unsigned num_args = to_app(e)->get_num_args();
        unsigned i = 0;
        unsigned diseq_count = 0;
        unsigned largest_vinx = 0;

        m_map.reset();
        m_pos2var.reset();
        m_inx2var.reset();

        m_pos2var.reserve(num_args, -1);

        // Find all disequalities
        for (; i < num_args; i++) {
            if (is_var_diseq(to_app(e)->get_arg(i), num_decls, v, t)) {
                unsigned idx = v->get_idx();
                if(m_map.get(idx, 0) == 0) {
                    m_map.reserve(idx + 1, 0);
                    m_inx2var.reserve(idx + 1, 0);

                    m_map[idx] = t;
                    m_inx2var[idx] = v;
                    m_pos2var[i] = idx;
                    diseq_count++;
                    largest_vinx = (idx>largest_vinx) ? idx : largest_vinx;
                }
            }
        }

        if (diseq_count > 0) {
            get_elimination_order();
            SASSERT(m_order.size() <= diseq_count); // some might be missing because of cycles

            if (!m_order.empty()) {
                create_substitution(largest_vinx + 1);
                apply_substitution(q, r);
            }
        }
        else {
            TRACE("der_bug", tout << "Did not find any diseq\n" << mk_pp(q, m_manager) << "\n";);
            r = q;
        }
    }
    // Remark: get_elimination_order/top-sort checks for cycles, but it is not invoked for unit clauses.
    // So, we must perform a occurs check here.
    else if (is_var_diseq(e, num_decls, v, t) && !occurs(v, t)) {
        r = m_manager.mk_false();
    }
    else
        r = q;

    if (m_manager.proofs_enabled()) {
        pr = r == q ? nullptr : m_manager.mk_der(q, r);
    }
}

void der_sort_vars(ptr_vector<var> & vars, ptr_vector<expr> & definitions, unsigned_vector & order) {
    order.reset();

    // eliminate self loops, and definitions containing quantifiers.
    bool found = false;
    for (unsigned i = 0; i < definitions.size(); i++) {
        var * v  = vars[i];
        expr * t = definitions[i];
        if (t == nullptr || has_quantifiers(t) || occurs(v, t))
            definitions[i] = 0;
        else
            found = true; // found at least one candidate
    }

    if (!found)
        return;

    typedef std::pair<expr *, unsigned> frame;
    svector<frame> todo;

    expr_fast_mark1 visiting;
    expr_fast_mark2 done;

    unsigned vidx, num;

    for (unsigned i = 0; i < definitions.size(); i++) {
        if (definitions[i] == 0)
            continue;
        var * v = vars[i];
        SASSERT(v->get_idx() == i);
        SASSERT(todo.empty());
        todo.push_back(frame(v, 0));
        while (!todo.empty()) {
        start:
            frame & fr = todo.back();
            expr * t   = fr.first;
            if (t->get_ref_count() > 1 && done.is_marked(t)) {
                todo.pop_back();
                continue;
            }
            switch (t->get_kind()) {
            case AST_VAR:
                vidx = to_var(t)->get_idx();
                if (fr.second == 0) {
                    CTRACE("der_bug", vidx >= definitions.size(), tout << "vidx: " << vidx << "\n";);
                    // Remark: The size of definitions may be smaller than the number of variables occurring in the quantified formula.
                    if (definitions.get(vidx, 0) != 0) {
                        if (visiting.is_marked(t)) {
                            // cycle detected: remove t
                            visiting.reset_mark(t);
                            definitions[vidx] = 0;
                        }
                        else {
                            visiting.mark(t);
                            fr.second = 1;
                            todo.push_back(frame(definitions[vidx], 0));
                            goto start;
                        }
                    }
                }
                else {
                    SASSERT(fr.second == 1);
                    if (definitions.get(vidx, 0) != 0) {
                        visiting.reset_mark(t);
                        order.push_back(vidx);
                    }
                    else {
                        // var was removed from the list of candidate vars to elim cycle
                        // do nothing
                    }
                }
                if (t->get_ref_count() > 1)
                    done.mark(t);
                todo.pop_back();
                break;
            case AST_QUANTIFIER:
                UNREACHABLE();
                todo.pop_back();
                break;
            case AST_APP:
                num = to_app(t)->get_num_args();
                while (fr.second < num) {
                    expr * arg = to_app(t)->get_arg(fr.second);
                    fr.second++;
                    if (arg->get_ref_count() > 1 && done.is_marked(arg))
                        continue;
                    todo.push_back(frame(arg, 0));
                    goto start;
                }
                if (t->get_ref_count() > 1)
                    done.mark(t);
                todo.pop_back();
                break;
            default:
                UNREACHABLE();
                todo.pop_back();
                break;
            }
        }
    }
}

void der::get_elimination_order() {
    m_order.reset();

    TRACE("top_sort",
        tout << "DEFINITIONS: " << std::endl;
        for(unsigned i = 0; i < m_map.size(); i++)
            if(m_map[i]) tout << "VAR " << i << " = " << mk_pp(m_map[i], m_manager) << std::endl;
      );

    // der::top_sort ts(m_manager);
    der_sort_vars(m_inx2var, m_map, m_order);

    TRACE("der",
            tout << "Elimination m_order:" << std::endl;
            for(unsigned i=0; i<m_order.size(); i++)
            {
                if (i != 0) tout << ",";
                tout << m_order[i];
            }
            tout << std::endl;
          );
}

void der::create_substitution(unsigned sz) {
    m_subst_map.reset();
    m_subst_map.resize(sz, nullptr);

    for(unsigned i = 0; i < m_order.size(); i++) {
        expr_ref cur(m_map[m_order[i]], m_manager);

        // do all the previous substitutions before inserting
        expr_ref r(m_manager);
        m_subst(cur, m_subst_map.size(), m_subst_map.c_ptr(), r);

        unsigned inx = sz - m_order[i]- 1;
        SASSERT(m_subst_map[inx]==0);
        m_subst_map[inx] = r;
    }
}

void der::apply_substitution(quantifier * q, expr_ref & r) {
    expr * e = q->get_expr();
    unsigned num_args=to_app(e)->get_num_args();

    // get a new expression
    m_new_args.reset();
    for(unsigned i = 0; i < num_args; i++) {
        int x = m_pos2var[i];
        if (x != -1 && m_map[x] != 0)
            continue; // this is a disequality with definition (vanishes)

        m_new_args.push_back(to_app(e)->get_arg(i));
    }

    unsigned sz = m_new_args.size();
    expr_ref t(m_manager);
    t = (sz == 1) ? m_new_args[0] : m_manager.mk_or(sz, m_new_args.c_ptr());
    expr_ref new_e(m_manager);
    m_subst(t, m_subst_map.size(), m_subst_map.c_ptr(), new_e);

    // don't forget to update the quantifier patterns
    expr_ref_buffer  new_patterns(m_manager);
    expr_ref_buffer  new_no_patterns(m_manager);
    for (unsigned j = 0; j < q->get_num_patterns(); j++) {
        expr_ref new_pat(m_manager);
        m_subst(q->get_pattern(j), m_subst_map.size(), m_subst_map.c_ptr(), new_pat);
        new_patterns.push_back(new_pat);
    }

    for (unsigned j = 0; j < q->get_num_no_patterns(); j++) {
        expr_ref new_nopat(m_manager);
        m_subst(q->get_no_pattern(j), m_subst_map.size(), m_subst_map.c_ptr(), new_nopat);
        new_no_patterns.push_back(new_nopat);
    }

    r = m_manager.update_quantifier(q, new_patterns.size(), new_patterns.c_ptr(),
                                    new_no_patterns.size(), new_no_patterns.c_ptr(), new_e);
}


struct der_rewriter_cfg : public default_rewriter_cfg {
    der   m_der;

    der_rewriter_cfg(ast_manager & m):m_der(m) {}

    ast_manager & m() const { return m_der.m(); }

    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        quantifier_ref q1(m());
        q1 = m().update_quantifier(old_q, old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns, new_body);
        m_der(q1, result, result_pr);
        return true;
    }
};

template class rewriter_tpl<der_rewriter_cfg>;

struct der_rewriter::imp : public rewriter_tpl<der_rewriter_cfg> {
    der_rewriter_cfg m_cfg;
    imp(ast_manager & m):
        rewriter_tpl<der_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m) {
    }
};

der_rewriter::der_rewriter(ast_manager & m) {
    m_imp = alloc(imp, m);
}

der_rewriter::~der_rewriter() {
    dealloc(m_imp);
}

ast_manager & der_rewriter::m() const {
    return m_imp->m();
}


void der_rewriter::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    m_imp->operator()(t, result, result_pr);
}


void der_rewriter::cleanup() {
    ast_manager & m = m_imp->m();
    #pragma omp critical (th_rewriter)
    {
        dealloc(m_imp);
        m_imp = alloc(imp, m);
    }
}

void der_rewriter::reset() {
    m_imp->reset();
}


