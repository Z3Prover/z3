/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    demodulator.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-12.

Revision History:

    Christoph M. Wintersteiger (cwinter) 2010-04-21: Implementation
    Christoph M. Wintersteiger (cwinter) 2012-10-24: Moved from demodulator.h to ufbv_rewriter.h

--*/

#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "tactic/ufbv/ufbv_rewriter.h"

ufbv_rewriter::ufbv_rewriter(ast_manager & m):
    m_manager(m),
    m_match_subst(m),
    m_bsimp(m),
    m_todo(m),
    m_rewrite_todo(m),
    m_rewrite_cache(m),
    m_new_exprs(m) {
    params_ref p;
    p.set_bool("elim_and", true);
    m_bsimp.updt_params(p);
}

ufbv_rewriter::~ufbv_rewriter() {
    reset_dealloc_values(m_fwd_idx);
    reset_dealloc_values(m_back_idx);
    for (demodulator2lhs_rhs::iterator it = m_demodulator2lhs_rhs.begin(); it != m_demodulator2lhs_rhs.end(); it++) {
        m_manager.dec_ref(it->m_key);
        m_manager.dec_ref(it->m_value.first);
        m_manager.dec_ref(it->m_value.second);
    }
}

bool ufbv_rewriter::is_demodulator(expr * e, expr_ref & large, expr_ref & small) const {
    if (e->get_kind() == AST_QUANTIFIER) {
        quantifier * q = to_quantifier(e);
        if (is_forall(q)) {
            expr * qe = q->get_expr();
            if ((m_manager.is_eq(qe) || m_manager.is_iff(qe))) {
                app * eq = to_app(q->get_expr());
                expr * lhs = eq->get_arg(0);
                expr * rhs = eq->get_arg(1);
                int subset = is_subset(lhs, rhs);
                int smaller = is_smaller(lhs, rhs);
                TRACE("demodulator", tout << "testing is_demodulator:\n"
                      << mk_pp(lhs, m_manager) << "\n"
                      << mk_pp(rhs, m_manager) << "\n"
                      << "subset: " << subset << ", smaller: " << smaller << "\n";);
                // We only track uninterpreted functions, everything else is likely too expensive.
                if ((subset == +1 || subset == +2) && smaller == +1) {
                    if (is_uninterp(rhs)) {
                        large = rhs;
                        small = lhs;
                        return true;
                    }
#if 1
                    // lhs = (not rhs) --> (not lhs) = rhs
                    expr * not_rhs;
                    if (m_manager.is_not(rhs, not_rhs) && is_uninterp(not_rhs)) {
                        large = not_rhs;
                        small = m_manager.mk_not(lhs);
                        return true;
                    }
#endif
                }

                if ((subset == -1 || subset == +2) && smaller == -1) {
                    if (is_uninterp(lhs)) {
                        large = lhs;
                        small = rhs;
                        return true;
                    }
#if 1
                    // (not lhs) = rhs --> lhs = (not rhs)
                    expr * not_lhs;
                    if (m_manager.is_not(lhs, not_lhs) && is_uninterp(not_lhs)) {
                        large = not_lhs;
                        small = m_manager.mk_not(rhs);
                        return true;
                    }
#endif
                }

            } else if (m_manager.is_not(qe) && is_uninterp(to_app(qe)->get_arg(0))) {
                // this is like (not (f ... )) --> (= (f ...) false)
                large = to_app(qe)->get_arg(0);
                small = m_manager.mk_false();
                return true;
            } else if (is_uninterp(qe)) {
                // this is like (f ... ) --> (= (f ...) true)
                large = to_app(qe);
                small = m_manager.mk_true();
                return true;
            }
        }
    }

    return false;
}

class var_set_proc {
    uint_set & m_set;
public:
    var_set_proc(uint_set &s):m_set(s) {}
    void operator()(var * n) { m_set.insert(n->get_idx()); }
    void operator()(quantifier * n) {}
    void operator()(app * n) {}
};

int ufbv_rewriter::is_subset(expr * e1, expr * e2) const {
    uint_set ev1, ev2;

    if (m_manager.is_value(e1))
        return 1; // values are always a subset!

    var_set_proc proc1(ev1);
    for_each_expr(proc1, e1);
    var_set_proc proc2(ev2);
    for_each_expr(proc2, e2);

    return (ev1==ev2          ) ? +2 : // We return +2 if the sets are equal.
           (ev1.subset_of(ev2)) ? +1 :
           (ev2.subset_of(ev1)) ? -1 :
                                   0 ;
}

int ufbv_rewriter::is_smaller(expr * e1, expr * e2) const {
    unsigned sz1 = 0, sz2 = 0;

    // values are always smaller!
    if (m_manager.is_value(e1))
        return +1;
    else if (m_manager.is_value(e2))
        return -1;

    // interpreted stuff is always better than uninterpreted.
    if (!is_uninterp(e1) && is_uninterp(e2))
        return +1;
    else if (is_uninterp(e1) && !is_uninterp(e2))
        return -1;

    // two uninterpreted functions are ordered first by the number of
    // arguments, then by their id.
    if (is_uninterp(e1) && is_uninterp(e2)) {
        if (to_app(e1)->get_num_args() < to_app(e2)->get_num_args())
            return +1;
        else if (to_app(e1)->get_num_args() > to_app(e2)->get_num_args())
            return -1;
        else {
            unsigned a = to_app(e1)->get_decl()->get_id();
            unsigned b = to_app(e2)->get_decl()->get_id();
            if (a < b)
                return +1;
            else if (a > b)
                return -1;
        }
    }

    switch (e1->get_kind()) {
        case AST_VAR: sz1 = 1; break;
        case AST_QUANTIFIER: sz1 = to_quantifier(e1)->get_depth(); break;
        case AST_APP: sz1 = to_app(e1)->get_depth(); break;
        default: UNREACHABLE();
    }

    switch (e2->get_kind()) {
        case AST_VAR: sz2 = 1; break;
        case AST_QUANTIFIER: sz2 = to_quantifier(e2)->get_depth(); break;
        case AST_APP: sz2 = to_app(e2)->get_depth(); break;
        default: UNREACHABLE();
    }

    return (sz1 == sz2) ?  0 :
           (sz1  < sz2) ? +1 :
                          -1 ;
}

class max_var_id_proc {
    unsigned    m_max_var_id;
public:
    max_var_id_proc():m_max_var_id(0) {}
    void operator()(var * n) {
        if(n->get_idx() > m_max_var_id)
            m_max_var_id = n->get_idx();
    }
    void operator()(quantifier * n) {}
    void operator()(app * n) {}
    unsigned get_max() { return m_max_var_id; }
};

unsigned ufbv_rewriter::max_var_id(expr * e)
{
    max_var_id_proc proc;
    for_each_expr(proc, e);
    return proc.get_max();
}

void ufbv_rewriter::insert_fwd_idx(expr * large, expr * small, quantifier * demodulator) {
    SASSERT(large->get_kind() == AST_APP);
    SASSERT(demodulator);
    SASSERT(large && small);
    TRACE("demodulator_fwd", tout << "INSERT: " << mk_pp(demodulator, m_manager) << std::endl; );

    func_decl * fd = to_app(large)->get_decl();

    fwd_idx_map::iterator it = m_fwd_idx.find_iterator(fd);
    if (it == m_fwd_idx.end()) {
        quantifier_set * qs = alloc(quantifier_set, 1);
        m_fwd_idx.insert(fd, qs);
        it = m_fwd_idx.find_iterator(fd);
    }

    SASSERT(it->m_value);
    it->m_value->insert(demodulator);

    m_manager.inc_ref(demodulator);
    m_manager.inc_ref(large);
    m_manager.inc_ref(small);
    m_demodulator2lhs_rhs.insert(demodulator, expr_pair(large, small));
}

void ufbv_rewriter::remove_fwd_idx(func_decl * f, quantifier * demodulator) {
    TRACE("demodulator_fwd", tout << "REMOVE: " << std::hex << (size_t)demodulator << std::endl; );

    fwd_idx_map::iterator it = m_fwd_idx.find_iterator(f);
    if (it != m_fwd_idx.end()) {
        demodulator2lhs_rhs::iterator fit = m_demodulator2lhs_rhs.find_iterator(demodulator);
        m_manager.dec_ref(fit->m_value.first);
        m_manager.dec_ref(fit->m_value.second);
        m_manager.dec_ref(demodulator);
        m_demodulator2lhs_rhs.erase(demodulator);
        it->m_value->erase(demodulator);
    } else {
        SASSERT(m_demodulator2lhs_rhs.contains(demodulator));
    }
}

bool ufbv_rewriter::check_fwd_idx_consistency() {
    for (fwd_idx_map::iterator it = m_fwd_idx.begin(); it != m_fwd_idx.end() ; it++ ) {
        quantifier_set * set = it->m_value;
        SASSERT(set);

        for (quantifier_set::iterator sit = set->begin(); sit != set->end(); sit++) {
            if (!m_demodulator2lhs_rhs.contains(*sit)) return false;
        }
    }

    return true;
}

void ufbv_rewriter::show_fwd_idx(std::ostream & out) {
    for (fwd_idx_map::iterator it = m_fwd_idx.begin(); it != m_fwd_idx.end() ; it++ ) {
        quantifier_set * set = it->m_value;
        SASSERT(!set);

        out << it->m_key->get_name() << ": " << std::endl;

        for (quantifier_set::iterator sit = set->begin(); sit != set->end(); sit++) {
            out << std::hex << (size_t)*sit << std::endl;
        }
    }

    out << "D2LR: " << std::endl;
    for (demodulator2lhs_rhs::iterator it = m_demodulator2lhs_rhs.begin(); it != m_demodulator2lhs_rhs.end() ; it++) {
        out << (size_t) it->m_key << std::endl;
    }
}

bool ufbv_rewriter::rewrite1(func_decl * f, ptr_vector<expr> & m_new_args, expr_ref & np) {
    fwd_idx_map::iterator it = m_fwd_idx.find_iterator(f);
    if (it != m_fwd_idx.end()) {
        TRACE("demodulator_bug", tout << "trying to rewrite: " << f->get_name() << " args:\n";
              for (unsigned i = 0; i < m_new_args.size(); i++) { tout << mk_pp(m_new_args[i], m_manager) << "\n"; });
        quantifier_set::iterator dit = it->m_value->begin();
        quantifier_set::iterator dend = it->m_value->end();
        for ( ; dit != dend ; dit++ ) {
            quantifier * d = *dit;

            SASSERT(m_demodulator2lhs_rhs.contains(d));
            expr_pair l_s;
            m_demodulator2lhs_rhs.find(d, l_s);
            app * large = to_app(l_s.first);

            if (large->get_num_args() != m_new_args.size())
                continue;

            TRACE("demodulator_bug", tout << "Matching with demodulator: " << mk_pp(d, m_manager) << std::endl; );

            SASSERT(large->get_decl() == f);

            if (m_match_subst(large, l_s.second, m_new_args.c_ptr(), np)) {
                TRACE("demodulator_bug", tout << "succeeded...\n" << mk_pp(l_s.second, m_manager) << "\n===>\n" << mk_pp(np, m_manager) << "\n";);
                return true;
            }
        }
    }

    return false;
}

bool ufbv_rewriter::rewrite_visit_children(app * a) {
    bool res=true;
    unsigned j = a->get_num_args();
    while (j > 0) {
        expr * e = a->get_arg(--j);
        if (!m_rewrite_cache.contains(e) || !m_rewrite_cache.get(e).second) {
            bool recursive = false;
            unsigned sz = m_rewrite_todo.size();
            expr * v = e;
            if (m_rewrite_cache.contains(e)) {
                expr_bool_pair const & ebp = m_rewrite_cache.get(e);
                if (ebp.second)
                    v = ebp.first;
            }
            for (unsigned i = sz; i > 0; i--) {
                if (m_rewrite_todo[i - 1] == v) {
                    recursive = true;
                    TRACE("demodulator", tout << "Detected demodulator cycle: " <<
                        mk_pp(a, m_manager) << " --> " << mk_pp(v, m_manager) << std::endl;);
                    m_rewrite_cache.insert(e, expr_bool_pair(v, true));
                    break;
                }
            }
            if (!recursive) {
                m_rewrite_todo.push_back(e);
                res = false;
            }
        }
    }
    return res;
}

void ufbv_rewriter::rewrite_cache(expr * e, expr * new_e, bool done) {
    m_rewrite_cache.insert(e, expr_bool_pair(new_e, done));
}

expr * ufbv_rewriter::rewrite(expr * n) {
    if (m_fwd_idx.empty())
        return n;

    TRACE("demodulator", tout << "rewrite: " << mk_pp(n, m_manager) << std::endl; );
    app * a;

    SASSERT(m_rewrite_todo.empty());
    m_rewrite_cache.reset();

    m_rewrite_todo.push_back(n);
    while (!m_rewrite_todo.empty()) {
        TRACE("demodulator_stack", tout << "STACK: " << std::endl;
              for ( unsigned i = 0; i<m_rewrite_todo.size(); i++)
                  tout << std::dec << i << ": " << std::hex << (size_t)m_rewrite_todo[i] <<
                  " = " << mk_pp(m_rewrite_todo[i], m_manager) << std::endl;
              );

        expr * e = m_rewrite_todo.back();
        expr * actual = e;

        if (m_rewrite_cache.contains(e)) {
            const expr_bool_pair &ebp = m_rewrite_cache.get(e);
            if (ebp.second) {
                m_rewrite_todo.pop_back();
                continue;
            }
            else {
                actual = ebp.first;
            }
        }

        switch (actual->get_kind()) {
        case AST_VAR:
            rewrite_cache(e, actual, true);
            m_rewrite_todo.pop_back();
            break;
        case AST_APP:
            a = to_app(actual);
            if (rewrite_visit_children(a)) {
                func_decl * f = a->get_decl();
                m_new_args.reset();
                unsigned num_args = a->get_num_args();
                bool all_untouched=true;
                for (unsigned i = 0 ; i < num_args ; i++ ) {
                    expr * o_child = a->get_arg(i);
                    expr * n_child;
                    SASSERT(m_rewrite_cache.contains(o_child) && m_rewrite_cache.get(o_child).second);
                    expr_bool_pair const & ebp = m_rewrite_cache.get(o_child);
                    n_child = ebp.first;
                    if (n_child != o_child)
                        all_untouched = false;
                    m_new_args.push_back(n_child);
                }
                expr_ref np(m_manager);
                if (rewrite1(f, m_new_args, np)) {
                    rewrite_cache(e, np, false);
                    // No pop.
                } else {
                    if(all_untouched) {
                        rewrite_cache(e, actual, true);
                    }
                    else {
                        expr_ref na(m_manager);
                        if (f->get_family_id() != m_manager.get_basic_family_id())
                            na = m_manager.mk_app(f, m_new_args.size(), m_new_args.c_ptr());
                        else
                            m_bsimp.mk_app(f, m_new_args.size(), m_new_args.c_ptr(), na);
                        TRACE("demodulator_bug", tout << "e:\n" << mk_pp(e, m_manager) << "\nnew_args: \n";
                              for (unsigned i = 0; i < m_new_args.size(); i++) { tout << mk_pp(m_new_args[i], m_manager) << "\n"; }
                              tout << "=====>\n";
                              tout << "na:\n " << mk_pp(na, m_manager) << "\n";);
                        rewrite_cache(e, na, true);
                    }
                    m_rewrite_todo.pop_back();
                }
            }
            break;
        case AST_QUANTIFIER: {
            expr * body = to_quantifier(actual)->get_expr();
            if (m_rewrite_cache.contains(body)) {
                const expr_bool_pair ebp = m_rewrite_cache.get(body);
                SASSERT(ebp.second);
                expr * new_body = ebp.first;
                quantifier_ref q(m_manager);
                q = m_manager.update_quantifier(to_quantifier(actual), new_body);
                m_new_exprs.push_back(q);
                expr_ref new_q = elim_unused_vars(m_manager, q, params_ref());
                m_new_exprs.push_back(new_q);
                rewrite_cache(e, new_q, true);
                m_rewrite_todo.pop_back();
            } else {
                m_rewrite_todo.push_back(body);
            }
            break;
        }
        default:
            UNREACHABLE();
        }
    }

    SASSERT(m_rewrite_cache.contains(n));
    const expr_bool_pair & ebp = m_rewrite_cache.get(n);
    SASSERT(ebp.second);
    expr * r = ebp.first;

    TRACE("demodulator", tout << "rewrite result: " << mk_pp(r, m_manager) << std::endl; );

    return r;
}

class ufbv_rewriter::add_back_idx_proc {
    back_idx_map & m_back_idx;
    expr *         m_expr;
public:
    add_back_idx_proc(back_idx_map & bi, expr * e):m_back_idx(bi),m_expr(e) {}
    void operator()(var * n) {}
    void operator()(quantifier * n) {}
    void operator()(app * n) {
        // We track only uninterpreted and constant functions.
        if (n->get_num_args()==0) return;
        SASSERT(m_expr && m_expr != (expr*) 0x00000003);
        func_decl * d=n->get_decl();
        if (d->get_family_id() == null_family_id) {
            back_idx_map::iterator it = m_back_idx.find_iterator(d);
            if (it != m_back_idx.end()) {
                SASSERT(it->m_value);
                it->m_value->insert(m_expr);
            } else {
                expr_set * e = alloc(expr_set);
                e->insert(m_expr);
                m_back_idx.insert(d, e);
            }
        }
    }
};

class ufbv_rewriter::remove_back_idx_proc {
    back_idx_map & m_back_idx;
    expr *         m_expr;
public:
    remove_back_idx_proc(back_idx_map & bi, expr * e):m_back_idx(bi),m_expr(e) {}
    void operator()(var * n) {}
    void operator()(quantifier * n) {}
    void operator()(app * n) {
        // We track only uninterpreted and constant functions.
        if (n->get_num_args()==0) return;
        func_decl * d=n->get_decl();
        if (d->get_family_id() == null_family_id) {
            back_idx_map::iterator it = m_back_idx.find_iterator(d);
            if (it != m_back_idx.end()) {
                SASSERT(it->m_value);
                it->m_value->remove(m_expr);
            }
        }
    }
};

void ufbv_rewriter::reschedule_processed(func_decl * f) {
    //use m_back_idx to find all formulas p in m_processed that contains f {
    back_idx_map::iterator it = m_back_idx.find_iterator(f);
    if (it != m_back_idx.end()) {
        SASSERT(it->m_value);
        expr_set temp;

        expr_set::iterator sit  = it->m_value->begin();
        expr_set::iterator send = it->m_value->end();
        for ( ; sit != send ; sit++ ) {
            expr * p = *sit;
            if (m_processed.contains(p))
              temp.insert(p);
        }

        sit  = temp.begin();
        send = temp.end();
        for ( ; sit != send; sit++) {
            expr * p = *sit;
            // remove p from m_processed and m_back_idx
            m_processed.remove(p);
            remove_back_idx_proc proc(m_back_idx, p); // this could change it->m_value, thus we need the `temp' set.
            for_each_expr(proc, p);
            // insert p into m_todo
            m_todo.push_back(p);
        }
    }
}

bool ufbv_rewriter::can_rewrite(expr * n, expr * lhs) {
    // this is a quick check, we just traverse d and check if there is an expression in d that is an instance of lhs of n'.
    // we cannot use the trick used for m_processed, since the main loop would not terminate.

    ptr_vector<expr> stack;
    expr *           curr;
    expr_mark        visited;

    stack.push_back(n);

    while (!stack.empty()) {
        curr = stack.back();

        if (visited.is_marked(curr)) {
            stack.pop_back();
            continue;
        }

        switch(curr->get_kind()) {
        case AST_VAR:
            visited.mark(curr, true);
            stack.pop_back();
            break;

        case AST_APP:
            if (for_each_expr_args(stack, visited, to_app(curr)->get_num_args(), to_app(curr)->get_args())) {
                if (m_match_subst(lhs, curr))
                    return true;
                visited.mark(curr, true);
                stack.pop_back();
            }
            break;

        case AST_QUANTIFIER:
            if (!for_each_expr_args(stack, visited, to_quantifier(curr)->get_num_patterns(),
                                    to_quantifier(curr)->get_patterns())) {
                break;
            }
            if (!for_each_expr_args(stack, visited, to_quantifier(curr)->get_num_no_patterns(),
                                    to_quantifier(curr)->get_no_patterns())) {
                break;
            }
            if (!visited.is_marked(to_quantifier(curr)->get_expr())) {
                stack.push_back(to_quantifier(curr)->get_expr());
                break;
            }

            stack.pop_back();
            break;
        default:
            UNREACHABLE();
        }
    }

    return false;
}

void ufbv_rewriter::reschedule_demodulators(func_decl * f, expr * lhs) {
    // use m_back_idx to find all demodulators d in m_fwd_idx that contains f {

    //ptr_vector<expr> to_remove;

    back_idx_map::iterator it = m_back_idx.find_iterator(f);
    if (it != m_back_idx.end()) {
        SASSERT(it->m_value);
        expr_set all_occurrences;
        expr_ref l(m_manager);

        expr_set::iterator esit = it->m_value->begin();
        expr_set::iterator esend = it->m_value->end();
        for ( ; esit != esend ; esit++)
          all_occurrences.insert(*esit);

        // Run over all f-demodulators
        esit = all_occurrences.begin();
        esend = all_occurrences.end();
        for ( ; esit != esend ; esit++ ) {
            expr * occ = *esit;

            if (!is_quantifier(occ))
                continue;

            // Use the fwd idx to find out whether this is a demodulator.
            demodulator2lhs_rhs::iterator d2lr_it = m_demodulator2lhs_rhs.find_iterator(to_quantifier(occ));
            if (d2lr_it != m_demodulator2lhs_rhs.end()) {
                l = d2lr_it->m_value.first;
                quantifier_ref d(m_manager);
                func_decl_ref df(m_manager);
                d = to_quantifier(occ);
                df = to_app(l)->get_decl();

                // Now we know there is an occurrence of f in d
                //   if n' can rewrite d {
                if (can_rewrite(d, lhs)) {
                    TRACE("demodulator", tout << "Rescheduling: " << std::endl << mk_pp(d, m_manager) << std::endl; );
                    //     remove d from m_fwd_idx
                    remove_fwd_idx(df, d);
                    //     remove d from m_back_idx
                    // just remember it here, because otherwise it and/or esit might become invalid?
                    // to_remove.insert(d);
                    remove_back_idx_proc proc(m_back_idx, d);
                    for_each_expr(proc, d);
                    //     insert d into m_todo
                    m_todo.push_back(d);
                }
            }
        }
    }

    //for (ptr_vector<expr>::iterator it = to_remove.begin(); it != to_remove.end(); it++) {
    //    expr * d = *it;
    //    remove_back_idx_proc proc(m_manager, m_back_idx, d);
    //    for_each_expr(proc, d);
    //}
}

void ufbv_rewriter::operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs) {
    if (m_manager.proofs_enabled()) {
        // Let us not waste time with proof production
        warning_msg("PRE_DEMODULATOR=true is not supported when proofs are enabled.");
        new_exprs.append(n, exprs);
        new_prs.append(n, prs);
        return;
    }

    TRACE("demodulator", tout << "before demodulator:\n";
                         for ( unsigned i = 0 ; i < n ; i++ )
                            tout << mk_pp(exprs[i], m_manager) << std::endl; );

    // Initially, m_todo contains all formulas. That is, it contains the argument exprs. m_fwd_idx, m_processed, m_back_idx are empty.
    unsigned max_vid = 0;
    for ( unsigned i = 0 ; i < n ; i++ ) {
        m_todo.push_back(exprs[i]);
        max_vid = std::max(max_vid, max_var_id(exprs[i]));
    }

    m_match_subst.reserve(max_vid);

    while (!m_todo.empty()) {
        // let n be the next formula in m_todo.
        expr_ref cur(m_manager);
        cur = m_todo.back();
        m_todo.pop_back();

        // rewrite cur using m_fwd_idx, and let n' be the result.
        expr * np = rewrite(cur);
        // at this point, it should be the case that there is no demodulator in m_fwd_idx that can rewrite n'.
        SASSERT(rewrite(np)==np);

        //    if (n' is not a demodulator) {
        expr_ref large(m_manager), small(m_manager);
        if (!is_demodulator(np, large, small)) {
            // insert n' into m_processed
            m_processed.insert(np);
            // update m_back_idx (traverse n' and for each uninterpreted function declaration f in n' add the entry f->n' to m_back_idx)
            add_back_idx_proc proc(m_back_idx, np);
            for_each_expr(proc, np);
        } else {
            // np is a demodulator that allows us to replace 'large' with 'small'.
            TRACE("demodulator", tout << "Found demodulator: " << std::endl;
                                 tout << mk_pp(large.get(), m_manager) << std::endl << " ---> " <<
                                      std::endl << mk_pp(small.get(), m_manager) << std::endl; );

            TRACE("demodulator_s", tout << "Found demodulator: " << std::endl;
                                   tout << to_app(large)->get_decl()->get_name() <<
                                        "[" << to_app(large)->get_depth() << "]" << " ---> ";
                                   if (is_app(small))
                                       tout << to_app(small)->get_decl()->get_name() <<
                                        "[" << to_app(small)->get_depth() << "]" << std::endl;
                                   else
                                       tout << mk_pp(small.get(), m_manager) << std::endl; );

            // let f be the top symbol of n'
            SASSERT(is_app(large));
            func_decl * f = to_app(large)->get_decl();

            reschedule_processed(f);
            reschedule_demodulators(f, large);

            // insert n' into m_fwd_idx
            insert_fwd_idx(large, small, to_quantifier(np));

            // update m_back_idx
            add_back_idx_proc proc(m_back_idx, np);
            for_each_expr(proc, np);
        }
    }

    // the result is the contents of m_processed + all demodulators in m_fwd_idx.
    obj_hashtable<expr>::iterator pit = m_processed.begin();
    obj_hashtable<expr>::iterator pend = m_processed.end();
    for ( ; pit != pend ; pit++ ) {
        new_exprs.push_back(*pit);
        TRACE("demodulator", tout << mk_pp(*pit, m_manager) << std::endl; );
    }

    fwd_idx_map::iterator fit = m_fwd_idx.begin();
    fwd_idx_map::iterator fend = m_fwd_idx.end();
    for ( ; fit != fend ; fit++ ) {
        if (fit->m_value) {
            quantifier_set::iterator dit = fit->m_value->begin();
            quantifier_set::iterator dend = fit->m_value->end();
            for ( ; dit != dend ; dit++ ) {
                expr * e = *dit;
                new_exprs.push_back(e);
                TRACE("demodulator", tout << mk_pp(*dit, m_manager) << std::endl; );
            }
        }
    }

    TRACE("demodulator", tout << "after demodulator:\n";
                         for ( unsigned i = 0 ; i < new_exprs.size() ; i++ )
                            tout << mk_pp(new_exprs[i].get(), m_manager) << std::endl; );
}


ufbv_rewriter::match_subst::match_subst(ast_manager & m):
    m_manager(m),
    m_subst(m) {
}

/**
   \brief Auxiliary functor used to implement optimization in match_args. See comment there.
*/
struct match_args_aux_proc {
    substitution &                               m_subst;
    struct no_match {};

    match_args_aux_proc(substitution & s):m_subst(s) {}

    void operator()(var * n) {
        expr_offset r;
        if (m_subst.find(n, 0, r)) {
            if (r.get_expr() != n) {
                SASSERT(r.get_offset() == 1);
                throw no_match();
            }
            else {
                m_subst.insert(n, 0, expr_offset(n, 1));
            }
        }
    }
    void operator()(quantifier * n) { throw no_match(); }
    void operator()(app * n) {}
};

bool ufbv_rewriter::match_subst::match_args(app * lhs, expr * const * args) {
    m_cache.reset();
    m_todo.reset();

    // fill todo-list, and perform quick success/failure tests
    m_all_args_eq = true;
    unsigned num_args = lhs->get_num_args();
    for (unsigned i = 0; i < num_args; i++) {
        expr * t_arg = lhs->get_arg(i);
        expr * i_arg = args[i];
        if (t_arg != i_arg)
            m_all_args_eq = false;
        if (is_app(t_arg) && is_app(i_arg) && to_app(t_arg)->get_decl() != to_app(i_arg)->get_decl()) {
            // quick failure...
            return false;
        }
        m_todo.push_back(expr_pair(t_arg, i_arg));
    }

    if (m_all_args_eq) {
        // quick success worked...
        return true;
    }

    m_subst.reset();

    while (!m_todo.empty()) {
        expr_pair const & p = m_todo.back();

        if (is_var(p.first)) {
            expr_offset r;
            if (m_subst.find(to_var(p.first), 0, r)) {
                if (r.get_expr() != p.second)
                    return false;
            }
            else {
                m_subst.insert(to_var(p.first), 0, expr_offset(p.second, 1));
            }
            m_todo.pop_back();
            continue;
        }

        if (is_var(p.second))
            return false;

        // we may have nested quantifiers.
        if (is_quantifier(p.first) || is_quantifier(p.second))
            return false;

        SASSERT(is_app(p.first) && is_app(p.second));

        if (to_app(p.first)->is_ground() && !to_app(p.second)->is_ground())
            return false;

        if (p.first == p.second && to_app(p.first)->is_ground()) {
            SASSERT(to_app(p.second)->is_ground());
            m_todo.pop_back();
            continue;
        }

        if (m_cache.contains(p)) {
            m_todo.pop_back();
            continue;
        }

        if (p.first == p.second) {
            // p.first and p.second is not ground...

            // Traverse p.first and check whether every variable X:0 in p.first
            //       1) is unbounded (then we bind X:0 -> X:1)
            //       2) or, is already bounded to X:1
            // If that is, the case, we execute:
            //     m_todo.pop_back();
            //     m_cache.insert(p);
            //     continue;
            // Otherwise
            //     return false;
            match_args_aux_proc proc(m_subst);
            try {
                for_each_expr(proc, p.first);
                // succeeded
                m_todo.pop_back();
                m_cache.insert(p);
                continue;
            }
            catch (match_args_aux_proc::no_match) {
                return false;
            }
        }

        app * n1 = to_app(p.first);
        app * n2 = to_app(p.second);

        if (n1->get_decl() != n2->get_decl())
            return false;

        unsigned num_args1 = n1->get_num_args();
        if (num_args1 != n2->get_num_args())
            return false;

        m_todo.pop_back();

        if (num_args1 == 0)
            continue;

        m_cache.insert(p);
        unsigned j = num_args1;
        while (j > 0) {
            --j;
            m_todo.push_back(expr_pair(n1->get_arg(j), n2->get_arg(j)));
        }
    }
    return true;
}


bool ufbv_rewriter::match_subst::operator()(app * lhs, expr * rhs, expr * const * args, expr_ref & new_rhs) {
    if (match_args(lhs, args)) {
        if (m_all_args_eq) {
            // quick success...
            new_rhs = rhs;
            return true;
        }
        unsigned deltas[2] = { 0, 0 };
        m_subst.apply(2, deltas, expr_offset(rhs, 0), new_rhs);
        return true;
    }
    return false;
}

bool ufbv_rewriter::match_subst::operator()(expr * t, expr * i) {
    m_cache.reset();
    m_todo.reset();
    if (is_var(t))
        return true;
    if (is_app(t) && is_app(i) && to_app(t)->get_decl() == to_app(i)->get_decl() && to_app(t)->get_num_args() == to_app(i)->get_num_args()) {
        return match_args(to_app(t), to_app(i)->get_args());
    }
    return false;
}
