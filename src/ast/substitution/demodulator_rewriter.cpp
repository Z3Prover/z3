/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    demodulator_rewriter.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-12.

Revision History:

    Christoph M. Wintersteiger (cwinter) 2010-04-21: Implementation
    Christoph M. Wintersteiger (cwinter) 2012-10-24: Moved from demodulator.h to ufbv_rewriter.h
    Nikolaj Bjorner (nbjorner) 2022-12-4: Moved to demodulator_rewriter.h

--*/

#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "ast/substitution/demodulator_rewriter.h"


class var_set_proc {
    uint_set & m_set;
public:
    var_set_proc(uint_set &s):m_set(s) {}
    void operator()(var * n) { m_set.insert(n->get_idx()); }
    void operator()(quantifier * n) {}
    void operator()(app * n) {}
};

int demodulator_util::is_subset(expr * e1, expr * e2) const {
    uint_set ev1, ev2;

    if (m.is_value(e1))
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

int demodulator_util::is_smaller(expr * e1, expr * e2) const {
    unsigned sz1 = 0, sz2 = 0;

    // values are always smaller!
    if (m.is_value(e1))
        return +1;
    else if (m.is_value(e2))
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
    sz1 = get_depth(e1);
    sz2 = get_depth(e2);

    return (sz1 == sz2) ?  0 :
           (sz1  < sz2) ? +1 :
                          -1 ;
}

bool demodulator_util::is_demodulator(expr * e, app_ref & large, expr_ref & small) const {
    if (!is_forall(e)) {
        return false;
    }
    expr * qe = to_quantifier(e)->get_expr();
    expr * lhs = nullptr, *rhs = nullptr, *n;
    if (m.is_eq(qe, lhs, rhs)) {
        int subset  = is_subset(lhs, rhs);
        int smaller = is_smaller(lhs, rhs);
        TRACE("demodulator", tout << "testing is_demodulator:\n"
              << mk_pp(lhs, m) << "\n"
              << mk_pp(rhs, m) << "\n"
              << "subset: " << subset << ", smaller: " << smaller << "\n";);
        // We only track uninterpreted functions, everything else is likely too expensive.
        if ((subset == +1 || subset == +2) && smaller == +1) {
            if (is_uninterp(rhs)) {
                large = to_app(rhs);
                small = lhs;
                return true;
            }
            // lhs = (not rhs) --> (not lhs) = rhs
            if (m.is_not(rhs, n) && is_uninterp(n)) {
                large = to_app(n);
                small = m.mk_not(lhs);
                return true;
            }
        }
        
        if ((subset == -1 || subset == +2) && smaller == -1) {
            if (is_uninterp(lhs)) {
                large = to_app(lhs);
                small = rhs;
                return true;
            }
            // (not lhs) = rhs --> lhs = (not rhs)
            if (m.is_not(lhs, n) && is_uninterp(n)) {
                large = to_app(n);
                small = m.mk_not(rhs);
                return true;
            }
        }        
    } 
    else if (m.is_not(qe, n) && is_app(n)) {
        // this is like (not (f ... )) --> (= (f ...) false)
        large = to_app(n);
        small = m.mk_false();
        return true;
    } 
    else if (is_uninterp(qe)) {
        // this is like (f ... ) --> (= (f ...) true)
        large = to_app(qe);
        small = m.mk_true();
        return true;
    }
    return false;
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

unsigned demodulator_util::max_var_id(expr* e) {
    max_var_id_proc proc;
    for_each_expr(proc, e);
    return proc.get_max();
}

unsigned demodulator_util::max_var_id(expr_ref_vector const& es) {
    max_var_id_proc proc;
    for (expr* e : es) 
        for_each_expr(proc, e);
    return proc.get_max();
}


// ------------------

demodulator_rewriter_util::demodulator_rewriter_util(ast_manager& m):
    m(m),
    m_th_rewriter(m),
    m_rewrite_todo(m),
    m_rewrite_cache(m),
    m_new_exprs(m),
    m_new_args(m)
{}

expr_ref demodulator_rewriter_util::rewrite(expr * n) {

    TRACE("demodulator", tout << "rewrite: " << mk_pp(n, m) << std::endl; );
    app * a;

    SASSERT(m_rewrite_todo.empty());
    m_new_exprs.reset();
    m_rewrite_cache.reset();

    m_rewrite_todo.push_back(n);
    while (!m_rewrite_todo.empty()) {
        TRACE("demodulator_stack", tout << "STACK: " << std::endl;
              for (unsigned i = 0; i < m_rewrite_todo.size(); i++)
                  tout << std::dec << i << ": " << std::hex << (size_t)m_rewrite_todo[i] <<
                  " = " << mk_pp(m_rewrite_todo[i], m) << std::endl;
              );

        expr * e = m_rewrite_todo.back();
        expr_ref actual(e, m);

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
                bool all_untouched = true;
                for (expr* o_child : *a) {
                    expr * n_child;
                    SASSERT(m_rewrite_cache.contains(o_child) && m_rewrite_cache.get(o_child).second);
                    expr_bool_pair const & ebp = m_rewrite_cache.get(o_child);
                    n_child = ebp.first;
                    if (n_child != o_child)
                        all_untouched = false;
                    m_new_args.push_back(n_child);
                }
                expr_ref np(m);
                if (m_rewrite1(f, m_new_args, np)) {
                    rewrite_cache(e, np, false);
                    // No pop.
                } 
                else {
                    if (all_untouched) {
                        rewrite_cache(e, actual, true);
                    }
                    else {
                        expr_ref na(m);
                        na = m_th_rewriter.mk_app(f, m_new_args);
                        TRACE("demodulator_bug", tout << "e:\n" << mk_pp(e, m) << "\nnew_args: \n";
                              tout << m_new_args << "\n";
                              tout << "=====>\n";
                              tout << "na:\n " << na << "\n";);
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
                quantifier_ref q(m);
                q = m.update_quantifier(to_quantifier(actual), new_body);
                m_new_exprs.push_back(q);
                expr_ref new_q = elim_unused_vars(m, q, params_ref());
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

    TRACE("demodulator", tout << "rewrite result: " << mk_pp(r, m) << std::endl; );

    return expr_ref(r, m);
}

bool demodulator_rewriter_util::rewrite_visit_children(app * a) {
    bool res = true;
    for (expr* e : *a) {
        if (m_rewrite_cache.contains(e) && m_rewrite_cache.get(e).second)
            continue;
        bool recursive = false;
        expr * v = e;
        if (m_rewrite_cache.contains(e)) {
            auto const & [t, marked] = m_rewrite_cache.get(e);
            if (marked) 
                v = t;
        }
        for (expr* t : m_rewrite_todo) {
            if (t == v) {
                recursive = true;
                TRACE("demodulator", tout << "Detected demodulator cycle: " <<
                      mk_pp(a, m) << " --> " << mk_pp(v, m) << std::endl;);
                rewrite_cache(e, v, true);
                break;
            }
        }
        if (!recursive) {
            m_rewrite_todo.push_back(e);
            res = false;
        }
    }
    return res;
}

void demodulator_rewriter_util::rewrite_cache(expr * e, expr * new_e, bool done) {
    m_rewrite_cache.insert(e, expr_bool_pair(new_e, done));
}



// ------------------

demodulator_rewriter::demodulator_rewriter(ast_manager & m):
    m(m),
    m_match_subst(m),
    m_util(m),
    m_bsimp(m),
    m_todo(m),
    m_in_processed(m),
    m_new_args(m), 
    m_rewrite_todo(m),
    m_rewrite_cache(m),
    m_new_exprs(m) {
    params_ref p;
    p.set_bool("elim_and", true);
    m_bsimp.updt_params(p);
}

demodulator_rewriter::~demodulator_rewriter() {
    reset_dealloc_values(m_fwd_idx);
    reset_dealloc_values(m_back_idx);
    for (auto & kv : m_demodulator2lhs_rhs) {
        m.dec_ref(kv.m_key);
        m.dec_ref(kv.m_value.first);
        m.dec_ref(kv.m_value.second);
    }
}



void demodulator_rewriter::insert_fwd_idx(app * large, expr * small, quantifier * demodulator) {
    SASSERT(demodulator);
    SASSERT(large && small);
    TRACE("demodulator_fwd", tout << "INSERT: " << mk_pp(demodulator, m) << std::endl; );

    func_decl * fd = to_app(large)->get_decl();

    quantifier_set * qs;
    if (!m_fwd_idx.find(fd, qs)) {
        qs = alloc(quantifier_set, 1);
        m_fwd_idx.insert(fd, qs);
    }

    SASSERT(qs);
    qs->insert(demodulator);

    m.inc_ref(demodulator);
    m.inc_ref(large);
    m.inc_ref(small);
    m_demodulator2lhs_rhs.insert(demodulator, app_expr_pair(large, small));
}

void demodulator_rewriter::remove_fwd_idx(func_decl * f, quantifier * demodulator) {
    TRACE("demodulator_fwd", tout << "REMOVE: " << std::hex << (size_t)demodulator << std::endl; );

    quantifier_set* qs;
    if (m_fwd_idx.find(f, qs)) {
        auto [lhs, rhs] = m_demodulator2lhs_rhs[demodulator];
        m_demodulator2lhs_rhs.erase(demodulator);
        qs->erase(demodulator);
        m.dec_ref(lhs);
        m.dec_ref(rhs);
        m.dec_ref(demodulator);
    } else {
        SASSERT(m_demodulator2lhs_rhs.contains(demodulator));
    }
}

bool demodulator_rewriter::check_fwd_idx_consistency() {
    for (auto & [k, set] : m_fwd_idx) {
        SASSERT(set);
        for (auto e : *set) 
            if (!m_demodulator2lhs_rhs.contains(e)) 
                return false;
    }
    return true;
}

void demodulator_rewriter::show_fwd_idx(std::ostream & out) {
    for (auto & [k, set] : m_fwd_idx) {
        out << k->get_name() << ": " << std::endl;
        if (set) 
            for (auto e : *set) 
                out << std::hex << (size_t)e << std::endl;
    }

    out << "D2LR: " << std::endl;
    for (auto & [k, v] : m_demodulator2lhs_rhs) {
        out << (size_t) k << std::endl;
    }
}

bool demodulator_rewriter::rewrite1(func_decl * f, expr_ref_vector const & args, expr_ref & np) {
    quantifier_set* set;
    if (!m_fwd_idx.find(f, set))
        return false;
    TRACE("demodulator_bug", tout << "trying to rewrite: " << f->get_name() << " args:\n";
          tout << m_new_args << "\n";);

    for (quantifier* d : *set) {

        auto const& [lhs, rhs] = m_demodulator2lhs_rhs[d];
        
        if (lhs->get_num_args() != args.size())
            continue;
        
        TRACE("demodulator_bug", tout << "Matching with demodulator: " << mk_pp(d, m) << std::endl; );
        
        SASSERT(lhs->get_decl() == f);
        
        if (m_match_subst(lhs, rhs, args.data(), np)) {
            TRACE("demodulator_bug", tout << "succeeded...\n" << mk_pp(rhs, m) << "\n===>\n" << mk_pp(np, m) << "\n";);
            m_new_exprs.push_back(np);
            return true;
        }
    }

    return false;
}

bool demodulator_rewriter::rewrite_visit_children(app * a) {
    bool res = true;
    for (expr* e : *a) {
        if (m_rewrite_cache.contains(e) && m_rewrite_cache.get(e).second)
            continue;
        bool recursive = false;
        expr * v = e;
        if (m_rewrite_cache.contains(e)) {
            auto const & [t, marked] = m_rewrite_cache.get(e);
            if (marked) 
                v = t;
        }
        for (expr* t : m_rewrite_todo) {
            if (t == v) {
                recursive = true;
                TRACE("demodulator", tout << "Detected demodulator cycle: " <<
                      mk_pp(a, m) << " --> " << mk_pp(v, m) << std::endl;);
                rewrite_cache(e, v, true);
                break;
            }
        }
        if (!recursive) {
            m_rewrite_todo.push_back(e);
            res = false;
        }
    }
    return res;
}

void demodulator_rewriter::rewrite_cache(expr * e, expr * new_e, bool done) {
    m_rewrite_cache.insert(e, expr_bool_pair(new_e, done));
}

expr * demodulator_rewriter::rewrite(expr * n) {
    if (m_fwd_idx.empty())
        return n;

    TRACE("demodulator", tout << "rewrite: " << mk_pp(n, m) << std::endl; );
    app * a;

    SASSERT(m_rewrite_todo.empty());
    m_rewrite_cache.reset();

    m_rewrite_todo.push_back(n);
    while (!m_rewrite_todo.empty()) {
        TRACE("demodulator_stack", tout << "STACK: " << std::endl;
              for (unsigned i = 0; i < m_rewrite_todo.size(); i++)
                  tout << std::dec << i << ": " << std::hex << (size_t)m_rewrite_todo[i] <<
                  " = " << mk_pp(m_rewrite_todo[i], m) << std::endl;
              );

        expr * e = m_rewrite_todo.back();
        expr_ref actual(e, m);

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
                bool all_untouched = true;
                for (expr* o_child : *a) {
                    expr * n_child;
                    SASSERT(m_rewrite_cache.contains(o_child) && m_rewrite_cache.get(o_child).second);
                    expr_bool_pair const & ebp = m_rewrite_cache.get(o_child);
                    n_child = ebp.first;
                    if (n_child != o_child)
                        all_untouched = false;
                    m_new_args.push_back(n_child);
                }
                expr_ref np(m);
                if (rewrite1(f, m_new_args, np)) {
                    rewrite_cache(e, np, false);
                    // No pop.
                } 
                else {
                    if (all_untouched) {
                        rewrite_cache(e, actual, true);
                    }
                    else {
                        expr_ref na(m);
                        if (f->get_family_id() != m.get_basic_family_id())
                            na = m.mk_app(f, m_new_args);
                        else
                            m_bsimp.mk_app(f, m_new_args.size(), m_new_args.data(), na);
                        TRACE("demodulator_bug", tout << "e:\n" << mk_pp(e, m) << "\nnew_args: \n";
                              tout << m_new_args << "\n";
                              tout << "=====>\n";
                              tout << "na:\n " << na << "\n";);
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
                quantifier_ref q(m);
                q = m.update_quantifier(to_quantifier(actual), new_body);
                m_new_exprs.push_back(q);
                expr_ref new_q = elim_unused_vars(m, q, params_ref());
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

    TRACE("demodulator", tout << "rewrite result: " << mk_pp(r, m) << std::endl; );

    return r;
}

class demodulator_rewriter::add_back_idx_proc {
    back_idx_map & m_back_idx;
    expr *         m_expr;
public:
    add_back_idx_proc(back_idx_map & bi, expr * e):m_back_idx(bi),m_expr(e) {}
    void operator()(var * n) {}
    void operator()(quantifier * n) {}
    void operator()(app * n) {
        // We track only uninterpreted functions.
        if (n->get_num_args() == 0) 
            return;
        SASSERT(m_expr && m_expr != (expr*) 0x00000003);
        func_decl * d = n->get_decl();
        if (d->get_family_id() != null_family_id) 
            return;
        expr_set* set = nullptr;
        if (!m_back_idx.find(d, set)) {
            set = alloc(expr_set);
            m_back_idx.insert(d, set);
        }
        set->insert(m_expr);        
    }
};

class demodulator_rewriter::remove_back_idx_proc {
    back_idx_map & m_back_idx;
    expr *         m_expr;
public:
    remove_back_idx_proc(back_idx_map & bi, expr * e):m_back_idx(bi),m_expr(e) {}
    void operator()(var * n) {}
    void operator()(quantifier * n) {}
    void operator()(app * n) {
        // We track only uninterpreted  functions.
        if (n->get_num_args() == 0) 
            return;
        func_decl * d = n->get_decl();
        if (d->get_family_id() != null_family_id) 
            return;
        expr_set* set = nullptr;
        if (m_back_idx.find(d, set)) 
            set->remove(m_expr);
    }
};


void demodulator_rewriter::insert_bwd_idx(expr* e) {
    add_back_idx_proc proc(m_back_idx, e);
    for_each_expr(proc, e);
}

void demodulator_rewriter::remove_bwd_idx(expr* e) {
    remove_back_idx_proc proc(m_back_idx, e); 
    for_each_expr(proc, e);
}

void demodulator_rewriter::reschedule_processed(func_decl * f) {
    //use m_back_idx to find all formulas p in m_processed that contains f {
    expr_set* set = nullptr;
    if (!m_back_idx.find(f, set)) 
        return;
    SASSERT(set);
    expr_set temp;

    for (expr* p : *set) 
        if (m_processed.contains(p))
              temp.insert(p);

    for (expr * p : temp) {
        // remove p from m_processed and m_back_idx
        m_processed.remove(p);
        // this could change `set', thus we need the `temp' set.
        remove_bwd_idx(p);
        // insert p into m_todo
        m_todo.push_back(p);
    }
}

void demodulator_rewriter::reschedule_demodulators(func_decl * f, expr * lhs) {
    // use m_back_idx to find all demodulators d in m_fwd_idx that contains f {


    expr_set* set = nullptr;
    if (!m_back_idx.find(f, set))
        return;
    SASSERT(set);
    expr_set all_occurrences;
    app_ref l(m);

    for (auto s : *set) 
        all_occurrences.insert(s);
    
    // Run over all f-demodulators
    for (expr* occ : all_occurrences) {
        
        if (!is_quantifier(occ))
            continue;
        quantifier* qe = to_quantifier(occ);
        
        // Use the fwd idx to find out whether this is a demodulator.
        app_expr_pair p;
        if (!m_demodulator2lhs_rhs.find(qe, p)) 
            continue;

        l = p.first;
        quantifier_ref d(qe, m);
        func_decl_ref df(l->get_decl(), m);
            
        // Now we know there is an occurrence of f in d
        if (!m_match_subst.can_rewrite(d, lhs)) 
            continue;

        TRACE("demodulator", tout << "Rescheduling: " << std::endl << mk_pp(d, m) << std::endl);

        remove_fwd_idx(df, d);
        remove_bwd_idx(d);
        m_todo.push_back(d);        
    }
}

void demodulator_rewriter::operator()(expr_ref_vector const& exprs,
                                      expr_ref_vector & new_exprs) {

    TRACE("demodulator", tout << "before demodulator:\n" << exprs);

    // Initially, m_todo contains all formulas. That is, it contains the argument exprs. m_fwd_idx, m_processed, m_back_idx are empty.
    for (expr* e : exprs) 
        m_todo.push_back(e);

    m_match_subst.reserve(m_util.max_var_id(exprs));

    while (!m_todo.empty()) {
        // let n be the next formula in m_todo.
        expr_ref cur(m);
        cur = m_todo.back();
        m_todo.pop_back();

        // rewrite cur using m_fwd_idx, and let n' be the result.
        expr_ref np(rewrite(cur), m);
        // at this point, it should be the case that there is no demodulator in m_fwd_idx that can rewrite n'.
        // unless there is a demodulator cycle
        // SASSERT(rewrite(np)==np);

        app_ref large(m);
        expr_ref small(m);
        if (!m_util.is_demodulator(np, large, small)) {
            // insert n' into m_processed
            m_processed.insert(np);
            m_in_processed.push_back(np);
            // update m_back_idx (traverse n' and for each uninterpreted function declaration f in n' add the entry f->n' to m_back_idx)
            insert_bwd_idx(np);
        } 
        else {
            // np is a demodulator that allows us to replace 'large' with 'small'.
            TRACE("demodulator", tout << "Found demodulator:\n" << large << "\n ---> " << small << "\n");

            // let f be the top symbol of n'
            func_decl * f = large->get_decl();

            reschedule_processed(f);
            reschedule_demodulators(f, large);

            // insert n' into m_fwd_idx
            insert_fwd_idx(large, small, to_quantifier(np));

            // update m_back_idx
            insert_bwd_idx(np);
        }
    }

    // the result is the contents of m_processed + all demodulators in m_fwd_idx.
    for (expr* e : m_processed) {
        new_exprs.push_back(e);
        TRACE("demodulator", tout << mk_pp(e, m) << std::endl; );
    }

    for (auto const& [k, set] : m_fwd_idx) {
        if (set) {
            for (expr* e : *set) 
                new_exprs.push_back(e);
            TRACE("demodulator", for (expr* e : *set) tout << mk_pp(e, m) << std::endl; );
        }
    }

    TRACE("demodulator", tout << "after demodulator:\n" << new_exprs << "\n";);
}


demodulator_match_subst::demodulator_match_subst(ast_manager & m):
    m_subst(m) {
}

bool demodulator_match_subst::can_rewrite(expr* n, expr* lhs) {
    // this is a quick check, we just traverse d and check if there is an expression in d that is an instance of lhs of n'.
    // we cannot use the trick used for m_processed, since the main loop would not terminate.
    ptr_vector<expr> stack;
    expr* curr;
    expr_mark        visited;

    stack.push_back(n);
    while (!stack.empty()) {
        curr = stack.back();
        if (visited.is_marked(curr)) {
            stack.pop_back();
            continue;
        }
        switch (curr->get_kind()) {
        case AST_VAR:
            visited.mark(curr, true);
            stack.pop_back();
            break;
        case AST_APP:
            if (for_each_expr_args(stack, visited, to_app(curr)->get_num_args(), to_app(curr)->get_args())) {
                if ((*this)(lhs, curr))
                    return true;
                visited.mark(curr, true);
                stack.pop_back();
            }
            break;
        case AST_QUANTIFIER:
            if (visited.is_marked(to_quantifier(curr)->get_expr()))
                stack.pop_back();
            else
                stack.push_back(to_quantifier(curr)->get_expr());
            break;
        default:
            UNREACHABLE();
        }
    }
    return false;
}

/**
   \brief Auxiliary functor used to implement optimization in match_args. See comment there.
*/
struct match_args_aux_proc {
    substitution &                               m_subst;
    struct no_match : public std::exception {};

    match_args_aux_proc(substitution & s):m_subst(s) {}

    void operator()(var * n) {
        expr_offset r;
        if (m_subst.find(n, 0, r)) {
            if (r.get_expr() != n) {
                SASSERT(r.get_offset() == 1);
                throw no_match();
            }
        }
        else 
            m_subst.insert(n, 0, expr_offset(n, 1));        
    }
    void operator()(quantifier * n) { throw no_match(); }
    void operator()(app * n) {}
};

bool demodulator_match_subst::match_args(app * lhs, expr * const * args) {
    m_cache.reset();
    m_todo.reset();

    auto fill_commutative = [&](app* lhs, expr * const* args) {
        if (!lhs->get_decl()->is_commutative())
            return false;
        if (lhs->get_num_args() != 2)
            return false;
        expr* l1 = lhs->get_arg(0);
        expr* l2 = lhs->get_arg(1);
        expr* r1 = args[0];
        expr* r2 = args[1];
        
        if (is_app(l1) && is_app(r1) && to_app(l1)->get_decl() != to_app(r1)->get_decl()) {
            m_all_args_eq = false;
            m_todo.push_back(expr_pair(l1, r2));
            m_todo.push_back(expr_pair(l2, r1));
            return true;
        }
        if (is_app(l2) && is_app(r2) && to_app(l2)->get_decl() != to_app(r2)->get_decl()) {
            m_all_args_eq = false;
            m_todo.push_back(expr_pair(l1, r2));
            m_todo.push_back(expr_pair(l2, r1));
            return true;
        }
        return false;
    };
    // fill todo-list, and perform quick success/failure tests
    m_all_args_eq = true;
    unsigned num_args = lhs->get_num_args();
    if (!fill_commutative(lhs, args)) {
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
    }

    if (m_all_args_eq) {
        // quick success worked...
        return true;
    }

    m_subst.reset();

    while (!m_todo.empty()) {
        auto const & [a, b] = m_todo.back();

        if (is_var(a)) {
            expr_offset r;
            if (m_subst.find(to_var(a), 0, r)) {
                if (r.get_expr() != b)
                    return false;
            }
            else {
                m_subst.insert(to_var(a), 0, expr_offset(b, 1));
            }
            m_todo.pop_back();
            continue;
        }

        if (is_var(b))
            return false;

        // we may have nested quantifiers.
        if (is_quantifier(a) || is_quantifier(b))
            return false;

        SASSERT(is_app(a) && is_app(b));

        if (to_app(a)->is_ground() && !to_app(b)->is_ground())
            return false;

        if (a == b && to_app(a)->is_ground()) {
            m_todo.pop_back();
            continue;
        }

        if (m_cache.contains(expr_pair(a, b))) {
            m_todo.pop_back();
            continue;
        }

        if (a == b) {
            // a and b is not ground...

            // Traverse a and check whether every variable X:0 in a
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
                for_each_expr(proc, a);
                // succeeded
                m_todo.pop_back();
                m_cache.insert(expr_pair(a, b));
                continue;
            }
            catch (const match_args_aux_proc::no_match &) {
                return false;
            }
        }

        app * n1 = to_app(a);
        app * n2 = to_app(b);

        if (n1->get_decl() != n2->get_decl())
            return false;

        unsigned num_args1 = n1->get_num_args();
        if (num_args1 != n2->get_num_args())
            return false;

        m_todo.pop_back();

        if (num_args1 == 0)
            continue;

        m_cache.insert(expr_pair(a, b));
 
        if (fill_commutative(n1, n2->get_args())) 
            continue;

        for (unsigned j = num_args1; j-- > 0; ) 
            m_todo.push_back(expr_pair(n1->get_arg(j), n2->get_arg(j)));
    }
    return true;
}


bool demodulator_match_subst::operator()(app * lhs, expr * rhs, expr * const * args, expr_ref & new_rhs) {
    
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

bool demodulator_match_subst::operator()(expr * t, expr * i) {
    m_cache.reset();
    m_todo.reset();
    if (is_var(t))
        return true;
    if (is_app(t) && is_app(i) && 
        to_app(t)->get_decl() == to_app(i)->get_decl() && 
        to_app(t)->get_num_args() == to_app(i)->get_num_args()) {
        return match_args(to_app(t), to_app(i)->get_args());
    }
    return false;
}
