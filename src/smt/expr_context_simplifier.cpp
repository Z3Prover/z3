/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    expr_context_simplifier.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2008-06-03

Revision History:

--*/

#include "expr_context_simplifier.h"
#include "ast_pp.h"
#include "obj_hashtable.h"
#include "smt_kernel.h"
#include "for_each_expr.h"

// table lookup before/after simplification.

expr_context_simplifier::expr_context_simplifier(ast_manager& m):
    m_manager(m), m_arith(m), m_trail(m), m_simp(m), m_forward(true) {}

void expr_context_simplifier::reduce(expr * m, expr_ref & result) {
    expr_ref tmp(m_manager);
    m_mark.reset();
    unsigned trail_size = m_trail.size();
    m_forward = true;
    reduce_rec(m, tmp);
    m_mark.reset();
    m_forward = false;
    reduce_rec(tmp.get(), result);
    clean_trail(trail_size);
}

void expr_context_simplifier::reduce_fix(expr * m, expr_ref & result) {
    expr_ref tmp(m_manager);
    result = m;
    do {
        tmp = result.get();
        reduce(tmp.get(), result);
    }
    while (tmp.get() != result.get());
}

void expr_context_simplifier::reduce_rec(expr * m, expr_ref & result) {
    //
    // reduce expr in context evaluation.
    //
    bool polarity;
    if (m_context.find(m, polarity)) {
        result = polarity ? m_manager.mk_true() : m_manager.mk_false();
    }
    else if (m_mark.is_marked(m) && !m_manager.is_not(m)) {
        result = m;
    }
    else if (is_quantifier(m)) {
        reduce_rec(to_quantifier(m), result);
        m_mark.mark(m, true);
    }
    else if (is_app(m)) {
        reduce_rec(to_app(m), result);
        m_mark.mark(m, true);
    }
    else if (is_var(m)) {
        result = m;
        m_mark.mark(m, true);
    }
    else {
        UNREACHABLE();
        result = m;
    }
}

void expr_context_simplifier::reduce_rec(quantifier* q, expr_ref & result) {
    result = q;

#if 0
    //
    // The context assumes that asserted expressions are in NNF with
    // respect to the quantifier occurrences.
    // This can be disabled if the strong context simplifier
    // is called from the API over the Z3_simplify method.
    //
    expr_context_simplifier nested(m_manager);
    expr_ref body_r(m_manager);
    nested.reduce(q->get_expr(), body_r);
    if (body_r.get() != q->get_expr()) {
        result = m_manager.update_quantifier(q, body_r.get());
    }
    else {
        result = q;
    }
#endif
}

void expr_context_simplifier::reduce_rec(app * a, expr_ref & result) {    
    if (m_manager.get_basic_family_id() == a->get_family_id()) {
        switch(a->get_decl_kind()) {
        case OP_AND: 
            reduce_and(a->get_num_args(), a->get_args(), result);
            return;
        case OP_OR:
            reduce_or(a->get_num_args(), a->get_args(), result);
            return;
        case OP_IFF: {
            expr_ref tmp1(m_manager), tmp2(m_manager);
            reduce_rec(a->get_arg(0), tmp1);
            reduce_rec(a->get_arg(1), tmp2);
            m_simp.mk_iff(tmp1.get(), tmp2.get(), result);
            return;
        }
        case OP_XOR: {
            expr_ref tmp1(m_manager), tmp2(m_manager);
            reduce_rec(a->get_arg(0), tmp1);
            reduce_rec(a->get_arg(1), tmp2);
            m_simp.mk_xor(tmp1.get(), tmp2.get(), result);
            return;
        }
        case OP_NOT: {
            expr_ref tmp(m_manager);
            reduce_rec(a->get_arg(0), tmp);
            m_simp.mk_not(tmp.get(), result);
            return;
        }
        case OP_IMPLIES: {
            app_ref tmp(m_manager);
            tmp = m_manager.mk_not(a->get_arg(0));
            expr* args[2] = { tmp.get(), a->get_arg(1) };
            reduce_or(2, args, result);
            return;
        }
        case OP_ITE: {
            expr_ref tmp(m_manager), tmp1(m_manager), tmp2(m_manager);
            reduce_rec(a->get_arg(0), tmp);
            if (is_true(tmp.get())) {
                reduce_rec(a->get_arg(1), result);
            }
            else if (is_false(tmp.get())) {
                reduce_rec(a->get_arg(2), result);
            }
            else {
                unsigned trail_size = m_trail.size();
                insert_context(tmp.get(), true);
                reduce_rec(a->get_arg(1), tmp1);
                clean_trail(trail_size);
                
                insert_context(tmp.get(), false);
                reduce_rec(a->get_arg(2), tmp2);
                clean_trail(trail_size);
                
                m_simp.mk_ite(tmp.get(), tmp1.get(), tmp2.get(), result);
            }
            return;
        }
        default:
            break;
        }
    }

    expr_ref_vector args(m_manager);
    for (unsigned i = 0; i < a->get_num_args(); ++i) {
        expr_ref tmp(m_manager);
        reduce_rec(a->get_arg(i), tmp);
        args.push_back(tmp.get());
    }
    result = m_manager.mk_app(a->get_decl(), args.size(), args.c_ptr());
}

void expr_context_simplifier::clean_trail(unsigned old_lim) {
    for (unsigned i = m_trail.size(); i > old_lim; ) {
        --i;
        m_context.erase(m_trail[i].get());
    }
    m_trail.resize(old_lim);
}

void expr_context_simplifier::insert_context(expr* e, bool polarity) {
    TRACE("expr_context_simplifier", tout << mk_pp(e, m_manager) << "\n";);
    if (m_manager.is_not(e)) {
        e = to_app(e)->get_arg(0);
        polarity = !polarity;
    }
    if (!m_context.contains(e)) {
        m_context.insert(e, polarity);
        m_trail.push_back(e);
    }
}

bool expr_context_simplifier::insert_arg(bool is_and, expr* arg, expr_ref_vector& args) {
    expr_ref tmp(m_manager);
    reduce_rec(arg, tmp);
    TRACE("expr_context_simplifier", tout << mk_pp(arg, m_manager) << " -> " << mk_pp(tmp.get(), m_manager) << "\n";);    
    if (is_true(tmp.get()) && is_and) {
        // skip.
    }
    else if (is_false(tmp.get()) && !is_and) {
        // skip.
    }
    else if (is_false(tmp.get()) && is_and) {
        return true;
    }
    else if (is_true(tmp.get()) && !is_and) {
        return true;
    }
    else {
        insert_context(tmp.get(), is_and);
        if (arg != tmp.get()) {
            insert_context(arg, is_and);       // allow to also use un-simplified version
        }
        args.push_back(tmp.get());
    }
    return false;
}

void expr_context_simplifier::reduce_and_or(bool is_and, unsigned num_args, expr * const* args, expr_ref & result) {
    expr_ref tmp(m_manager);
    expr_ref_vector args1(m_manager);
    unsigned trail_size = m_trail.size();

    if (m_forward) {
        for (unsigned i = 0; i < num_args; ++i) {
            if (insert_arg(is_and, args[i], args1)) {
                clean_trail(trail_size);
                result = is_and?m_manager.mk_false():m_manager.mk_true();
                return;
            }
        }
    }
    else {
        for (unsigned i = num_args; i > 0; ) {
            --i;
            if (insert_arg(is_and, args[i], args1)) {
                clean_trail(trail_size);
                result = is_and?m_manager.mk_false():m_manager.mk_true();
                return;
            }
        }
    }
    clean_trail(trail_size);

    if (is_and) {
        m_simp.mk_and(args1.size(), args1.c_ptr(), result);
    }
    else {
        m_simp.mk_or(args1.size(), args1.c_ptr(), result);
    }
}

void expr_context_simplifier::reduce_and(unsigned num_args, expr * const* args, expr_ref & result) {
    reduce_and_or(true, num_args, args, result);
}

void expr_context_simplifier::reduce_or(unsigned num_args, expr * const* args, expr_ref & result) {
    reduce_and_or(false, num_args, args, result);
}

bool expr_context_simplifier::is_true(expr* e) const {
    return 
        m_manager.is_true(e) ||
        (m_manager.is_not(e) && m_manager.is_false(to_app(e)->get_arg(0)));
}

bool expr_context_simplifier::is_false(expr* e) const {
    return 
        m_manager.is_false(e) ||
        (m_manager.is_not(e) && m_manager.is_true(to_app(e)->get_arg(0)));
}


//
// This routine performs strong context simplification.
// It replaces sub-formulas by a fresh name
// and checks if the original formula is equivalent 
// to the resulting formula if the fresh name is set to
// true or false.
// otherwise it recursively expands the definition of the
// fresh name to match the original formula.
//
//  assert ! (fml <=> n)
//
//for (fml', n')
//  check visited
//  check n'
//  check !n'
//  if each a is visited, 
//     fml' by fml'[a/a'] 
//     pop_scope
//  ow,
//  let a be a non-visited argument.
//  push_scope
//  push (a, n'')
//  assert (n' <=> f(visited_args, n'', visited_or_non_visited_args)) 
// 
// The implementation avoid the stack. It uses the following vectors: 
//  todo  - DFS stack
//  names - collection of fresh names.
//  is_checked - Boolean to control if contextual equivalence with T or F was checked.
//  parent_ids - stack of IDs used to identify path down to expression on first visit.
//  self_ids   - stack of IDs used to identify path down to children on first visit.
//  The parent_ids, self_ids stacks are used to ensure that caching results can be done
//  in a context dependent way. A cached result is only valid for simplification if
//  it occurs in the context (on the path) where it was inserted.
// 

expr_strong_context_simplifier::expr_strong_context_simplifier(smt_params& p, ast_manager& m): 
    m_manager(m), m_arith(m), m_fn(0,m), m_solver(m, p) {
    sort* i_sort = m_arith.mk_int();
    m_fn = m.mk_func_decl(symbol(0xbeef101), i_sort, m.mk_bool_sort());
}


void expr_strong_context_simplifier::simplify_basic(expr* fml, expr_ref& result) {
    ast_manager& m = m_manager;
    //
    // The context assumes that asserted expressions are in NNF with
    // respect to the quantifier occurrences.
    // This can be disabled if the strong context simplifier
    // is called from the API over the Z3_simplify method.
    //
    if (!m.is_bool(fml) || has_quantifiers(fml)) {
        result = fml;
        return;
    }                                                

    ptr_vector<expr> todo;
    ptr_vector<expr> names;
    svector<bool>    is_checked;
    svector<unsigned> parent_ids, self_ids;
    expr_ref_vector  fresh_vars(m);
    expr_ref_vector trail(m);
    obj_map<expr,std::pair<unsigned, expr*> > cache;
    m_solver.push();
    unsigned id = 1;
    expr* n = m.mk_app(m_fn, m_arith.mk_numeral(rational(id++), true));
    expr* r, *n2;
    lbool is_sat;
    unsigned path_id = 0, self_pos = 0;
    app * a;
    unsigned sz;
    trail.push_back(n);
    
    m_solver.assert_expr(m.mk_not(m.mk_iff(fml, n)));
    todo.push_back(fml);
    names.push_back(n);
    is_checked.push_back(false);
    parent_ids.push_back(0);
    self_ids.push_back(0);
    std::pair<unsigned,expr*> path_r;

    m_solver.push();
    while (!todo.empty()) {

        r = 0;
        ptr_buffer<expr> args;
        expr* e = todo.back();
        unsigned pos = parent_ids.back();
        n = names.back();
        bool checked = is_checked.back();

        if (cache.contains(e)) {
            goto done;
        }
        if (!m.is_bool(e)) {
            r = e;
            goto done;
        }
        if (m.is_bool(e) && !checked) {
            m_solver.push();
            m_solver.assert_expr(n);
            is_sat = m_solver.check();
            m_solver.pop(1);
            if (is_sat == l_false) {
                r = m.mk_true();
                goto done;
            }
        }
        if (m.is_bool(e) && !checked) {
            m_solver.push();
            m_solver.assert_expr(m.mk_not(n));
            is_sat = m_solver.check();
            m_solver.pop(1);
            if (is_sat == l_false) {
                r = m.mk_false();
                goto done;
            }
        }
        if (!is_app(e)) {
            r = e;
            goto done;
        }
       
        a = to_app(e);
        if (!is_checked.back()) {
            self_ids.back() = ++path_id;
            is_checked.back() = true;
        }
        self_pos = self_ids.back();
        sz = a->get_num_args();

        n2 = 0;
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg = a->get_arg(i);

            if (cache.find(arg, path_r)) {
                if (path_r.first == self_pos) {
                    args.push_back(path_r.second);
                }
                else {
                    args.push_back(arg);
                }
            }
            else if (!m.is_bool(arg)) {
                args.push_back(arg);
            }
            else if (!n2) {                
                n2 = m.mk_app(m_fn, m_arith.mk_numeral(rational(id++), true));
                todo.push_back(arg);
                parent_ids.push_back(self_pos);
                self_ids.push_back(0);
                names.push_back(n2);
                trail.push_back(n2);
                args.push_back(n2);
                is_checked.push_back(false);
            }
            else {
                args.push_back(arg);
            }
        }
        r = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
        trail.push_back(r);
        if (n2) {
            m_solver.push();
            m_solver.assert_expr(m.mk_eq(r, n));
            continue;
        }

    done:
        if (r) {
            cache.insert(e, std::make_pair(pos, r));
        }

        TRACE("expr_context_simplifier", 
              tout << mk_pp(e, m_manager) 
              << " checked: " << checked 
              << " cached: " 
              << mk_pp(r?r:e, m_manager) << "\n";);

        todo.pop_back();
        parent_ids.pop_back();
        self_ids.pop_back();
        names.pop_back();
        is_checked.pop_back();
        m_solver.pop(1);
    }

    VERIFY(cache.find(fml, path_r));
    m_solver.pop(1);
    result = path_r.second;
}


void expr_strong_context_simplifier::simplify_model_based(expr* fml, expr_ref& result) {
    ast_manager& m = m_manager;
    //
    // The context assumes that asserted expressions are in NNF with
    // respect to the quantifier occurrences.
    // This can be disabled if the strong context simplifier
    // is called from the API over the Z3_simplify method.
    //
    if (!m.is_bool(fml) || has_quantifiers(fml)) {
        result = fml;
        return;
    }                                                

    ptr_vector<expr> todo;
    ptr_vector<expr> names;
    svector<bool>    is_checked;
    svector<unsigned> parent_ids, self_ids;
    expr_ref_vector  fresh_vars(m);
    expr_ref_vector trail(m);
    obj_map<expr,std::pair<unsigned, expr*> > cache;
    lbool is_sat;
    expr_ref_vector assignments(m);

    m_solver.push();
    m_solver.assert_expr(fml);
    is_sat = m_solver.check();
    if (is_sat != l_false) {
        m_solver.get_assignments(assignments);
    }
    m_solver.pop(1);
    if (is_sat == l_false) {
        result = m.mk_false();
        return;
    }    
    // Collect assignments to sub-formulas from satisfying assignment.
    obj_map<expr,lbool> assignment_map;
    {
        expr* n1, *n2;
        for (unsigned i = 0; i < assignments.size(); ++i) {
            if (m.is_not(assignments[i].get(), n1)) {
                assignment_map.insert(n1, l_false);
            }
            else {
                assignment_map.insert(assignments[i].get(), l_true);
            }
        }

        todo.push_back(fml);
        while (!todo.empty()) {
            expr* n = todo.back();
            if (!is_app(n)) {
                assignment_map.insert(n, l_undef);
                todo.pop_back();
                continue;
            }
            app* a = to_app(n);
            unsigned sz = a->get_num_args();
            bool all_visit = true;
            for (unsigned i = 0; i < sz; ++i) {
                if (!assignment_map.contains(a->get_arg(i))) {
                    todo.push_back(a->get_arg(i));
                    all_visit = false;
                }
            }
            if (!all_visit) {
                continue;
            }
            todo.pop_back();
            lbool value = l_undef;
            if (m.is_and(a)) {
                value = l_true;
                for (unsigned i = 0; value != l_false && i < sz; ++i) {
                    switch(assignment_map.find(a->get_arg(i))) {
                    case l_false: value = l_false; break;
                    case l_undef: value = l_undef; break;
                    default: break;
                    }
                }
                assignment_map.insert(a, value);
            }
            else if (m.is_or(a)) {
                value = l_false;
                for (unsigned i = 0; value != l_true && i < sz; ++i) {
                    switch(assignment_map.find(a->get_arg(i))) {
                    case l_true:  value = l_true; break;
                    case l_undef: value = l_undef; break;
                    default: break;
                    }
                }
                assignment_map.insert(a, value);
            }
            else if (m.is_not(a)) {
                switch(assignment_map.find(a->get_arg(0))) {
                case l_true: value = l_false; break;
                case l_false: value = l_true; break;
                default: value = l_undef; break;
                }
                assignment_map.insert(a, value);
            }
            else if (m.is_implies(a, n1, n2)) {
                lbool v1 = assignment_map.find(n1);
                lbool v2 = assignment_map.find(n2);
                if (v1 == l_false || v2 == l_true) {
                    value = l_true;
                }
                else if (v1 == l_true && v2 == l_false) {
                    value = l_false;
                }
                else {
                    value = l_undef;
                }
                assignment_map.insert(a, value);                
            }
            else if (m.is_iff(a, n1, n2) || m.is_eq(a, n1, n2)) {
                lbool v1 = assignment_map.find(n1);
                lbool v2 = assignment_map.find(n2);
                if (v1 == l_undef || v2 == l_undef) {
                    value = l_undef;
                }
                else if (v1 == v2) {
                    value = l_true;
                }
                else {
                    value = l_false;
                }
                assignment_map.insert(a, value);                                
            }
            else {
                assignment_map.insert(a, l_undef);
            }
        }
    }
    
    m_solver.push();
    unsigned id = 1;
    expr* n = m.mk_app(m_fn, m_arith.mk_numeral(rational(id++), true));
    expr* r, *n2;
    unsigned path_id = 0, self_pos = 0;
    app * a;
    unsigned sz;
    trail.push_back(n);
    
    m_solver.assert_expr(m.mk_not(m.mk_iff(fml, n)));
    todo.push_back(fml);
    names.push_back(n);
    is_checked.push_back(false);
    parent_ids.push_back(0);
    self_ids.push_back(0);
    std::pair<unsigned,expr*> path_r;

    m_solver.push();
    while (!todo.empty()) {

        r = 0;
        ptr_buffer<expr> args;
        expr* e = todo.back();
        unsigned pos = parent_ids.back();
        n = names.back();
        bool checked = is_checked.back();

        if (cache.contains(e)) {
            goto done;
        }
        if (!m.is_bool(e)) {
            r = e;
            goto done;
        }
        if (m.is_bool(e) && !checked) {
            lbool value = l_undef;
            assignment_map.find(e, value);

                switch(value) {
                case l_true:
                    if (is_forced(n, m.mk_true())) {
                        r = m.mk_true();
                        goto done;
                    }
                    break;
                case l_false:
                    if (is_forced(n, m.mk_false())) {
                        r = m.mk_false();
                        goto done;
                    }
                    break;
                default:
                    // NB. assignments contain just internalized literals,
                    // the literals in the input may not be internalized.
                    // we therefore fall back to the default behavior, which
                    // is to check both cases.
                    if (is_forced(n, m.mk_true())) {
                        r = m.mk_true();
                        goto done;
                    }
                    if (is_forced(n, m.mk_false())) {
                        r = m.mk_false();
                        goto done;
                    }
                    break;
                }
            
        }
        if (!is_app(e)) {
            r = e;
            goto done;
        }
       
        a = to_app(e);
        if (!is_checked.back()) {
            self_ids.back() = ++path_id;
            is_checked.back() = true;
        }
        self_pos = self_ids.back();
        sz = a->get_num_args();

        n2 = 0;
        for (unsigned i = 0; i < sz; ++i) {
            expr* arg = a->get_arg(i);

            if (cache.find(arg, path_r)) {
                if (path_r.first == self_pos) {
                    args.push_back(path_r.second);
                }
                else {
                    args.push_back(arg);
                }
            }
            else if (!m.is_bool(arg)) {
                args.push_back(arg);
            }
            else if (!n2) {                
                n2 = m.mk_app(m_fn, m_arith.mk_numeral(rational(id++), true));
                todo.push_back(arg);
                parent_ids.push_back(self_pos);
                self_ids.push_back(0);
                names.push_back(n2);
                trail.push_back(n2);
                args.push_back(n2);
                is_checked.push_back(false);
            }
            else {
                args.push_back(arg);
            }
        }
        r = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
        trail.push_back(r);
        if (n2) {
            m_solver.push();
            m_solver.assert_expr(m.mk_eq(r, n));
            continue;
        }

    done:
        if (r) {
            cache.insert(e, std::make_pair(pos, r));
        }

        TRACE("expr_context_simplifier", 
              tout << mk_pp(e, m_manager) 
              << " checked: " << checked 
              << " cached: " 
              << mk_pp(r?r:e, m_manager) << "\n";);

        todo.pop_back();
        parent_ids.pop_back();
        self_ids.pop_back();
        names.pop_back();
        is_checked.pop_back();
        m_solver.pop(1);
    }

    VERIFY(cache.find(fml, path_r));
    m_solver.pop(1);
    result = path_r.second;
}

bool expr_strong_context_simplifier::is_forced(expr* e, expr* v) {
    m_solver.push();
    m_solver.assert_expr(m_manager.mk_eq(e, v));
    lbool is_sat = m_solver.check();
    m_solver.pop(1);
    return (is_sat == l_false);
}
