/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_rewriter.cpp

Abstract:

    Basic rewriting rules for sequences constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5
    Murphy Berzish 2017-02-21
    Caleb Stanford 2020-07-07

--*/

#include "util/uint_set.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "params/seq_rewriter_params.hpp"
#include "math/automata/automaton.h"
#include "math/automata/symbolic_automata_def.h"


expr_ref sym_expr::accept(expr* e) {
    ast_manager& m = m_t.get_manager();
    expr_ref result(m);
    var_subst subst(m);
    seq_util u(m);
    unsigned r1, r2, r3;
    switch (m_ty) {
    case t_pred:         
        result = subst(m_t, 1, &e);
        break;    
    case t_not:
        result = m_expr->accept(e);
        result = m.mk_not(result);
        break;
    case t_char:
        SASSERT(e->get_sort() == m_t->get_sort());
        SASSERT(e->get_sort() == m_sort);
        result = m.mk_eq(e, m_t);
        break;
    case t_range: 
        if (u.is_const_char(m_t, r1) && u.is_const_char(e, r2) && u.is_const_char(m_s, r3)) {
            result = m.mk_bool_val((r1 <= r2) && (r2 <= r3));            
        }
        else {
            result = m.mk_and(u.mk_le(m_t, e), u.mk_le(e, m_s));
        }
        break;
    }
    
    return result;
}

std::ostream& sym_expr::display(std::ostream& out) const {
    switch (m_ty) {
    case t_char: return out << m_t;
    case t_range: return out << m_t << ":" << m_s;
    case t_pred: return out << m_t;
    case t_not: return m_expr->display(out << "not ");
    }
    return out << "expression type not recognized";
}

struct display_expr1 {
    ast_manager& m;
    display_expr1(ast_manager& m): m(m) {}
    std::ostream& display(std::ostream& out, sym_expr* e) const {
        return e->display(out);
    }
};

class sym_expr_boolean_algebra : public boolean_algebra<sym_expr*> {
    ast_manager& m;
    expr_solver& m_solver;
    expr_ref     m_var;
    typedef sym_expr* T;
public:
    sym_expr_boolean_algebra(ast_manager& m, expr_solver& s): 
        m(m), m_solver(s), m_var(m) {}

    T mk_false() override {
        expr_ref fml(m.mk_false(), m);
        return sym_expr::mk_pred(fml, m.mk_bool_sort()); // use of Bool sort for bound variable is arbitrary
    }
    T mk_true() override {
        expr_ref fml(m.mk_true(), m);
        return sym_expr::mk_pred(fml, m.mk_bool_sort());
    }
    T mk_and(T x, T y) override {
        seq_util u(m);
        if (x->is_char() && y->is_char()) {
            if (x->get_char() == y->get_char()) {
                return x;
            }
            if (m.are_distinct(x->get_char(), y->get_char())) {
                expr_ref fml(m.mk_false(), m);
                return sym_expr::mk_pred(fml, x->get_sort());
            }
        }
        unsigned lo1, hi1, lo2, hi2;
        if (x->is_range() && y->is_range() &&
            u.is_const_char(x->get_lo(), lo1) && u.is_const_char(x->get_hi(), hi1) &&
            u.is_const_char(y->get_lo(), lo2) && u.is_const_char(y->get_hi(), hi2)) {
            lo1 = std::max(lo1, lo2);
            hi1 = std::min(hi1, hi2);
            if (lo1 > hi1) {
                expr_ref fml(m.mk_false(), m);
                return sym_expr::mk_pred(fml, x->get_sort());
            }
            expr_ref _start(u.mk_char(lo1), m);
            expr_ref _stop(u.mk_char(hi1), m);
            return sym_expr::mk_range(_start, _stop);
        }

        sort* s = x->get_sort();
        if (m.is_bool(s)) s = y->get_sort();
        var_ref v(m.mk_var(0, s), m);
        expr_ref fml1 = x->accept(v);
        expr_ref fml2 = y->accept(v);
        if (m.is_true(fml1)) {
            return y;
        }
        if (m.is_true(fml2)) {
            return x;
        }
        if (fml1 == fml2) {
            return x;   
        }
        if (is_complement(fml1, fml2)) {
            expr_ref ff(m.mk_false(), m);
            return sym_expr::mk_pred(ff, x->get_sort());
        }
        expr_ref fml(m);
        bool_rewriter br(m);
        br.mk_and(fml1, fml2, fml);
        return sym_expr::mk_pred(fml, x->get_sort());
    }

    bool is_complement(expr* f1, expr* f2) {
        expr* f = nullptr;
        return 
            (m.is_not(f1, f) && f == f2) ||
            (m.is_not(f2, f) && f == f1);
    }

    T mk_or(T x, T y) override {
        if (x->is_char() && y->is_char() &&
            x->get_char() == y->get_char()) {
            return x;
        }
        if (x == y) return x;
        var_ref v(m.mk_var(0, x->get_sort()), m);
        expr_ref fml1 = x->accept(v);
        expr_ref fml2 = y->accept(v);        
        if (m.is_false(fml1)) return y;
        if (m.is_false(fml2)) return x;
        bool_rewriter br(m);
        expr_ref fml(m);
        br.mk_or(fml1, fml2, fml);
        return sym_expr::mk_pred(fml, x->get_sort());
    }

    T mk_and(unsigned sz, T const* ts) override {
        switch (sz) {
        case 0: return mk_true();
        case 1: return ts[0];
        default: {
            T t = ts[0];
            for (unsigned i = 1; i < sz; ++i) {
                t = mk_and(t, ts[i]);
            }
            return t;
        }
        }
    }

    T mk_or(unsigned sz, T const* ts) override {
        switch (sz) {
        case 0: return mk_false();
        case 1: return ts[0];
        default: {
            T t = ts[0];
            for (unsigned i = 1; i < sz; ++i) {
                t = mk_or(t, ts[i]);
            }
            return t;
        }
        }
    }

    lbool is_sat(T x) override {
        unsigned lo, hi;
        seq_util u(m);

        if (x->is_char()) {
            return l_true;
        }
        if (x->is_range() && u.is_const_char(x->get_lo(), lo) && u.is_const_char(x->get_hi(), hi)) {
            return (lo <= hi) ? l_true : l_false; 
        }
        if (x->is_not() && x->get_arg()->is_range() && u.is_const_char(x->get_arg()->get_lo(), lo) && 0 < lo) {
            return l_true;
        }            
        if (!m_var || m_var->get_sort() != x->get_sort()) {
            m_var = m.mk_fresh_const("x", x->get_sort()); 
        }
        expr_ref fml = x->accept(m_var);
        if (m.is_true(fml)) {
            return l_true;
        }
        if (m.is_false(fml)) {
            return l_false;
        }
        return m_solver.check_sat(fml);
    }

    T mk_not(T x) override {
        return sym_expr::mk_not(m, x);    
    }

};

re2automaton::re2automaton(ast_manager& m): m(m), u(m), m_ba(nullptr), m_sa(nullptr) {}

void re2automaton::set_solver(expr_solver* solver) {
    m_solver = solver;
    m_ba = alloc(sym_expr_boolean_algebra, m, *solver);
    m_sa = alloc(symbolic_automata_t, sm, *m_ba.get());
}

eautomaton* re2automaton::mk_product(eautomaton* a1, eautomaton* a2) {
    return m_sa->mk_product(*a1, *a2);
}

eautomaton* re2automaton::operator()(expr* e) { 
    eautomaton* r = re2aut(e); 
    if (r) {        
        r->compress(); 
        bool_rewriter br(m);
        TRACE("seq", display_expr1 disp(m); r->display(tout << mk_pp(e, m) << " -->\n", disp););
    }
    return r;
} 

bool re2automaton::is_unit_char(expr* e, expr_ref& ch) {
    zstring s;
    expr* c = nullptr;
    if (u.str.is_string(e, s) && s.length() == 1) {
        ch = u.mk_char(s[0]);
        return true;
    }
    if (u.str.is_unit(e, c)) {
        ch = c;
        return true;
    }
    return false;
}

eautomaton* re2automaton::re2aut(expr* e) {
    SASSERT(u.is_re(e));
    expr *e0, *e1, *e2;
    scoped_ptr<eautomaton> a, b;
    unsigned lo, hi;
    zstring s1, s2;
    if (u.re.is_to_re(e, e1)) {
        return seq2aut(e1);
    }
    else if (u.re.is_concat(e, e1, e2) && (a = re2aut(e1)) && (b = re2aut(e2))) {
        return eautomaton::mk_concat(*a, *b);
    }
    else if (u.re.is_union(e, e1, e2) && (a = re2aut(e1)) && (b = re2aut(e2))) {
        return eautomaton::mk_union(*a, *b);
    }
    else if (u.re.is_star(e, e1) && (a = re2aut(e1))) {
        a->add_final_to_init_moves();
        a->add_init_to_final_states();        
        return a.detach();            
    }
    else if (u.re.is_plus(e, e1) && (a = re2aut(e1))) {
        a->add_final_to_init_moves();
        return a.detach();            
    }
    else if (u.re.is_opt(e, e1) && (a = re2aut(e1))) {
        a = eautomaton::mk_opt(*a);
        return a.detach();                    
    }
    else if (u.re.is_range(e, e1, e2)) {
        expr_ref _start(m), _stop(m);
        if (is_unit_char(e1, _start) &&
            is_unit_char(e2, _stop)) {
            TRACE("seq", tout << "Range: " << _start << " " << _stop << "\n";);
            a = alloc(eautomaton, sm, sym_expr::mk_range(_start, _stop));
            return a.detach();            
        }
        else {
            // if e1/e2 are not unit, (re.range e1 e2) is defined to be the empty language
            return alloc(eautomaton, sm);
        }
    }
    else if (u.re.is_complement(e, e0) && (a = re2aut(e0)) && m_sa) {
        return m_sa->mk_complement(*a);
    }
    else if (u.re.is_loop(e, e1, lo, hi) && (a = re2aut(e1))) {
        scoped_ptr<eautomaton> eps = eautomaton::mk_epsilon(sm);
        b = eautomaton::mk_epsilon(sm);
        while (hi > lo) {
            scoped_ptr<eautomaton> c = eautomaton::mk_concat(*a, *b);
            b = eautomaton::mk_union(*eps, *c);
            --hi;
        }
        while (lo > 0) {
            b = eautomaton::mk_concat(*a, *b);
            --lo;
        }
        return b.detach();        
    }
    else if (u.re.is_loop(e, e1, lo) && (a = re2aut(e1))) {
        b = eautomaton::clone(*a);
        b->add_final_to_init_moves();
        b->add_init_to_final_states();        
        while (lo > 0) {
            b = eautomaton::mk_concat(*a, *b);
            --lo;
        }
        return b.detach();        
    }
    else if (u.re.is_empty(e)) {
        return alloc(eautomaton, sm);
    }
    else if (u.re.is_full_seq(e)) {
        expr_ref tt(m.mk_true(), m);
        sort *seq_s = nullptr, *char_s = nullptr;
        VERIFY (u.is_re(e->get_sort(), seq_s));
        VERIFY (u.is_seq(seq_s, char_s));
        sym_expr* _true = sym_expr::mk_pred(tt, char_s);
        return eautomaton::mk_loop(sm, _true);
    }
    else if (u.re.is_full_char(e)) {
        expr_ref tt(m.mk_true(), m);
        sort *seq_s = nullptr, *char_s = nullptr;
        VERIFY (u.is_re(e->get_sort(), seq_s));
        VERIFY (u.is_seq(seq_s, char_s));
        sym_expr* _true = sym_expr::mk_pred(tt, char_s);
        a = alloc(eautomaton, sm, _true);
        return a.detach();
    }
    else if (u.re.is_intersection(e, e1, e2) && m_sa && (a = re2aut(e1)) && (b = re2aut(e2))) {
        eautomaton* r = m_sa->mk_product(*a, *b);
        TRACE("seq", display_expr1 disp(m); a->display(tout << "a:", disp); b->display(tout << "b:", disp); r->display(tout << "intersection:", disp););
        return r;
    }
    else {        
        TRACE("seq", tout << "not handled " << mk_pp(e, m) << "\n";);
    }
    
    return nullptr;
}

eautomaton* re2automaton::seq2aut(expr* e) {
    SASSERT(u.is_seq(e));
    zstring s;
    expr* e1, *e2;
    scoped_ptr<eautomaton> a, b;
    if (u.str.is_concat(e, e1, e2) && (a = seq2aut(e1)) && (b = seq2aut(e2))) {
        return eautomaton::mk_concat(*a, *b);
    }
    else if (u.str.is_unit(e, e1)) {
        return alloc(eautomaton, sm, sym_expr::mk_char(m, e1));
    }
    else if (u.str.is_empty(e)) {
        return eautomaton::mk_epsilon(sm);
    }
    else if (u.str.is_string(e, s)) {        
        unsigned init = 0;
        eautomaton::moves mvs;        
        unsigned_vector final;
        final.push_back(s.length());
        for (unsigned k = 0; k < s.length(); ++k) {
            // reference count?
            mvs.push_back(eautomaton::move(sm, k, k+1, sym_expr::mk_char(m, u.str.mk_char(s, k))));
        }
        return alloc(eautomaton, sm, init, final, mvs);
    }
    return nullptr;
}

void seq_rewriter::updt_params(params_ref const & p) {
    seq_rewriter_params sp(p);
    m_coalesce_chars = sp.coalesce_chars();
}

void seq_rewriter::get_param_descrs(param_descrs & r) {
    seq_rewriter_params::collect_param_descrs(r);
}

br_status seq_rewriter::mk_bool_app(func_decl* f, unsigned n, expr* const* args, expr_ref& result) {
    switch (f->get_decl_kind()) {
    case OP_AND:
        return mk_bool_app_helper(true, n, args, result);
    case OP_OR:
        return mk_bool_app_helper(false, n, args, result);
    case OP_EQ:
        SASSERT(n == 2);
        // return mk_eq_helper(args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status seq_rewriter::mk_bool_app_helper(bool is_and, unsigned n, expr* const* args, expr_ref& result) {
    bool found = false;
    expr* arg = nullptr;
    
    for (unsigned i = 0; i < n && !found; ++i) {        
        found = str().is_in_re(args[i]) || (m().is_not(args[i], arg) && str().is_in_re(arg));
    }
    if (!found) return BR_FAILED;
    
    obj_map<expr, expr*> in_re, not_in_re;
    bool found_pair = false;
    
    ptr_buffer<expr> new_args;
    for (unsigned i = 0; i < n; ++i) {
        expr* args_i = args[i];
        expr* x = nullptr, *y = nullptr, *z = nullptr;
        if (str().is_in_re(args_i, x, y) && !str().is_empty(x)) {
            if (in_re.find(x, z)) {				
                in_re[x] = is_and ? re().mk_inter(z, y) : re().mk_union(z, y);
                found_pair = true;
            }
            else {
                in_re.insert(x, y);
                found_pair |= not_in_re.contains(x);
            }
        }
        else if (m().is_not(args_i, arg) && str().is_in_re(arg, x, y) && !str().is_empty(x)) {
            if (not_in_re.find(x, z)) {
                not_in_re[x] = is_and ? re().mk_union(z, y) : re().mk_inter(z, y);
                found_pair = true;
            }
            else {
                not_in_re.insert(x, y);
                found_pair |= in_re.contains(x);
            }
        }
        else 
            new_args.push_back(args_i);
    }
    
    if (!found_pair) {
        return BR_FAILED;
    }
    

    for (auto const & kv : in_re) {
        expr* x = kv.m_key;
        expr* y = kv.m_value;
        expr* z = nullptr;
        if (not_in_re.find(x, z)) {
            expr* z_c = re().mk_complement(z);
            expr* w = is_and ? re().mk_inter(y, z_c) : re().mk_union(y, z_c);
            new_args.push_back(re().mk_in_re(x, w));
        }
        else {
            new_args.push_back(re().mk_in_re(x, y));
        }
    }
    for (auto const& kv : not_in_re) {
        expr* x = kv.m_key;
        expr* y = kv.m_value;
        if (!in_re.contains(x)) {
            new_args.push_back(re().mk_in_re(x, re().mk_complement(y)));
        }
    }
    
    result = is_and ? m().mk_and(new_args) : m().mk_or(new_args);
    return BR_REWRITE_FULL;
}

br_status seq_rewriter::mk_eq_helper(expr* a, expr* b, expr_ref& result) {
    expr* sa = nullptr, *ra = nullptr, *sb = nullptr, *rb = nullptr;
    if (str().is_in_re(b))
        std::swap(a, b);
    if (!str().is_in_re(a, sa, ra))
        return BR_FAILED;
    bool is_not = m().is_not(b, b);
    if (!str().is_in_re(b, sb, rb))
        return BR_FAILED;
    if (sa != sb)
        return BR_FAILED;
    // sa in ra = sb in rb;
    // sa in (ra n rb) u (C(ra) n C(rb))
    if (is_not)
        rb = re().mk_complement(rb);
    expr* r = re().mk_union(re().mk_inter(ra, rb), re().mk_inter(re().mk_complement(ra), re().mk_complement(rb)));
    result = re().mk_in_re(sa, r);
    return BR_REWRITE_FULL;
}

br_status seq_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    br_status st = BR_FAILED;
    switch(f->get_decl_kind()) {
        
    case OP_SEQ_UNIT:
        SASSERT(num_args == 1);
        st = mk_seq_unit(args[0], result);
        break;
    case OP_SEQ_EMPTY:
        return BR_FAILED;
    case OP_RE_PLUS:
        SASSERT(num_args == 1);
        st = mk_re_plus(args[0], result);
        break;
    case OP_RE_STAR:
        SASSERT(num_args == 1);
        st = mk_re_star(args[0], result);
        break;
    case OP_RE_OPTION:
        SASSERT(num_args == 1);
        st = mk_re_opt(args[0], result);
        break;
    case OP_RE_REVERSE:
        SASSERT(num_args == 1);
        st = mk_re_reverse(args[0], result);
        break;
    case OP_RE_DERIVATIVE:
        SASSERT(num_args == 2);
        st = mk_re_derivative(args[0], args[1], result);
        break;
    case OP_RE_CONCAT:
        if (num_args == 1) {
            result = args[0]; 
            st = BR_DONE;
        }
        else {
            SASSERT(num_args == 2);
            st = mk_re_concat(args[0], args[1], result); 
        }
        break;
    case _OP_RE_ANTIMOROV_UNION:
        SASSERT(num_args == 2);
        // Rewrite Antimorov union to real union
        result = re().mk_union(args[0], args[1]);
        st = BR_REWRITE1;
        break;
    case OP_RE_UNION:
        if (num_args == 1) {
            result = args[0]; 
            st = BR_DONE;
        }
        else {
            SASSERT(num_args == 2);
            st = mk_re_union(args[0], args[1], result);
        }
        break;
    case OP_RE_RANGE:
        SASSERT(num_args == 2);
        st = mk_re_range(args[0], args[1], result);
        break;
    case OP_RE_DIFF: 
        if (num_args == 2)
            st = mk_re_diff(args[0], args[1], result);
        else if (num_args == 1) {
            result = args[0];
            st = BR_DONE;
        }          
        break;
    case OP_RE_INTERSECT:
        if (num_args == 1) {
            result = args[0];
            st = BR_DONE;
        }
        else {
            SASSERT(num_args == 2);
            st = mk_re_inter(args[0], args[1], result);
        }
        break;
    case OP_RE_COMPLEMENT:
        SASSERT(num_args == 1);
        st = mk_re_complement(args[0], result);
        break;
    case OP_RE_LOOP:
        st = mk_re_loop(f, num_args, args, result);
        break;
    case OP_RE_POWER:
        st = mk_re_power(f, args[0], result);
        break;
    case OP_RE_EMPTY_SET:
        return BR_FAILED;    
    case OP_RE_FULL_SEQ_SET:
        return BR_FAILED;    
    case OP_RE_FULL_CHAR_SET:
        return BR_FAILED;    
    case OP_RE_OF_PRED:
        return BR_FAILED;    
    case _OP_SEQ_SKOLEM:
        return BR_FAILED;    
    case OP_SEQ_CONCAT: 
        if (num_args == 1) {
            result = args[0];
            st = BR_DONE;
        }
        else {
            SASSERT(num_args == 2);
            st = mk_seq_concat(args[0], args[1], result);
        }
        break;
    case OP_SEQ_LENGTH:
        SASSERT(num_args == 1);
        st = mk_seq_length(args[0], result);
        break;
    case OP_SEQ_EXTRACT:
        SASSERT(num_args == 3);
        st = mk_seq_extract(args[0], args[1], args[2], result);
        break;
    case OP_SEQ_CONTAINS: 
        SASSERT(num_args == 2);
        st = mk_seq_contains(args[0], args[1], result);
        break;
    case OP_SEQ_AT:
        SASSERT(num_args == 2);
        st = mk_seq_at(args[0], args[1], result); 
        break;
    case OP_SEQ_NTH:
        SASSERT(num_args == 2);
        return mk_seq_nth(args[0], args[1], result); 
    case OP_SEQ_NTH_I:
        SASSERT(num_args == 2);
        return mk_seq_nth_i(args[0], args[1], result); 
    case OP_SEQ_PREFIX: 
        SASSERT(num_args == 2);
        st = mk_seq_prefix(args[0], args[1], result);
        break;
    case OP_SEQ_SUFFIX: 
        SASSERT(num_args == 2);
        st = mk_seq_suffix(args[0], args[1], result);
        break;
    case OP_SEQ_INDEX:
        if (num_args == 2) {
            expr_ref arg3(zero(), m());
            result = str().mk_index(args[0], args[1], arg3);
            st = BR_REWRITE1;
        }
        else {
            SASSERT(num_args == 3);
            st = mk_seq_index(args[0], args[1], args[2], result);
        }
        break;
    case OP_SEQ_LAST_INDEX:
        SASSERT(num_args == 2);
        st = mk_seq_last_index(args[0], args[1], result);
        break;
    case OP_SEQ_REPLACE:
        SASSERT(num_args == 3);
        st = mk_seq_replace(args[0], args[1], args[2], result);
        break;
    case OP_SEQ_REPLACE_ALL:
        SASSERT(num_args == 3);
        st = mk_seq_replace_all(args[0], args[1], args[2], result);
        break;
    case OP_SEQ_TO_RE:
        SASSERT(num_args == 1);
        st = mk_str_to_regexp(args[0], result);
        break;
    case OP_SEQ_IN_RE:
        SASSERT(num_args == 2);
        st = mk_str_in_regexp(args[0], args[1], result);
        break;
    case OP_STRING_LE:
        SASSERT(num_args == 2);
        st = mk_str_le(args[0], args[1], result);
        break;
    case OP_STRING_LT:
        SASSERT(num_args == 2);
        st = mk_str_lt(args[0], args[1], result);
        break;
    case OP_STRING_FROM_CODE:
        SASSERT(num_args == 1);
        st = mk_str_from_code(args[0], result);
        break;
    case OP_STRING_TO_CODE:
        SASSERT(num_args == 1);
        st = mk_str_to_code(args[0], result);
        break;
    case OP_STRING_IS_DIGIT:
        SASSERT(num_args == 1);
        st = mk_str_is_digit(args[0], result);
        break;
    case OP_STRING_CONST:
        st = BR_FAILED;
        if (!m_coalesce_chars) {
            st = mk_str_units(f, result);
        }
        break;
    case OP_STRING_ITOS: 
        SASSERT(num_args == 1);
        st = mk_str_itos(args[0], result);
        break;
    case OP_STRING_STOI: 
        SASSERT(num_args == 1);
        st = mk_str_stoi(args[0], result);
        break;
    case OP_STRING_UBVTOS:
        SASSERT(num_args == 1);
        st = mk_str_ubv2s(args[0], result);
        break;
    case _OP_STRING_CONCAT:
    case _OP_STRING_PREFIX:
    case _OP_STRING_SUFFIX:
    case _OP_STRING_STRCTN:
    case _OP_STRING_LENGTH:
    case _OP_STRING_CHARAT:
    case _OP_STRING_IN_REGEXP: 
    case _OP_STRING_TO_REGEXP: 
    case _OP_STRING_SUBSTR: 
    case _OP_STRING_STRREPL:
    case _OP_STRING_STRIDOF: 
        UNREACHABLE();
    }
    if (st == BR_FAILED) {
        st = lift_ites_throttled(f, num_args, args, result);
    }
    CTRACE("seq_verbose", st != BR_FAILED, tout << expr_ref(m().mk_app(f, num_args, args), m()) << " -> " << result << "\n";);
    SASSERT(st == BR_FAILED || result->get_sort() == f->get_range());
    return st;
}

/*
 * (seq.unit (_ BitVector 8)) ==> String constant
 */
br_status seq_rewriter::mk_seq_unit(expr* e, expr_ref& result) {
    unsigned ch;
    // specifically we want (_ BitVector 8)
    if (m_util.is_const_char(e, ch) && m_coalesce_chars) {
        // convert to string constant
        zstring s(ch);
        TRACE("seq_verbose", tout << "rewrite seq.unit of 8-bit value " << ch << " to string constant \"" << s<< "\"" << std::endl;);
        result = str().mk_string(s);
        return BR_DONE;
    }

    return BR_FAILED;
}

/*
   string + string = string
   (a + b) + c = a + (b + c)
   a + "" = a
   "" + a = a
   string + (string + a) = string + a
*/
expr_ref seq_rewriter::mk_seq_concat(expr* a, expr* b) {
    expr_ref result(m());
    if (BR_FAILED == mk_seq_concat(a, b, result))
        result = str().mk_concat(a, b);
    return result;
}
br_status seq_rewriter::mk_seq_concat(expr* a, expr* b, expr_ref& result) {
    zstring s1, s2;
    expr* c, *d;
    bool isc1 = str().is_string(a, s1) && m_coalesce_chars;
    bool isc2 = str().is_string(b, s2) && m_coalesce_chars;
    if (isc1 && isc2) {
        result = str().mk_string(s1 + s2);
        return BR_DONE;
    }
    if (str().is_concat(a, c, d)) {
        result = str().mk_concat(c, str().mk_concat(d, b));
        return BR_REWRITE2;
    }
    if (str().is_empty(a)) {
        result = b;
        return BR_DONE;
    }
    if (str().is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    if (isc1 && str().is_concat(b, c, d) && str().is_string(c, s2)) {
        result = str().mk_concat(str().mk_string(s1 + s2), d);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_length(expr* a, expr_ref& result) {
    zstring b;
    m_es.reset();
    str().get_concat(a, m_es);
    unsigned len = 0;
    unsigned j = 0;
    for (expr* e : m_es) {
        if (str().is_string(e, b)) {
            len += b.length();
        }
        else if (str().is_unit(e)) {
            len += 1;
        }
        else if (str().is_empty(e)) {
            // skip
        }
        else {
            m_es[j++] = e;
        }
    }
    if (j == 0) {
        result = m_autil.mk_int(len);
        return BR_DONE;
    }
    if (j != m_es.size() || j != 1) {
        expr_ref_vector es(m());        
        for (unsigned i = 0; i < j; ++i) {
            es.push_back(str().mk_length(m_es.get(i)));
        }
        if (len != 0) {
            es.push_back(m_autil.mk_int(len));
        }
        result = m_autil.mk_add(es.size(), es.data());
        return BR_REWRITE2;
    }
    expr* x = nullptr, *y = nullptr, *z = nullptr;
    if (str().is_replace(a, x, y, z) && l_true == eq_length(y, z)) {
        result = str().mk_length(x);
        return BR_REWRITE1;
    }
#if 0
    expr* s = nullptr, *offset = nullptr, *length = nullptr;
    if (str().is_extract(a, s, offset, length)) {
        expr_ref len_s(str().mk_length(s), m());
        // if offset < 0 then 0
        // elif length <= 0 then 0
        // elif offset >= len(s) then 0
        // elif offset + length > len(s) then len(s) - offset
        // else length
        expr_ref zero(m_autil.mk_int(0), m());
        result = length;
        result = m().mk_ite(m_autil.mk_gt(m_autil.mk_add(offset, length), len_s),
                            m_autil.mk_sub(len_s, offset),
                            result);
        result = m().mk_ite(m().mk_or(m_autil.mk_le(len_s, offset), m_autil.mk_le(length, zero), m_autil.mk_lt(offset, zero)),
                            zero,
                            result);
        return BR_REWRITE_FULL;
    }
#endif
    return BR_FAILED;
}

/*
    Lift all ite expressions to the top level, safely
    throttled to not blowup the size of the expression.

    Note: this function does not ensure the same BDD form that is
    used in the normal form for derivatives in mk_re_derivative.
*/
br_status seq_rewriter::lift_ites_throttled(func_decl* f, unsigned n, expr* const* args, expr_ref& result) {
    expr* c = nullptr, * t = nullptr, * e = nullptr;
    for (unsigned i = 0; i < n; ++i)
        if (m().is_ite(args[i], c, t, e) &&
            lift_ites_filter(f, args[i]) &&
            (get_depth(t) <= 2 || t->get_ref_count() == 1 ||
                get_depth(e) <= 2 || e->get_ref_count() == 1)) {
            ptr_buffer<expr> new_args;
            for (unsigned j = 0; j < n; ++j) new_args.push_back(args[j]);
            new_args[i] = t;
            expr_ref arg1(m().mk_app(f, new_args), m());
            new_args[i] = e;
            expr_ref arg2(m().mk_app(f, new_args), m());
            result = m().mk_ite(c, arg1, arg2);
            TRACE("seq_verbose", tout << "lifting ite: " << mk_pp(result, m()) << std::endl;);
            return BR_REWRITE2;
        }
    return BR_FAILED;
}

/* returns false iff the ite must not be lifted */
bool seq_rewriter::lift_ites_filter(func_decl* f, expr* ite) {
    // do not lift ites from sequences over regexes
    // for example DO NOT lift to_re(ite(c, s, t)) to ite(c, to_re(s), to_re(t))
    if (u().is_re(f->get_range()) && u().is_seq(ite->get_sort()))
        return false;
    // The following check is intended to avoid lifting cases such as 
    // substring(s,0,ite(c,e1,e2)) ==> ite(c, substring(s,0,e1), substring(s,0,e2))
    // TBD: not sure if this is too restrictive though and may block cases when such lifting is desired
    // if (m_autil.is_int(m().get_sort(ite)) && u().is_seq(f->get_range()))
    //    return false;
    return true;
}


bool seq_rewriter::is_suffix(expr* s, expr* offset, expr* len) {
    expr_ref_vector lens(m());
    rational a, b;
    return 
        get_lengths(len, lens, a) && 
        (a.neg(), m_autil.is_numeral(offset, b) && 
         b.is_pos() && 
         a == b && 
         lens.contains(s));
}

bool seq_rewriter::is_prefix(expr* s, expr* offset, expr* len) {
    expr_ref_vector lens(m());
    rational a, b;
    return 
        get_lengths(len, lens, a) &&
        a < 0 && 
        m_autil.is_numeral(offset, b) && 
        b == 0 && 
        lens.size() == 1 && 
        lens.contains(s);
}

bool seq_rewriter::sign_is_determined(expr* e, sign& s) {
    s = sign_zero;
    if (m_autil.is_add(e)) {
        for (expr* arg : *to_app(e)) {
            sign s1;
            if (!sign_is_determined(arg, s1))
                return false;
            if (s == sign_zero) 
                s = s1;
            else if (s1 == sign_zero)
                continue;
            else if (s1 != s)
                return false;
        }
        return true;
    }
    if (m_autil.is_mul(e)) {
        for (expr* arg : *to_app(e)) {
            sign s1;
            if (!sign_is_determined(arg, s1))
                return false;
            if (s1 == sign_zero) {
                s = sign_zero;
                return true;
            }
            if (s == sign_zero)
                s = s1;
            else if (s != s1)
                s = sign_neg;
            else 
                s = sign_pos;
        }
        return true;
    }
    if (str().is_length(e)) {
        s = sign_pos;
        return true;
    }
    rational r;
    if (m_autil.is_numeral(e, r)) {
        if (r.is_pos())
            s = sign_pos;
        else if (r.is_neg())
            s = sign_neg;
        return true;
    }
    return false;
}

expr_ref seq_rewriter::mk_len(rational const& p, expr_ref_vector const& xs) {
    expr_ref r(m_autil.mk_int(p), m());
    for (expr* e : xs)
        r = m_autil.mk_add(r, str().mk_length(e));
    return r;
}

bool seq_rewriter::extract_pop_suffix(expr_ref_vector const& as, expr* b, expr* c, expr_ref& result) {
    unsigned len_a1 = 0, len_a2 = 0;
    min_length(as, len_a1);
    rational pos, len;
    if (!as.empty() && m_autil.is_numeral(b, pos) && 
        m_autil.is_numeral(c, len) && len_a1 >= pos + len && pos >= 0 && len >= 0) {
        unsigned i = 0;
        len_a1 = 0;
        for ( ; i < as.size() && len_a1 < pos + len; ++i) {
            min_length(as.get(i), len_a2);
            len_a1 += len_a2;
        }
        if (i < as.size()) {
            expr* a = str().mk_concat(i, as.data(), as[0]->get_sort());
            result = str().mk_substr(a, b, c);
            return true;
        }
    }
    return false;
}


bool seq_rewriter::extract_push_offset(expr_ref_vector const& as, expr* b, expr* c, expr_ref& result) {
    expr_ref_vector lens(m());
    rational pos1;
    if (get_lengths(b, lens, pos1) && pos1 >= 0) {
        unsigned i = 0;
        for (; i < as.size(); ++i) {
            expr* lhs = as.get(i);
            if (lens.contains(lhs)) {
                lens.erase(lhs);
            }
            else if (str().is_unit(lhs) && pos1.is_pos()) {
                pos1 -= rational(1);
            }
            else {
                break;
            }
        }
        if (i != 0) {
            expr_ref t1(m());
            t1 = str().mk_concat(as.size() - i, as.data() + i, as[0]->get_sort());
            expr_ref t2 = mk_len(pos1, lens);
            result = str().mk_substr(t1, t2, c);
            TRACE("seq", tout << result << "\n";);
            return true;
        }
    }
    return false;
}

bool seq_rewriter::extract_push_length(expr_ref_vector& as, expr* b, expr* c, expr_ref& result) {
    rational pos;
    expr_ref_vector lens(m());
    if (!as.empty() && 
        m_autil.is_numeral(b, pos) && pos.is_zero() && 
        get_lengths(c, lens, pos) && !pos.is_neg()) {
        unsigned i = 0;
        for (; i < as.size(); ++i) {
            expr* lhs = as.get(i);
            if (lens.contains(lhs)) {
                lens.erase(lhs);
            }
            else if (str().is_unit(lhs) && pos.is_pos()) {
                pos -= rational(1);
            }
            else {
                break;
            }
        }
        if (i == as.size()) {
            result = str().mk_concat(as.size(), as.data(), as[0]->get_sort());
            return true;
        }
        else if (i != 0) {
            expr_ref t1(m()), t2(m());
            t1 = str().mk_concat(as.size() - i, as.data() + i, as[0]->get_sort());
            t2 = mk_len(pos, lens);
            result = str().mk_substr(t1, b, t2);
            as[i] = result;
            result = str().mk_concat(i + 1, as.data(), as[0]->get_sort());
            TRACE("seq", tout << result << "\n";);
            return true;
        }
    }
    return false;
}


br_status seq_rewriter::mk_seq_extract(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s;
    rational pos, len;

    TRACE("seq_verbose", tout << mk_pp(a, m()) << " " << mk_pp(b, m()) << " " << mk_pp(c, m()) << "\n";);
    bool constantBase = str().is_string(a, s);
    bool constantPos = m_autil.is_numeral(b, pos);
    bool constantLen = m_autil.is_numeral(c, len);
    sort* a_sort = a->get_sort();

    sign sg;
    if (sign_is_determined(c, sg) && sg == sign_neg) {
        result = str().mk_empty(a_sort);
        return BR_DONE;
    }
    
    // case 1: pos < 0 or len <= 0
    // rewrite to ""
    if ( (constantPos && pos.is_neg()) || (constantLen && !len.is_pos()) ) {
        result = str().mk_empty(a_sort);
        return BR_DONE;
    }
    // case 1.1: pos >= length(base)
    // rewrite to ""
    if (constantPos && constantBase && pos >= s.length()) {
        result = str().mk_empty(a_sort);
        return BR_DONE;
    }

    rational len_a;
    if (constantPos && max_length(a, len_a) && len_a <= pos) {
        result = str().mk_empty(a_sort);
        return BR_DONE;
    }
    
    constantPos &= pos.is_unsigned();
    constantLen &= len.is_unsigned();

    if (constantPos && constantLen && constantBase) {
        unsigned _pos = pos.get_unsigned();
        unsigned _len = len.get_unsigned();
        if (pos + len >= s.length()) 
            result = str().mk_string(s.extract(_pos, s.length()));
        else 
            result = str().mk_string(s.extract(_pos, _len));
        return BR_DONE;
    }


    expr_ref_vector as(m());
    str().get_concat_units(a, as);
    if (as.empty()) {
        result = str().mk_empty(a->get_sort());
        return BR_DONE;
    }

    if (extract_pop_suffix(as, b, c, result))
        return BR_REWRITE1;

    // extract(a + b + c, len(a + b), s) -> extract(c, 0, s)
    // extract(a + b + c, len(a) + len(b), s) -> extract(c, 0, s)
    if (extract_push_offset(as, b, c, result))
        return BR_REWRITE3;

    // extract(a + b + c, 0, len(a) + len(b)) -> c
    if (extract_push_length(as, b, c, result))
        return BR_REWRITE3;
    
    expr* a1 = nullptr, *b1 = nullptr, *c1 = nullptr;
    if (str().is_extract(a, a1, b1, c1) && 
        is_suffix(a1, b1, c1) && is_suffix(a, b, c)) {
        result = str().mk_substr(a1, m_autil.mk_add(b1, b), m_autil.mk_sub(c1, b));
        return BR_REWRITE3;
    }

    if (str().is_extract(a, a1, b1, c1) && 
        is_prefix(a1, b1, c1) && is_prefix(a, b, c)) {
        result = str().mk_substr(a1, b, m_autil.mk_sub(c1, m_autil.mk_sub(str().mk_length(a), c)));
        return BR_REWRITE3;
    }

    if (str().is_extract(a, a1, b1, c1) &&
        is_prefix(a, b, c) && is_suffix(a1, b1, c1)) {
        expr_ref q(m_autil.mk_sub(c, str().mk_length(a)), m());
        result = str().mk_substr(a1, b1, m_autil.mk_add(c1, q));
        return BR_REWRITE3;
    }

    // (extract (extract a p l) 0 (len a)) -> (extract a p l)
    if (str().is_extract(a, a1, b1, c1) && constantPos && pos == 0 && str().is_length(c, b1) && a1 == b1) {
        result = a;
        return BR_DONE;
    }

    // (extract (extract a p l) 0 l) -> (extract a p l)
    if (str().is_extract(a, a1, b1, c1) && constantPos && pos == 0 && c == c1) {
        result = a;
        return BR_DONE;
    }

    // extract(extract(a, 3, 6), 1, len(extract(a, 3, 6)) - 1) -> extract(a, 4, 5)
    if (str().is_extract(a, a1, b1, c1) && is_suffix(a, b, c) && 
        m_autil.is_numeral(c1) && m_autil.is_numeral(b1)) {
        result = str().mk_substr(a1, m_autil.mk_add(b, b1), m_autil.mk_sub(c1, b));
        return BR_REWRITE2;
    }
 

    if (!constantPos) 
        return BR_FAILED;

    unsigned offset = 0;
    for (; offset < as.size() && str().is_unit(as.get(offset)) && offset < pos; ++offset) {};
    if (offset == 0 && pos > 0) {
        return BR_FAILED;
    }
    std::function<bool(expr*)> is_unit = [&](expr *e) { return str().is_unit(e); };

    if (pos == 0 && as.forall(is_unit)) {
        result = str().mk_empty(a->get_sort());
        for (unsigned i = 1; i <= as.size(); ++i) {
            result = m().mk_ite(m_autil.mk_ge(c, m_autil.mk_int(i)), 
                                str().mk_concat(i, as.data(), a->get_sort()), 
                                result);
        }
        return BR_REWRITE_FULL;
    }
    if (pos == 0 && !constantLen) {
        return BR_FAILED;
    }
    // (extract (++ (unit x) (unit y)) 3 c) = empty
    if (offset == as.size()) {
        result = str().mk_empty(a->get_sort());
        return BR_DONE;
    }
    SASSERT(offset != 0 || pos == 0);
    
    if (constantLen && pos == offset) {
        unsigned _len = len.get_unsigned();
        // (extract (++ (unit a) (unit b) (unit c) x) 1 2) = (++ (unit b) (unit c))
        unsigned i = offset;
        for (; i < as.size() && str().is_unit(as.get(i)) && i - offset < _len; ++i);
        if (i - offset == _len) {
            result = str().mk_concat(_len, as.data() + offset, a->get_sort());
            return BR_DONE;
        }
        if (i == as.size()) {
            result = str().mk_concat(as.size() - offset, as.data() + offset, as[0]->get_sort());
            return BR_DONE;
        }
    }
    if (offset == 0) {
        return BR_FAILED;
    }
    expr_ref position(m());
    position = m_autil.mk_sub(b, m_autil.mk_int(offset));
    result = str().mk_concat(as.size() - offset, as.data() + offset, as[0]->get_sort());
    result = str().mk_substr(result, position, c);
    return BR_REWRITE3;
}

bool seq_rewriter::get_lengths(expr* e, expr_ref_vector& lens, rational& pos) {
    expr* arg = nullptr, *e1 = nullptr, *e2 = nullptr;
    rational pos1;
    if (m_autil.is_add(e)) {
        for (expr* arg1 : *to_app(e)) {
            if (!get_lengths(arg1, lens, pos)) 
                return false;
        }
    }
    else if (str().is_length(e, arg)) {
        lens.push_back(arg);
    }
    else if (m_autil.is_mul(e, e1, e2) && m_autil.is_numeral(e1, pos1) && str().is_length(e2, arg) && 0 <= pos1 && pos1 <= 10) {
        while (pos1 > 0) {
            lens.push_back(arg);
            pos1 -= rational(1);
        }
    }
    else if (m_autil.is_numeral(e, pos1)) {
        pos += pos1;
    }
    else {
        return false;
    }
    return true;
}

bool seq_rewriter::cannot_contain_suffix(expr* a, expr* b) {
    
    if (str().is_unit(a) && str().is_unit(b) && m().are_distinct(a, b)) {
        return true;
    }
    zstring A, B;
    if (str().is_string(a, A) && str().is_string(b, B)) {
        // some prefix of a is a suffix of b
        bool found = false;
        for (unsigned i = 1; !found && i <= A.length(); ++i) {
            found = A.extract(0, i).suffixof(B);
        }
        return !found;
    }

    return false;
}


bool seq_rewriter::cannot_contain_prefix(expr* a, expr* b) {
    
    if (str().is_unit(a) && str().is_unit(b) && m().are_distinct(a, b)) {
        return true;
    }
    zstring A, B;
    if (str().is_string(a, A) && str().is_string(b, B)) {
        // some suffix of a is a prefix of b
        bool found = false;
        for (unsigned i = 0; !found && i < A.length(); ++i) {
            found = A.extract(i, A.length()-i).suffixof(B);
        }
        return !found;
    }

    return false;
}



br_status seq_rewriter::mk_seq_contains(expr* a, expr* b, expr_ref& result) {
    zstring c, d;
    if (str().is_string(a, c) && str().is_string(b, d)) {
        result = m().mk_bool_val(c.contains(d));
        return BR_DONE;
    }
    expr* x = nullptr, *y, *z;
    if (str().is_extract(b, x, y, z) && x == a) {
        result = m().mk_true();
        return BR_DONE;
    }

    // check if subsequence of a is in b.
    expr_ref_vector as(m()), bs(m());
    str().get_concat_units(a, as);
    str().get_concat_units(b, bs);
    
    TRACE("seq", tout << mk_pp(a, m()) << " contains " << mk_pp(b, m()) << "\n";);
   
    if (bs.empty()) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (as.empty()) {
        result = str().mk_is_empty(b);
        return BR_REWRITE2;
    }

    for (unsigned i = 0; bs.size() + i <= as.size(); ++i) {
        unsigned j = 0;
        for (; j < bs.size() && as.get(j+i) == bs.get(j); ++j) {};
        if (j == bs.size()) {
            result = m().mk_true();
            return BR_DONE;
        }
    }
    std::function<bool(expr*)> is_value = [&](expr* e) { return m().is_value(e); };
    if (bs.forall(is_value) && as.forall(is_value)) {
        result = m().mk_false();
        return BR_DONE;
    }

    unsigned lenA = 0, lenB = 0;
    bool lA = min_length(as, lenA);
    if (lA) {
        min_length(bs, lenB);
        if (lenB > lenA) {
            result = m().mk_false();
            return BR_DONE;
        }
    }

    unsigned offs = 0;
    unsigned sz = as.size();
    expr* b0 = bs.get(0);
    expr* bL = bs.get(bs.size()-1);
    for (; offs < as.size() && cannot_contain_prefix(as[offs].get(), b0); ++offs) {}
    for (; sz > offs && cannot_contain_suffix(as.get(sz-1), bL); --sz) {}
    if (offs == sz) {
        result = str().mk_is_empty(b);
        return BR_REWRITE2;
    }
    if (offs > 0 || sz < as.size()) {
        SASSERT(sz > offs);
        result = str().mk_contains(str().mk_concat(sz-offs, as.data()+offs, a->get_sort()), b);
        return BR_REWRITE2;
    }    

    std::function<bool(expr*)> is_unit = [&](expr *e) { return str().is_unit(e); };

    if (bs.forall(is_unit) && as.forall(is_unit)) {
        expr_ref_vector ors(m());
        for (unsigned i = 0; i + bs.size() <= as.size(); ++i) {
            expr_ref_vector ands(m());
            for (unsigned j = 0; j < bs.size(); ++j) {
                ands.push_back(m().mk_eq(as.get(i + j), bs.get(j)));
            }
            ors.push_back(::mk_and(ands));
        }
        result = ::mk_or(ors);
        return BR_REWRITE_FULL;
    }

    if (bs.size() == 1 && bs.forall(is_unit) && as.size() > 1) {
        expr_ref_vector ors(m());        
        for (expr* ai : as) {
            ors.push_back(str().mk_contains(ai, bs.get(0)));
        }
        result = ::mk_or(ors);
        return BR_REWRITE_FULL;
    }
    
    expr_ref ra(a, m());
    if (is_unit(b) && m().is_value(b) && 
        reduce_by_char(ra, b, 4)) {
        result = str().mk_contains(ra, b);
        return BR_REWRITE1;
    }
    return BR_FAILED;
}

bool seq_rewriter::reduce_by_char(expr_ref& r, expr* ch, unsigned depth) {
    expr* x = nullptr, *y = nullptr, *z = nullptr;
    if (str().is_replace(r, x, y, z) && 
        str().is_unit(y) && m().is_value(y) &&
        str().is_unit(z) && m().is_value(z) && 
        ch != y && ch != z) {
        r = x;
        if (depth > 0)
            reduce_by_char(r, ch, depth - 1);
        return true;
    }
    if (depth > 0 && str().is_concat(r)) {
        bool reduced = false;
        expr_ref_vector args(m());
        for (expr* e : *to_app(r)) {
            expr_ref tmp(e, m());
            if (reduce_by_char(tmp, ch, depth - 1))
                reduced = true;
            args.push_back(tmp);
        }
        if (reduced) 
            r = str().mk_concat(args, args.get(0)->get_sort());
        return reduced;
    }
    if (depth > 0 && str().is_extract(r, x, y, z)) {
        expr_ref tmp(x, m());
        if (reduce_by_char(tmp, ch, depth - 1)) {
            r = str().mk_substr(tmp, y, z);
            return true;
        }        
    }        
    return false;
}


/*
 * (str.at s i), constants s/i, i < 0 or i >= |s| ==> (str.at s i) = ""
 */
br_status seq_rewriter::mk_seq_at(expr* a, expr* b, expr_ref& result) {
    zstring c;
    rational r;
    expr_ref_vector lens(m());
    sort* sort_a = a->get_sort();
    if (!get_lengths(b, lens, r)) {
        return BR_FAILED;
    }
    if (lens.empty() && r.is_neg()) {
        result = str().mk_empty(sort_a);
        return BR_DONE;
    } 

    expr* a2 = nullptr, *i2 = nullptr;
    if (lens.empty() && str().is_at(a, a2, i2)) {
        if (r.is_pos()) {
            result = str().mk_empty(sort_a);
        }
        else {
            result = a;
        }
        return BR_DONE;            
    }

    m_lhs.reset();
    str().get_concat_units(a, m_lhs);

    if (m_lhs.empty()) {
        result = str().mk_empty(a->get_sort());
        return BR_DONE;        
    }
    
    unsigned i = 0;
    for (; i < m_lhs.size(); ++i) {
        expr* lhs = m_lhs.get(i);
        if (lens.contains(lhs) && !r.is_neg()) {
            lens.erase(lhs);
        }
        else if (str().is_unit(lhs) && r.is_zero() && lens.empty()) {
            result = lhs;
            return BR_REWRITE1;
        }
        else if (str().is_unit(lhs) && r.is_pos()) {
            r -= rational(1);
        }
        else {
            break;
        }
    }
    if (i == 0) {
        return BR_FAILED;
    }
    if (m_lhs.size() == i) {
        result = str().mk_empty(sort_a);
        return BR_DONE;
    }
    expr_ref pos(m_autil.mk_int(r), m());
    for (expr* rhs : lens) {
        pos = m_autil.mk_add(pos, str().mk_length(rhs));
    }
    result = str().mk_concat(m_lhs.size() - i , m_lhs.data() + i, sort_a);
    result = str().mk_at(result, pos);
    return BR_REWRITE2;   
}

br_status seq_rewriter::mk_seq_nth(expr* a, expr* b, expr_ref& result) {

    rational pos1, pos2;
    expr* s = nullptr, *p = nullptr, *len = nullptr;
    if (str().is_unit(a, s) && m_autil.is_numeral(b, pos1) && pos1.is_zero()) {
        result = s;
        return BR_DONE;
    }
    if (str().is_extract(a, s, p, len) && m_autil.is_numeral(p, pos1)) {
        expr_ref_vector lens(m());
        rational pos2;
        if (get_lengths(len, lens, pos2) && (pos1 == -pos2) && (lens.size() == 1) && (lens.get(0) == s)) {
            expr_ref idx(m_autil.mk_int(pos1), m());
            idx = m_autil.mk_add(b, idx);
            expr* es[2] = { s, idx };
            result = m().mk_app(m_util.get_family_id(), OP_SEQ_NTH, 2, es);
            return BR_REWRITE_FULL;
        }
    }

    expr* es[2] = { a, b};
    expr* la = str().mk_length(a);
    result = m().mk_ite(m().mk_and(m_autil.mk_ge(b, zero()), m().mk_not(m_autil.mk_le(la, b))), 
                        m().mk_app(m_util.get_family_id(), OP_SEQ_NTH_I, 2, es), 
                        m().mk_app(m_util.get_family_id(), OP_SEQ_NTH_U, 2, es));
    return BR_REWRITE_FULL;
}


br_status seq_rewriter::mk_seq_nth_i(expr* a, expr* b, expr_ref& result) {
    zstring c;
    rational r;
    if (!m_autil.is_numeral(b, r) || !r.is_unsigned()) {
        return BR_FAILED;
    }
    unsigned len = r.get_unsigned();

    expr* a2, *i2;
    if (len == 0 && str().is_at(a, a2, i2) && m_autil.is_numeral(i2, r) && r.is_zero()) {
        result = str().mk_nth_i(a2, i2);
        return BR_REWRITE1;
    }

    expr_ref_vector as(m());
    str().get_concat_units(a, as);

    for (unsigned i = 0; i < as.size(); ++i) {
        expr* a = as.get(i), *u = nullptr;
        if (str().is_unit(a, u)) {
            if (len == i) {
                result = u;
                return BR_DONE;
            }            
        }
        else {
            return BR_FAILED;
        }
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_last_index(expr* a, expr* b, expr_ref& result) {
    zstring s1, s2;
    bool isc1 = str().is_string(a, s1);
    bool isc2 = str().is_string(b, s2);
    if (isc1 && isc2) {
        int idx = s1.last_indexof(s2);
        result = m_autil.mk_numeral(rational(idx), true);
        return BR_DONE;
    }
    return BR_FAILED;
}

/**

  Index of first occurrence of second string in first one starting at 
  the position specified by the third argument.
  (str.indexof s t i), with 0 <= i <= |s| is the position of the first
  occurrence of t in s at or after position i, if any. 
  Otherwise, it is -1. Note that the result is i whenever i is within
  the range [0, |s|] and t is empty.
  (str.indexof String String Int Int)

   indexof(s, b, c) -> -1 if c < 0
   indexof(a, "", 0) -> if a = "" then 0 else -1
   indexof("", b, r) -> if b = "" and r = 0 then 0 else -1
   indexof(a, "", x) -> if 0 <= x <= len(a) then x else - 1
   indexof(unit(x)+a, b, r+1) -> indexof(a, b, r) 
   indexof(unit(x)+a, unit(y)+b, 0) -> indexof(a,unit(y)+b, 0) if x != y
   indexof(substr(x,y,len1), z, len2) -> -1 if len2 > len1
*/
br_status seq_rewriter::mk_seq_index(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s1, s2;
    rational r;
    bool isc1 = str().is_string(a, s1);
    bool isc2 = str().is_string(b, s2);
    sort* sort_a = a->get_sort();

    if (isc1 && isc2 && m_autil.is_numeral(c, r) && r.is_unsigned()) {
        int idx = s1.indexofu(s2, r.get_unsigned());
        result = m_autil.mk_int(idx);
        return BR_DONE;
    }
    if (m_autil.is_numeral(c, r) && r.is_neg()) {
        result = m_autil.mk_int(-1);
        return BR_DONE;
    }
    
    if (str().is_empty(b) && m_autil.is_numeral(c, r) && r.is_zero()) {
        result = c;
        return BR_DONE;
    }

    if (str().is_empty(b)) {
        result = m().mk_ite(m().mk_and(m_autil.mk_le(m_autil.mk_int(0), c),
                                       m_autil.mk_le(c, str().mk_length(a))),
                            c,
                            m_autil.mk_int(-1));
        return BR_REWRITE2;
    }

    
    if (str().is_empty(a)) {
        expr* emp = str().mk_is_empty(b);
        result = m().mk_ite(m().mk_and(m().mk_eq(c, zero()), emp), zero(), minus_one());
        return BR_REWRITE2;
    }

    if (a == b) {
        if (m_autil.is_numeral(c, r)) {
            result = r.is_zero() ? zero() : minus_one();            
            return BR_DONE;
        }
        else {
            result = m().mk_ite(m().mk_eq(zero(), c), zero(), minus_one());
            return BR_REWRITE2;
        }
    }
    expr* x = nullptr, *y = nullptr, *len1 = nullptr;
    rational r1, r2;
    if (str().is_extract(a, x, y, len1) && m_autil.is_numeral(len1, r1) && 
        m_autil.is_numeral(c, r2) && r2 > r1) {
        result = minus_one();
        return BR_DONE;
    }

    expr_ref_vector as(m()), bs(m());
    str().get_concat_units(a, as);
    unsigned i = 0;
    if (m_autil.is_numeral(c, r)) {
        i = 0;
        while (r.is_pos() && i < as.size() && str().is_unit(as.get(i))) {
            r -= rational(1);
            ++i;
        }
        if (i > 0) {
            expr_ref a1(m());
            a1 = str().mk_concat(as.size() - i, as.data() + i, sort_a);
            result = str().mk_index(a1, b, m_autil.mk_int(r));
            result = m().mk_ite(m_autil.mk_ge(result, zero()), m_autil.mk_add(m_autil.mk_int(i), result), minus_one());
            return BR_REWRITE_FULL;
        }
    }
    bool is_zero = m_autil.is_numeral(c, r) && r.is_zero();
    str().get_concat_units(b, bs);
    i = 0;
    while (is_zero && i < as.size() && 
           0 < bs.size() && 
           str().is_unit(as.get(i)) && 
           str().is_unit(bs.get(0)) &&
           m().are_distinct(as.get(i), bs.get(0))) {
        ++i;
    }
    if (i > 0) {
        result = str().mk_index(
            str().mk_concat(as.size() - i, as.data() + i, sort_a), b, c);
        result = m().mk_ite(m_autil.mk_ge(result, zero()), m_autil.mk_add(m_autil.mk_int(i), result), minus_one());
        return BR_REWRITE_FULL;
    }

    switch (compare_lengths(as, bs)) {
    case shorter_c:
        if (is_zero) {
            result = minus_one();
            return BR_DONE;
        }
        break;
    case same_length_c:
        result = m().mk_ite(m_autil.mk_le(c, minus_one()), minus_one(), 
                            m().mk_ite(m().mk_eq(c, zero()), 
                                       m().mk_ite(m().mk_eq(a, b), zero(), minus_one()),
                                       minus_one()));
        return BR_REWRITE_FULL;
    default:
        break;
    }
    if (is_zero && !as.empty() && str().is_unit(as.get(0))) {
        expr_ref a1(str().mk_concat(as.size() - 1, as.data() + 1, as[0]->get_sort()), m());
        expr_ref b1(str().mk_index(a1, b, c), m());
        result = m().mk_ite(str().mk_prefix(b, a), zero(), 
                            m().mk_ite(m_autil.mk_ge(b1, zero()), m_autil.mk_add(one(), b1), minus_one()));
        return BR_REWRITE3;
    }
    expr_ref ra(a, m());
    if (str().is_unit(b) && m().is_value(b) && 
        reduce_by_char(ra, b, 4)) {
        result = str().mk_index(ra, b, c);
        return BR_REWRITE1;
    }

    // Enhancement: walk segments of a, determine which segments must overlap, must not overlap, may overlap.
    return BR_FAILED;
}

seq_rewriter::length_comparison seq_rewriter::compare_lengths(unsigned sza, expr* const* as, unsigned szb, expr* const* bs) {
    unsigned units_a = 0, units_b = 0, k = 0;
    obj_map<expr, unsigned> mults;
    bool b_has_foreign = false;
    for (unsigned i = 0; i < sza; ++i) {
        if (str().is_unit(as[i]))
            units_a++;
        else 
            mults.insert_if_not_there(as[i], 0)++;
    }
    for (unsigned i = 0; i < szb; ++i) {
        if (str().is_unit(bs[i]))
            units_b++;
        else if (mults.find(bs[i], k)) {
            --k;
            if (k == 0) {
                mults.erase(bs[i]);
            }
            else {
                mults.insert(bs[i], k);
            }
        }
        else {
            b_has_foreign = true;
        }
    }
    if (units_a > units_b && !b_has_foreign) {
        return longer_c;
    }
    if (units_a == units_b && !b_has_foreign && mults.empty()) {
        return same_length_c;
    }
    if (units_b > units_a && mults.empty()) {
        return shorter_c;
    }
    return unknown_c;
}


//  (str.replace s t t') is the string obtained by replacing the first occurrence 
//  of t in s, if any, by t'. Note that if t is empty, the result is to prepend
//  t' to s; also, if t does not occur in s then the result is s.

br_status seq_rewriter::mk_seq_replace(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s1, s2, s3;
    sort* sort_a = a->get_sort();
    if (str().is_string(a, s1) && str().is_string(b, s2) && 
        str().is_string(c, s3)) {
        result = str().mk_string(s1.replace(s2, s3));
        return BR_DONE;
    }
    if (b == c) {
        result = a;
        return BR_DONE;
    }
    if (a == b) {
        result = c;
        return BR_DONE;
    }
    if (str().is_empty(b)) {
        result = str().mk_concat(c, a);
        return BR_REWRITE1;
    }
    if (str().is_empty(a) && str().is_empty(c)) {
        result = a;
        return BR_DONE;
    }

    m_lhs.reset();
    str().get_concat(a, m_lhs);

    // a = "", |b| > 0 -> replace("",b,c) = ""
    if (m_lhs.empty()) {
        unsigned len = 0;
        str().get_concat(b, m_lhs);
        min_length(m_lhs, len);
        if (len > 0) {
            result = a;
            return BR_DONE;
        }
        return BR_FAILED;
    }

    // a := b + rest
    if (m_lhs.get(0) == b) {
        m_lhs[0] = c;
        result = str().mk_concat(m_lhs.size(), m_lhs.data(), sort_a);
        return BR_REWRITE1;
    }

    // a : a' + rest string, b is string, c is string, a' contains b
    if (str().is_string(b, s2) && str().is_string(c, s3) && 
        str().is_string(m_lhs.get(0), s1) && s1.contains(s2) ) {
        m_lhs[0] = str().mk_string(s1.replace(s2, s3));
        result = str().mk_concat(m_lhs.size(), m_lhs.data(), sort_a);
        return BR_REWRITE1;
    }
    m_lhs.reset();
    m_rhs.reset();
    str().get_concat_units(a, m_lhs);
    str().get_concat_units(b, m_rhs);
    if (m_rhs.empty()) {
        result = str().mk_concat(c, a);
        return BR_REWRITE1;
    }

    // is b a prefix of m_lhs at position i?
    auto compare_at_i = [&](unsigned i) {
        for (unsigned j = 0; j < m_rhs.size() && i + j < m_lhs.size(); ++j) {
            expr* b0 = m_rhs.get(j);
            expr* a0 = m_lhs.get(i + j);
            if (m().are_equal(a0, b0))
                continue;
            if (!str().is_unit(b0) || !str().is_unit(a0)) 
                return l_undef;
            if (m().are_distinct(a0, b0)) 
                return l_false;
            return l_undef;
        }
        return l_true;
    };

    unsigned i = 0;
    for (; i < m_lhs.size(); ++i) {
        lbool cmp = compare_at_i(i);
        if (cmp == l_false && str().is_unit(m_lhs.get(i)))
            continue;
        if (cmp == l_true && m_lhs.size() < i + m_rhs.size()) {
            expr_ref a1(str().mk_concat(i, m_lhs.data(), sort_a), m());
            expr_ref a2(str().mk_concat(m_lhs.size()-i, m_lhs.data()+i, sort_a), m());
            result = m().mk_ite(m().mk_eq(a2, b), str().mk_concat(a1, c), a);
            return BR_REWRITE_FULL;            
        }
        if (cmp == l_true) {
            expr_ref_vector es(m());
            es.append(i, m_lhs.data());
            es.push_back(c);
            es.append(m_lhs.size()-i-m_rhs.size(), m_lhs.data()+i+m_rhs.size());
            result = str().mk_concat(es, sort_a);
            return BR_REWRITE_FULL;        
        }
        break;
    }

    if (i > 0) {
        expr_ref a1(str().mk_concat(i, m_lhs.data(), sort_a), m());
        expr_ref a2(str().mk_concat(m_lhs.size()-i, m_lhs.data()+i, sort_a), m());
        result = str().mk_concat(a1, str().mk_replace(a2, b, c));
        return BR_REWRITE_FULL;        
    }


    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_replace_all(expr* a, expr* b, expr* c, expr_ref& result) {
    if (str().is_empty(b) || b == c) {
        result = a;
        return BR_DONE;
    } 
    if (a == b) {
        result = m().mk_ite(str().mk_is_empty(b), str().mk_empty(a->get_sort()), c);
        return BR_REWRITE1;
    }
    zstring s1, s2;
    if (str().is_string(a, s1) && str().is_string(b, s2)) {
        SASSERT(s2.length() > 0);
        if (s1.length() < s2.length()) {
            result = a;
            return BR_DONE;
        }
        expr_ref_vector strs(m());
        for (unsigned i = 0; i < s1.length(); ++i) {
            if (s1.length() >= s2.length() + i && 
                s2 == s1.extract(i, s2.length())) {
                strs.push_back(c);
                i += s2.length() - 1;
            }
            else 
                strs.push_back(str().mk_unit(str().mk_char(s1, i)));
        }
        result = str().mk_concat(strs, a->get_sort());
        return BR_REWRITE_FULL;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_replace_re_all(expr* a, expr* b, expr* c, expr_ref& result) {
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_replace_re(expr* a, expr* b, expr* c, expr_ref& result) {
    return BR_FAILED;
}


br_status seq_rewriter::mk_seq_prefix(expr* a, expr* b, expr_ref& result) {
    TRACE("seq", tout << mk_pp(a, m()) << " " << mk_pp(b, m()) << "\n";);
    zstring s1, s2;
    bool isc1 = str().is_string(a, s1);
    bool isc2 = str().is_string(b, s2);
    sort* sort_a = a->get_sort();
    if (isc1 && isc2) {
        result = m().mk_bool_val(s1.prefixof(s2));
        TRACE("seq", tout << result << "\n";);
        return BR_DONE;
    }
    if (str().is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    expr* a1 = str().get_leftmost_concat(a);
    expr* b1 = str().get_leftmost_concat(b);
    isc1 = str().is_string(a1, s1);
    isc2 = str().is_string(b1, s2);
    expr_ref_vector as(m()), bs(m());

    if (a1 != b1 && isc1 && isc2) {
        if (s1.length() <= s2.length()) {
            if (s1.prefixof(s2)) {
                if (a == a1) {
                    result = m().mk_true();
                    TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                    return BR_DONE;
                }               
                str().get_concat(a, as);
                str().get_concat(b, bs);
                SASSERT(as.size() > 1);
                s2 = s2.extract(s1.length(), s2.length()-s1.length());
                bs[0] = str().mk_string(s2);
                result = str().mk_prefix(str().mk_concat(as.size()-1, as.data()+1, sort_a),
                                              str().mk_concat(bs.size(), bs.data(), sort_a));
                TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                return BR_REWRITE_FULL;
            }
            else {
                result = m().mk_false();
                TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                return BR_DONE;
            }
        }
        else {
            if (s2.prefixof(s1)) {
                if (b == b1) {
                    result = m().mk_false();
                    TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                    return BR_DONE;
                }
                str().get_concat(a, as);
                str().get_concat(b, bs);
                SASSERT(bs.size() > 1);
                s1 = s1.extract(s2.length(), s1.length() - s2.length());
                as[0] = str().mk_string(s1);
                result = str().mk_prefix(str().mk_concat(as.size(), as.data(), sort_a),
                                              str().mk_concat(bs.size()-1, bs.data()+1, sort_a));
                TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                return BR_REWRITE_FULL;                
            }
            else {
                result = m().mk_false();
                TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                return BR_DONE;
            }
        }        
    }
    str().get_concat_units(a, as);
    str().get_concat_units(b, bs);
    unsigned i = 0;
    expr_ref_vector eqs(m());
    for (; i < as.size() && i < bs.size(); ++i) {
        expr* ai = as.get(i), *bi = bs.get(i);
        if (m().are_equal(ai, bi)) {
            continue;
        }
        if (m().are_distinct(ai, bi)) {
            result = m().mk_false();
            return BR_DONE;
        }
        if (str().is_unit(ai) && str().is_unit(bi)) {
            eqs.push_back(m().mk_eq(ai, bi));
            continue;
        }
        break;
    }
    if (i == as.size()) {
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }
    SASSERT(i < as.size());
    if (i == bs.size()) {
        for (unsigned j = i; j < as.size(); ++j) {
            eqs.push_back(str().mk_is_empty(as.get(j)));
        }
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }
    if (i > 0) {
        SASSERT(i < as.size() && i < bs.size());
        a = str().mk_concat(as.size() - i, as.data() + i, sort_a);
        b = str().mk_concat(bs.size() - i, bs.data() + i, sort_a); 
        eqs.push_back(str().mk_prefix(a, b));
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }

    expr* a2 = nullptr, *a3 = nullptr;    
    if (str().is_replace(a, a1, a2, a3) && a1 == a3 && a2 == b) {
        // TBD: generalize to when a1 is a prefix of a3?
        result = str().mk_prefix(a1, b);
        return BR_DONE;
    }


    unsigned len_a;
    rational len_b;
    if (max_length(b, len_b)) {
        min_length(a, len_a);
        if (len_b <= len_a) {
            result = m().mk_eq(a, b);
            return BR_REWRITE1;
        }
    }

    return BR_FAILED;    
}

br_status seq_rewriter::mk_seq_suffix(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = m().mk_true();
        return BR_DONE;
    }
    sort* sort_a = a->get_sort();
    if (str().is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (str().is_empty(b)) {
        result = str().mk_is_empty(a);
        return BR_REWRITE3;
    }
    
    expr_ref_vector as(m()), bs(m()), eqs(m());
    str().get_concat_units(a, as);
    str().get_concat_units(b, bs);
    unsigned i = 1, sza = as.size(), szb = bs.size();
    for (; i <= sza && i <= szb; ++i) {
        expr* ai = as.get(sza-i), *bi = bs.get(szb-i);
        if (m().are_equal(ai, bi)) {
            continue;
        }
        if (m().are_distinct(ai, bi)) {
            result = m().mk_false();
            return BR_DONE;
        }
        if (str().is_unit(ai) && str().is_unit(bi)) {
            eqs.push_back(m().mk_eq(ai, bi));
            continue;
        }
        break;
    }
    if (i > sza) {
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }
    if (i > szb) {
        for (unsigned j = i; j <= sza; ++j) {
            expr* aj = as.get(sza-j);
            eqs.push_back(str().mk_is_empty(aj));
        }
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }

    if (i > 1) {
        SASSERT(i <= sza && i <= szb);
        a = str().mk_concat(sza - i + 1, as.data(), sort_a);
        b = str().mk_concat(szb - i + 1, bs.data(), sort_a);
        eqs.push_back(str().mk_suffix(a, b));
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }

    expr* a1 = nullptr, *a2 = nullptr, *a3 = nullptr;    
    if (str().is_replace(a, a1, a2, a3) && a1 == a3 && a2 == b) {
        // TBD: generalize to when a1 is a prefix of a3?
        result = str().mk_suffix(a1, b);
        return BR_DONE;
    }
    unsigned len_a;
    rational len_b;
    if (max_length(b, len_b)) {
        min_length(a, len_a);
        if (len_b <= len_a) {
            result = m().mk_eq(a, b);
            return BR_REWRITE1;
        }
    }

    return BR_FAILED;
}

br_status seq_rewriter::mk_str_units(func_decl* f, expr_ref& result) {
    zstring s;
    VERIFY(str().is_string(f, s));
    expr_ref_vector es(m());
    unsigned sz = s.length();
    for (unsigned j = 0; j < sz; ++j) {
        es.push_back(str().mk_unit(str().mk_char(s, j)));
    }        
    result = str().mk_concat(es, f->get_range());    
    return BR_DONE;
}

br_status seq_rewriter::mk_str_le(expr* a, expr* b, expr_ref& result) {
    result = m().mk_not(str().mk_lex_lt(b, a));
    return BR_REWRITE2;
}

br_status seq_rewriter::mk_str_lt(expr* a, expr* b, expr_ref& result) {
    zstring as, bs;
    if (str().is_string(a, as) && str().is_string(b, bs)) {
        unsigned sz = std::min(as.length(), bs.length());
        for (unsigned i = 0; i < sz; ++i) {
            if (as[i] < bs[i]) {
                result = m().mk_true();
                return BR_DONE;
            }
            if (as[i] > bs[i]) {
                result = m().mk_false();
                return BR_DONE;
            }
        }
        result = m().mk_bool_val(as.length() < bs.length());
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_from_code(expr* a, expr_ref& result) {
    rational r;
    if (m_autil.is_numeral(a, r)) {
        if (r.is_neg() || r > u().max_char()) {
            result = str().mk_string(zstring());
        }
        else {
            unsigned num = r.get_unsigned();
            zstring s(1, &num);
            result = str().mk_string(s);
        }
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_to_code(expr* a, expr_ref& result) {
    zstring s;
    if (str().is_string(a, s)) {
        if (s.length() == 1) 
            result = m_autil.mk_int(s[0]);
        else
            result = m_autil.mk_int(-1);
        return BR_DONE;
    }    
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_is_digit(expr* a, expr_ref& result) {
    zstring s;
    if (str().is_string(a, s)) {
        if (s.length() == 1 && '0' <= s[0] && s[0] <= '9')
            result = m().mk_true();
        else
            result = m().mk_false();
        return BR_DONE;
    }
    if (str().is_empty(a)) {
        result = m().mk_false();
        return BR_DONE;
    }
    // when a has length > 1 -> false
    // when a is a unit character -> evaluate
   
    return BR_FAILED;
}


br_status seq_rewriter::mk_str_ubv2s(expr* a, expr_ref& result) {
    bv_util bv(m());
    rational val;
    if (bv.is_numeral(a, val)) {
        result = str().mk_string(zstring(val));
        return BR_DONE;
    }
    return BR_FAILED;
}


br_status seq_rewriter::mk_str_itos(expr* a, expr_ref& result) {
    rational r;
    if (m_autil.is_numeral(a, r)) {
        if (r.is_int() && !r.is_neg()) {
            result = str().mk_string(zstring(r));
        }
        else {
            result = str().mk_string(zstring());
        }
        return BR_DONE;
    }
    // itos(stoi(s)) -> if s = '0' or .... or s = '9' then s else ""
    // when |s| <= 1
    expr* b = nullptr;
    
    if (str().is_stoi(a, b) && max_length(b, r) && r <= 1) {
        expr_ref_vector eqs(m());
        for (unsigned i = 0; i < 10; ++i) {
            zstring s('0' + i);
            eqs.push_back(m().mk_eq(b, str().mk_string(s)));
        }
        result = m().mk_or(eqs);
        result = m().mk_ite(result, b, str().mk_string(zstring()));
        return BR_REWRITE2;
    }
    return BR_FAILED;
}

/**
   \brief rewrite str.to.int according to the rules:
   - if the expression is a string which is a non-empty 
     sequence of digits 0-9 extract the corresponding numeral.
   - if the expression is a string that contains any other character 
     or is empty, produce -1
   - if the expression is int.to.str(x) produce
      ite(x >= 0, x, -1)
     
*/
br_status seq_rewriter::mk_str_stoi(expr* a, expr_ref& result) {
    zstring s;
    if (str().is_string(a, s)) {
        std::string s1 = s.encode();
        if (s1.length() == 0) {
            result = minus_one();
            return BR_DONE;
        } 
        for (unsigned i = 0; i < s1.length(); ++i) {
            if (!('0' <= s1[i] && s1[i] <= '9')) {
                result = minus_one();
                return BR_DONE;
            }
        }
        rational r(s1.c_str());
        result = m_autil.mk_numeral(r, true);
        return BR_DONE;
    }
    expr* b;
    if (str().is_itos(a, b)) {
        result = m().mk_ite(m_autil.mk_ge(b, zero()), b, minus_one());
        return BR_DONE;
    }
    if (str().is_ubv2s(a, b)) {
        bv_util bv(m());
        result = bv.mk_bv2int(b);
        return BR_DONE;
    }
    
    expr* c = nullptr, *t = nullptr, *e = nullptr;
    if (m().is_ite(a, c, t, e)) {
        result = m().mk_ite(c, str().mk_stoi(t), str().mk_stoi(e));
        return BR_REWRITE_FULL;
    }

    expr* u = nullptr;
    unsigned ch = 0;
    if (str().is_unit(a, u) && m_util.is_const_char(u, ch)) {
        if ('0' <= ch && ch <= '9') {
            result = m_autil.mk_int(ch - '0');
        }
        else {
            result = m_autil.mk_int(-1);
        }
        return BR_DONE;
    }        

    expr_ref_vector as(m());
    str().get_concat_units(a, as);
    if (as.empty()) {
        result = m_autil.mk_int(-1);
        return BR_DONE;
    }
    if (str().is_unit(as.back())) {
        // if head = "" then tail else
        // if tail < 0 then tail else 
        // if stoi(head) >= 0 and then stoi(head)*10+tail else -1
        expr_ref tail(str().mk_stoi(as.back()), m());
        expr_ref head(str().mk_concat(as.size() - 1, as.data(), a->get_sort()), m());
        expr_ref stoi_head(str().mk_stoi(head), m());
        result = m().mk_ite(m_autil.mk_ge(stoi_head, m_autil.mk_int(0)), 
                            m_autil.mk_add(m_autil.mk_mul(m_autil.mk_int(10), stoi_head), tail),
                            m_autil.mk_int(-1));
        
        result = m().mk_ite(m_autil.mk_ge(tail, m_autil.mk_int(0)), 
                            result,
                            tail);
        result = m().mk_ite(str().mk_is_empty(head), 
                            tail,
                            result);
        return BR_REWRITE_FULL;
    }
    if (str().is_unit(as.get(0), u) && m_util.is_const_char(u, ch) && '0' == ch) {
        result = str().mk_concat(as.size() - 1, as.data() + 1, as[0]->get_sort());
        result = m().mk_ite(str().mk_is_empty(result),
                            m_autil.mk_int(0),
                            str().mk_stoi(result));
        return BR_REWRITE_FULL;
    }

    return BR_FAILED;
}

void seq_rewriter::add_next(u_map<expr*>& next, expr_ref_vector& trail, unsigned idx, expr* cond) {
    expr* acc;
    if (!m().is_true(cond) && next.find(idx, acc)) {              
        expr* args[2] = { cond, acc };
        cond = mk_or(m(), 2, args);
    }
    trail.push_back(cond);
    next.insert(idx, cond);   

}

bool seq_rewriter::is_sequence(eautomaton& aut, expr_ref_vector& seq) {
    seq.reset();
    unsigned state = aut.init();
    uint_set visited;
    eautomaton::moves mvs;
    unsigned_vector states;
    aut.get_epsilon_closure(state, states);
    bool has_final = false;
    for (unsigned i = 0; !has_final && i < states.size(); ++i) {
        has_final = aut.is_final_state(states[i]);
    }
    aut.get_moves_from(state, mvs, true);       
    while (!has_final) {
        if (mvs.size() != 1) {
            return false;
        }
        if (visited.contains(state)) {
            return false;
        }
        if (aut.is_final_state(mvs[0].src())) {
            return false;
        }
        visited.insert(state);
        sym_expr* t = mvs[0].t();
        if (!t || !t->is_char()) {
            return false;
        }
        seq.push_back(str().mk_unit(t->get_char()));
        state = mvs[0].dst();
        mvs.reset();
        aut.get_moves_from(state, mvs, true);
        states.reset();
        has_final = false;
        aut.get_epsilon_closure(state, states);
        for (unsigned i = 0; !has_final && i < states.size(); ++i) {
            has_final = aut.is_final_state(states[i]);
        }
    }
    return mvs.empty();
}

bool seq_rewriter::is_sequence(expr* e, expr_ref_vector& seq) {
    seq.reset();
    zstring s;
    ptr_vector<expr> todo;
    expr *e1, *e2;
    todo.push_back(e);
    while (!todo.empty()) {
        e = todo.back();
        todo.pop_back();
        if (str().is_string(e, s)) {
            for (unsigned i = 0; i < s.length(); ++i) {
                seq.push_back(str().mk_char(s, i));
            }
        }
        else if (str().is_empty(e)) {
            continue;
        }
        else if (str().is_unit(e, e1)) {
            seq.push_back(e1);
        }
        else if (str().is_concat(e, e1, e2)) {
            todo.push_back(e2);
            todo.push_back(e1);
        }
        else {
            return false;
        }
    }
    return true;
}

/*
    s = head + tail where |head| = 1
*/
bool seq_rewriter::get_head_tail(expr* s, expr_ref& head, expr_ref& tail) {
    expr* h = nullptr, *t = nullptr;
    zstring s1;
    if (str().is_unit(s, h)) {
        head = h;
        tail = str().mk_empty(s->get_sort());
        return true;
    }
    if (str().is_string(s, s1) && s1.length() > 0) {
        head = m_util.mk_char(s1[0]);
        tail = str().mk_string(s1.extract(1, s1.length()));
        return true;
    }
    if (str().is_concat(s, h, t) && get_head_tail(h, head, tail)) {
        tail = mk_seq_concat(tail, t);
        return true;
    }
    return false;
}

/*
    s = head + tail where |tail| = 1
*/
bool seq_rewriter::get_head_tail_reversed(expr* s, expr_ref& head, expr_ref& tail) {
    expr* h = nullptr, *t = nullptr;
    zstring s1;
    if (str().is_unit(s, t)) {
        head = str().mk_empty(s->get_sort());
        tail = t;
        return true;
    }
    if (str().is_string(s, s1) && s1.length() > 0) {
        head = str().mk_string(s1.extract(0, s1.length() - 1));
        tail = m_util.mk_char(s1[s1.length() - 1]);
        return true;
    }
    if (str().is_concat(s, h, t) && get_head_tail_reversed(t, head, tail)) {
        head = mk_seq_concat(h, head);
        return true;
    }
    return false;
}

bool seq_rewriter::get_re_head_tail(expr* r, expr_ref& head, expr_ref& tail) {
    expr* r1 = nullptr, *r2 = nullptr;
    if (re().is_concat(r, r1, r2)) {
        head = r1;
        tail = r2;
        return re().min_length(r1) != UINT_MAX && re().max_length(r1) == re().min_length(r1);
    }
    return false;
}

bool seq_rewriter::get_re_head_tail_reversed(expr* r, expr_ref& head, expr_ref& tail) {
    expr* r1 = nullptr, *r2 = nullptr;
    if (re().is_concat(r, r1, r2)) {
        unsigned len = re().min_length(r2);
        if (len != UINT_MAX && re().max_length(r2) == len) {
            head = r1;
            tail = r2;
            return true;
        }
        if (get_re_head_tail_reversed(r2, head, tail)) {
            head = re().mk_concat(r1, head);
            return true;
        }
    }
    return false;
}


expr_ref seq_rewriter::re_and(expr* cond, expr* r) {
    expr_ref _cond(cond, m()), _r(r, m());
    if (m().is_true(cond))
        return expr_ref(r, m());    
    expr* re_empty = re().mk_empty(r->get_sort());
    if (m().is_false(cond))
        return expr_ref(re_empty, m());
    return expr_ref(m().mk_ite(cond, r, re_empty), m());
}

expr_ref seq_rewriter::re_predicate(expr* cond, sort* seq_sort) {
    expr_ref re_with_empty(re().mk_to_re(str().mk_empty(seq_sort)), m());
    return re_and(cond, re_with_empty);
}

expr_ref seq_rewriter::is_nullable(expr* r) {
    STRACE("seq_verbose", tout << "is_nullable: "
                               << mk_pp(r, m()) << std::endl;);
    expr_ref result(m_op_cache.find(_OP_RE_IS_NULLABLE, r, nullptr), m());
    if (!result) {
        result = is_nullable_rec(r);
        m_op_cache.insert(_OP_RE_IS_NULLABLE, r, nullptr, result);        
    }
    STRACE("seq_verbose", tout << "is_nullable result: "
                               << result << std::endl;);
    return result;
}

expr_ref seq_rewriter::is_nullable_rec(expr* r) {
    SASSERT(m_util.is_re(r) || m_util.is_seq(r));
    expr* r1 = nullptr, *r2 = nullptr, *cond = nullptr;
    sort* seq_sort = nullptr;
    unsigned lo = 0, hi = 0;
    zstring s1;
    expr_ref result(m());
    if (re().is_concat(r, r1, r2) ||
        re().is_intersection(r, r1, r2)) { 
        m_br.mk_and(is_nullable(r1), is_nullable(r2), result);
    }
    else if (re().is_union(r, r1, r2)) {
        m_br.mk_or(is_nullable(r1), is_nullable(r2), result);
    }
    else if (re().is_diff(r, r1, r2)) {
        m_br.mk_not(is_nullable(r2), result);
        m_br.mk_and(result, is_nullable(r1), result);
    }
    else if (re().is_star(r) || 
        re().is_opt(r) ||
        re().is_full_seq(r) ||
        (re().is_loop(r, r1, lo) && lo == 0) || 
        (re().is_loop(r, r1, lo, hi) && lo == 0)) {
        result = m().mk_true();
    }
    else if (re().is_full_char(r) ||
        re().is_empty(r) ||
        re().is_of_pred(r) ||
        re().is_range(r)) {
        result = m().mk_false();
    }
    else if (re().is_plus(r, r1) ||
        (re().is_loop(r, r1, lo) && lo > 0) ||
        (re().is_loop(r, r1, lo, hi) && lo > 0) ||
        (re().is_reverse(r, r1))) {
        result = is_nullable(r1);
    }
    else if (re().is_complement(r, r1)) {
        m_br.mk_not(is_nullable(r1), result);
    }
    else if (re().is_to_re(r, r1)) {        
        result = is_nullable(r1);
    }
    else if (m().is_ite(r, cond, r1, r2)) {
        result = m().mk_ite(cond, is_nullable(r1), is_nullable(r2));
    }
    else if (m_util.is_re(r, seq_sort)) {
        result = is_nullable_symbolic_regex(r, seq_sort);
    }
    else if (str().is_concat(r, r1, r2)) {
        m_br.mk_and(is_nullable(r1), is_nullable(r2), result);
    }
    else if (str().is_empty(r)) {
        result = m().mk_true();
    }
    else if (str().is_unit(r)) {
        result = m().mk_false();
    }
    else if (str().is_string(r, s1)) {
        result = m().mk_bool_val(s1.length() == 0);
    }
    else {
        SASSERT(m_util.is_seq(r));
        result = m().mk_eq(str().mk_empty(r->get_sort()), r);
    }
    return result;
}

expr_ref seq_rewriter::is_nullable_symbolic_regex(expr* r, sort* seq_sort) {
    SASSERT(m_util.is_re(r));
    expr* elem = nullptr, *r1 = r, * r2 = nullptr, * s = nullptr;
    expr_ref elems(str().mk_empty(seq_sort), m());
    expr_ref result(m());
    while (re().is_derivative(r1, elem, r2)) {
        if (str().is_empty(elems))
            elems = str().mk_unit(elem);
        else
            elems = str().mk_concat(str().mk_unit(elem), elems);
        r1 = r2;
    }
    if (re().is_to_re(r1, s)) {
        // r is nullable  
        // iff after taking the derivatives the remaining sequence is empty 
        // iff the inner sequence equals to the sequence of derivative elements in reverse
        result = m().mk_eq(elems, s);
        return result;
    }
    // the default case when either r is not a derivative
    // or when the nested derivatives are not applied to a sequence
    result = re().mk_in_re(str().mk_empty(seq_sort), r);
    return result;
}

/*
    Push reverse inwards (whenever possible).
*/
br_status seq_rewriter::mk_re_reverse(expr* r, expr_ref& result) {
    sort* seq_sort = nullptr;
    VERIFY(m_util.is_re(r, seq_sort));
    expr *r1 = nullptr, *r2 = nullptr, *p = nullptr, *s = nullptr;
    expr *s1 = nullptr, *s2 = nullptr;
    zstring zs;
    unsigned lo = 0, hi = 0;
    if (re().is_concat(r, r1, r2)) {
        result = re().mk_concat(re().mk_reverse(r2), re().mk_reverse(r1));
        return BR_REWRITE2;
    }
    else if (re().is_star(r, r1)) {
        result = re().mk_star((re().mk_reverse(r1)));
        return BR_REWRITE2;
    }
    else if (re().is_plus(r, r1)) {
        result = re().mk_plus((re().mk_reverse(r1)));
        return BR_REWRITE2;
    }
    else if (re().is_union(r, r1, r2)) {
        result = re().mk_union(re().mk_reverse(r1), re().mk_reverse(r2));
        return BR_REWRITE2;
    }
    else if (re().is_intersection(r, r1, r2)) {
        result = re().mk_inter(re().mk_reverse(r1), re().mk_reverse(r2));
        return BR_REWRITE2;
    }
    else if (re().is_diff(r, r1, r2)) {
        result = re().mk_diff(re().mk_reverse(r1), re().mk_reverse(r2));
        return BR_REWRITE2;
    }
    else if (m().is_ite(r, p, r1, r2)) {
        result = m().mk_ite(p, re().mk_reverse(r1), re().mk_reverse(r2));
        return BR_REWRITE2;
    }
    else if (re().is_opt(r, r1)) {
        result = re().mk_opt(re().mk_reverse(r1));
        return BR_REWRITE2;
    }
    else if (re().is_complement(r, r1)) {
        result = re().mk_complement(re().mk_reverse(r1));
        return BR_REWRITE2;
    }
    else if (re().is_loop(r, r1, lo)) {
        result = re().mk_loop(re().mk_reverse(r1), lo);
        return BR_REWRITE2;
    }
    else if (re().is_loop(r, r1, lo, hi)) {
        result = re().mk_loop(re().mk_reverse(r1), lo, hi);
        return BR_REWRITE2;
    }
    else if (re().is_reverse(r, r1)) {
        result = r1;
        return BR_DONE;
    }
    else if (re().is_full_seq(r) ||
             re().is_empty(r) ||
             re().is_range(r) ||
             re().is_full_char(r) ||
             re().is_of_pred(r)) {
        result = r;
        return BR_DONE;
    }
    else if (re().is_to_re(r, s) && str().is_string(s, zs)) {
        result = re().mk_to_re(str().mk_string(zs.reverse()));
        return BR_DONE;
    }
    else if (re().is_to_re(r, s) && str().is_unit(s)) {
        result = r;
        return BR_DONE;
    }
    else if (re().is_to_re(r, s) && str().is_concat(s, s1, s2)) {
        result = re().mk_concat(re().mk_reverse(re().mk_to_re(s2)), 
                                re().mk_reverse(re().mk_to_re(s1)));
        return BR_REWRITE3;
    }
    else {
        // stuck cases: variable, re().is_derivative, ...
        return BR_FAILED;
    }
}

/***************************************************
 *****          Begin Derivative Code          *****
 ***************************************************/

/*
    Symbolic derivative: seq -> regex -> regex
    seq should be single char

    This is the rewriter entrypoint for computing a derivative.
    Use mk_derivative from seq_decl_plugin instead to create a derivative
    expression without computing it (simplifying).

    This calls mk_derivative, the main logic which builds a derivative
    recursively, but mk_derivative doesn't guarantee full simplification.
    Once the derivative is built, we return BR_REWRITE_FULL so that
    any remaining possible simplification is performed from the bottom up.

    Rewriting also replaces _OP_RE_ANTIMOROV_UNION, which is produced
    by is_derivative, with real union.
*/
br_status seq_rewriter::mk_re_derivative(expr* ele, expr* r, expr_ref& result) {
    result = mk_derivative(ele, r);
    // TBD: we may even declare BR_DONE here and potentially miss some simplifications
    return re().is_derivative(result) ? BR_DONE : BR_REWRITE_FULL;
}

/*
    Note: Derivative Normal Form

    When computing derivatives recursively, we preserve the following
    BDD normal form:

    - At the top level, the derivative is a union of Antimorov derivatives
      (Conceptually each element of the union is a different derivative).
      We currently express this derivative using an internal op code:
          _OP_RE_ANTIMOROV_UNION
    - An Antimorov derivative is a nested if-then-else term.
      if-then-elses are pushed outwards and sorted by condition ID
      (cond->get_id()), from largest on the outside to smallest on the
      inside. Duplicate nested conditions are eliminated.
    - The leaves of the if-then-else BDD can have unions themselves,
      but these are interpreted as Regex union, not as separate Antimorov
      derivatives.

    To debug the normal form, call Z3 with -dbg:seq_regex:
    this calls check_deriv_normal_form (below) periodically.

    The main logic is in mk_der_op_rec for combining normal forms
    (some also in mk_der_compl_rec).
*/

#ifdef Z3DEBUG
/*
    Debugging to check the derivative normal form that we assume
    (see definition above).

    This may fail on unusual/unexpected REs, such as those containing
    regex variables, but this is by design as this is only checked
    during debugging, and we have not considered how normal form
    should apply in such cases.
*/
bool seq_rewriter::check_deriv_normal_form(expr* r, int level) {
    if (level == 3) { // top level
        STRACE("seq_verbose", tout
            << "Checking derivative normal form invariant...";);
    }
    expr *r1 = nullptr, *r2 = nullptr, *p = nullptr, *s = nullptr;
    unsigned lo = 0, hi = 0;
    STRACE("seq_verbose", tout << " (level " << level << ")";);
    int new_level = 0;
    if (re().is_antimorov_union(r)) {
        SASSERT(level >= 2);
        new_level = 2;
    }
    else if (m().is_ite(r)) {
        SASSERT(level >= 1);
        new_level = 1;
    }

    SASSERT(!re().is_diff(r));
    SASSERT(!re().is_opt(r));
    SASSERT(!re().is_plus(r));

    if (re().is_antimorov_union(r, r1, r2) ||
        re().is_concat(r, r1, r2) ||
        re().is_union(r, r1, r2) ||
        re().is_intersection(r, r1, r2) ||
        m().is_ite(r, p, r1, r2)) {
        check_deriv_normal_form(r1, new_level);
        check_deriv_normal_form(r2, new_level);
    }
    else if (re().is_star(r, r1) ||
             re().is_complement(r, r1) ||
             re().is_loop(r, r1, lo) ||
             re().is_loop(r, r1, lo, hi)) {
        check_deriv_normal_form(r1, new_level);
    }
    else if (re().is_reverse(r, r1)) {
        SASSERT(re().is_to_re(r1));
    }
    else if (re().is_full_seq(r) ||
             re().is_empty(r) ||
             re().is_range(r) ||
             re().is_full_char(r) ||
             re().is_of_pred(r) ||
             re().is_to_re(r, s)) {
        // OK
    }
    else {
        SASSERT(false);
    }
    if (level == 3) {
        STRACE("seq_verbose", tout << " passed!" << std::endl;);
    }
    return true;
}
#endif

/*
    Memoized, recursive implementation of the symbolic derivative such that
    the result is in normal form.

    Functions without _rec are memoized wrappers, which call the _rec
    version if lookup fails.

    The main logic is in mk_der_op_rec for combining normal forms.
*/
expr_ref seq_rewriter::mk_derivative(expr* ele, expr* r) {
    STRACE("seq_verbose", tout << "derivative: " << mk_pp(ele, m())
                               << "," << mk_pp(r, m()) << std::endl;);
    expr_ref result(m_op_cache.find(OP_RE_DERIVATIVE, ele, r), m());
    if (!result) {
        result = mk_derivative_rec(ele, r);
        m_op_cache.insert(OP_RE_DERIVATIVE, ele, r, result);
    }
    STRACE("seq_verbose", tout << "derivative result: "
                               << mk_pp(result, m()) << std::endl;);
    CASSERT("seq_regex", check_deriv_normal_form(r));
    return result;
}

expr_ref seq_rewriter::mk_der_antimorov_union(expr* r1, expr* r2) {
    return mk_der_op(_OP_RE_ANTIMOROV_UNION, r1, r2);
}

expr_ref seq_rewriter::mk_der_union(expr* r1, expr* r2) {
    return mk_der_op(OP_RE_UNION, r1, r2);
}

expr_ref seq_rewriter::mk_der_inter(expr* r1, expr* r2) {
    return mk_der_op(OP_RE_INTERSECT, r1, r2);
}

expr_ref seq_rewriter::mk_der_concat(expr* r1, expr* r2) {
    return mk_der_op(OP_RE_CONCAT, r1, r2);
}

/*
    Utility functions to decide char <, ==, and <=.
    Return true if deduced, false if unknown.
*/
bool seq_rewriter::lt_char(expr* ch1, expr* ch2) {
    unsigned u1, u2;
    return u().is_const_char(ch1, u1) &&
           u().is_const_char(ch2, u2) && (u1 < u2);
}
bool seq_rewriter::eq_char(expr* ch1, expr* ch2) {
    return ch1 == ch2;
}
bool seq_rewriter::le_char(expr* ch1, expr* ch2) {
    return eq_char(ch1, ch2) || lt_char(ch1, ch2);
}

/*
    Utility function to decide if a simple predicate (ones that appear
    as the conditions in if-then-else expressions in derivatives)
    implies another.

    Return true if we deduce that a implies b, false if unknown.

    Current cases handled:
    - a and b are char <= constraints, or negations of char <= constraints
*/
bool seq_rewriter::pred_implies(expr* a, expr* b) {
    STRACE("seq_verbose", tout << "pred_implies: "
                               << "," << mk_pp(a, m())
                               << "," << mk_pp(b, m()) << std::endl;);
    expr *cha1 = nullptr, *cha2 = nullptr, *nota = nullptr,
         *chb1 = nullptr, *chb2 = nullptr, *notb = nullptr;
    if (m().is_not(a, nota) &&
        m().is_not(b, notb)) {
        return pred_implies(notb, nota);
    }
    else if (u().is_char_le(a, cha1, cha2) &&
             u().is_char_le(b, chb1, chb2)) {
        return le_char(chb1, cha1) && le_char(cha2, chb2);
    }
    else if (u().is_char_le(a, cha1, cha2) &&
             m().is_not(b, notb) &&
             u().is_char_le(notb, chb1, chb2)) {
        return (le_char(chb2, cha1) && lt_char(cha2, chb1)) ||
               (lt_char(chb2, cha1) && le_char(cha2, chb1));
    }
    else if (u().is_char_le(b, chb1, chb2) &&
             m().is_not(a, nota) &&
             u().is_char_le(nota, cha1, cha2)) {
        return le_char(chb1, cha2) && le_char(cha1, chb2);
    }
    return false;
}

/*
    Utility function to decide if two BDDs (nested if-then-else terms)
    have exactly the same structure and conditions.
*/
bool seq_rewriter::ite_bdds_compatabile(expr* a, expr* b) {
    expr* ca = nullptr, *a1 = nullptr, *a2 = nullptr;
    expr* cb = nullptr, *b1 = nullptr, *b2 = nullptr;
    if (m().is_ite(a, ca, a1, a2) && m().is_ite(b, cb, b1, b2)) {
        return (ca == cb) && ite_bdds_compatabile(a1, b1)
                          && ite_bdds_compatabile(a2, b2);
    }
    else if (m().is_ite(a) || m().is_ite(b)) {
        return false;
    }
    else {
        return true;
    }
}

/*
    Apply a binary operation, preserving normal form on derivative expressions.

    Preconditions:
        - k is one of the following binary op codes on REs:
            OP_RE_INTERSECT
            OP_RE_UNION
            OP_RE_CONCAT
            _OP_RE_ANTIMOROV_UNION
        - a and b are in normal form (check_deriv_normal_form)

    Postcondition:
        - result is in normal form (check_deriv_normal_form)
*/
expr_ref seq_rewriter::mk_der_op_rec(decl_kind k, expr* a, expr* b) {
    STRACE("seq_verbose", tout << "mk_der_op_rec: " << k
                               << "," << mk_pp(a, m())
                               << "," << mk_pp(b, m()) << std::endl;);
    expr* ca = nullptr, *a1 = nullptr, *a2 = nullptr;
    expr* cb = nullptr, *b1 = nullptr, *b2 = nullptr;
    expr_ref result(m());

    // Simplify if-then-elses whenever possible
    auto mk_ite = [&](expr* c, expr* a, expr* b) {
        return (a == b) ? a : m().mk_ite(c, a, b);
    };
    // Use character code to order conditions
    auto get_id = [&](expr* e) {
        expr *ch1 = nullptr, *ch2 = nullptr;
        unsigned ch;
        if (u().is_char_le(e, ch1, ch2) && u().is_const_char(ch2, ch))
            return ch;
        // Fallback: use expression ID (but use same ID for negation)
        m().is_not(e, e);
        return e->get_id();
    };

    // Choose when to lift a union to the top level, by converting
    // it to an Antimorov union
    // This implements a restricted form of Antimorov derivatives
    if (k == OP_RE_UNION) {
        if (re().is_antimorov_union(a) || re().is_antimorov_union(b)) {
            k = _OP_RE_ANTIMOROV_UNION;
        }
        #if 0
        // Disabled: eager Antimorov lifting unless BDDs are compatible
        // Note: the check for BDD compatibility could be made more
        // sophisticated: in an Antimorov union of n terms, we really
        // want to check if any pair of them is compatible.
        else if (m().is_ite(a) && m().is_ite(b) &&
                 !ite_bdds_compatabile(a, b)) {
            k = _OP_RE_ANTIMOROV_UNION;
        }
        #endif
    }
    if (k == _OP_RE_ANTIMOROV_UNION) {
        result = re().mk_antimorov_union(a, b);
        return result;
    }
    if (re().is_antimorov_union(a, a1, a2)) {
        expr_ref r1(m()), r2(m());
        r1 = mk_der_op(k, a1, b);
        r2 = mk_der_op(k, a2, b);
        result = re().mk_antimorov_union(r1, r2);
        return result;
    }
    if (re().is_antimorov_union(b, b1, b2)) {
        expr_ref r1(m()), r2(m());
        r1 = mk_der_op(k, a, b1);
        r2 = mk_der_op(k, a, b2);
        result = re().mk_antimorov_union(r1, r2);
        return result;
    }

    // Remaining non-union case: combine two if-then-else BDDs
    // (underneath top-level Antimorov unions)
    if (m().is_ite(a, ca, a1, a2)) {
        expr_ref r1(m()), r2(m());
        expr_ref notca(m().mk_not(ca), m());
        if (m().is_ite(b, cb, b1, b2)) {
            // --- Core logic for combining two BDDs
            expr_ref notcb(m().mk_not(cb), m());
            if (ca == cb) {
                r1 = mk_der_op(k, a1, b1);
                r2 = mk_der_op(k, a2, b2);
                result = mk_ite(ca, r1, r2);
                return result;
            }
            // Order with higher IDs on the outside
            if (get_id(ca) < get_id(cb)) {
                std::swap(a, b);
                std::swap(ca, cb);
                std::swap(notca, notcb);
                std::swap(a1, b1);
                std::swap(a2, b2);
            }
            // Simplify if there is a relationship between ca and cb
            if (pred_implies(ca, cb)) {
                r1 = mk_der_op(k, a1, b1);
            }
            else if (pred_implies(ca, notcb)) {
                r1 = mk_der_op(k, a1, b2);
            }
            if (pred_implies(notca, cb)) {
                r2 = mk_der_op(k, a2, b1);
            }
            else if (pred_implies(notca, notcb)) {
                r2 = mk_der_op(k, a2, b2);
            }
            // --- End core logic
        }
        if (!r1) r1 = mk_der_op(k, a1, b);
        if (!r2) r2 = mk_der_op(k, a2, b);
        result = mk_ite(ca, r1, r2);
        return result;
    }
    if (m().is_ite(b, cb, b1, b2)) {
        expr_ref r1 = mk_der_op(k, a, b1);
        expr_ref r2 = mk_der_op(k, a, b2);
        result = mk_ite(cb, r1, r2);
        return result;
    }
    switch (k) {
    case OP_RE_INTERSECT:
        if (BR_FAILED == mk_re_inter(a, b, result))
            result = re().mk_inter(a, b);
        break;
    case OP_RE_UNION:
        if (BR_FAILED == mk_re_union(a, b, result))
            result = re().mk_union(a, b);
        break;
    case OP_RE_CONCAT:
        if (BR_FAILED == mk_re_concat(a, b, result))
            result = re().mk_concat(a, b);
        break;
    default:
        UNREACHABLE();
        break;
    }

    return result;
}

expr_ref seq_rewriter::mk_der_op(decl_kind k, expr* a, expr* b) {
    expr_ref _a(a, m()), _b(b, m());
    expr_ref result(m());

    // Pre-simplification assumes that none of the
    // transformations hide ite sub-terms, 
    // Rewriting that changes associativity of
    // operators may hide ite sub-terms.

    switch (k) {
    case OP_RE_INTERSECT:
        if (BR_FAILED != mk_re_inter0(a, b, result))
            return result;
        break;
    case OP_RE_UNION:
        if (BR_FAILED != mk_re_union0(a, b, result))
            return result;
        break;
    case OP_RE_CONCAT:
        if (BR_FAILED != mk_re_concat(a, b, result))
            return result;
        break;
    default:
        break;
    }
    result = m_op_cache.find(k, a, b);
    if (!result) {
        result = mk_der_op_rec(k, a, b);
        m_op_cache.insert(k, a, b, result);
    }
    CASSERT("seq_regex", check_deriv_normal_form(result));
    return result;
}

expr_ref seq_rewriter::mk_der_compl(expr* r) {
    STRACE("seq_verbose", tout << "mk_der_compl: " << mk_pp(r, m())
                               << std::endl;);
    expr_ref result(m_op_cache.find(OP_RE_COMPLEMENT, r, nullptr), m());
    if (!result) {
        expr* c = nullptr, * r1 = nullptr, * r2 = nullptr;
        if (re().is_antimorov_union(r, r1, r2)) {
            // Convert union to intersection
            // Result: Antimorov union at top level is lost, pushed inside ITEs
            expr_ref res1(m()), res2(m());
            res1 = mk_der_compl(r1);
            res2 = mk_der_compl(r2);
            result = mk_der_inter(res1, res2);
        }
        else if (m().is_ite(r, c, r1, r2)) {
            result = m().mk_ite(c, mk_der_compl(r1), mk_der_compl(r2));
        }
        else if (BR_FAILED == mk_re_complement(r, result))
            result = re().mk_complement(r);        
        m_op_cache.insert(OP_RE_COMPLEMENT, r, nullptr, result);
    }
    CASSERT("seq_regex", check_deriv_normal_form(result));
    return result;
}

/*
    Make an re_predicate with an arbitrary condition cond, enforcing
    derivative normal form on how conditions are written.

    Tries to rewrite everything to (ele <= x) constraints:
    (ele = a) => ite(ele <= a-1, none, ite(ele <= a, epsilon, none))
    (a = ele) => "
    (a <= ele) => ite(ele <= a-1, none, epsilon)
    (not p)   => mk_der_compl(...)
    (p and q) => mk_der_inter(...)
    (p or q)  => mk_der_union(...)

    Postcondition: result is in BDD form
*/
expr_ref seq_rewriter::mk_der_cond(expr* cond, expr* ele, sort* seq_sort) {
    STRACE("seq_verbose", tout << "mk_der_cond: "
        <<  mk_pp(cond, m()) << ", " << mk_pp(ele, m()) << std::endl;);
    sort *ele_sort = nullptr;
    VERIFY(u().is_seq(seq_sort, ele_sort));
    SASSERT(ele_sort == ele->get_sort());
    expr *c1 = nullptr, *c2 = nullptr, *ch1 = nullptr, *ch2 = nullptr;
    unsigned ch = 0;
    expr_ref result(m()), r1(m()), r2(m());
    if (m().is_eq(cond, ch1, ch2)) {
        r1 = u().mk_le(ch1, ch2);
        r1 = mk_der_cond(r1, ele, seq_sort);
        r2 = u().mk_le(ch2, ch1);
        r2 = mk_der_cond(r2, ele, seq_sort);
        result = mk_der_inter(r1, r2);
    }
    else if (u().is_char_le(cond, ch1, ch2) &&
             u().is_const_char(ch1, ch) && (ch2 == ele)) {
        if (ch > 0) {
            result = u().mk_char(ch - 1);
            result = u().mk_le(ele, result);
            result = re_predicate(result, seq_sort);
            result = mk_der_compl(result);
        }
        else {
            result = m().mk_true();
            result = re_predicate(result, seq_sort);
        }
    }
    else if (m().is_not(cond, c1)) {
        result = mk_der_cond(c1, ele, seq_sort);
        result = mk_der_compl(result);
    }
    else if (m().is_and(cond, c1, c2)) {
        r1 = mk_der_cond(c1, ele, seq_sort);
        r2 = mk_der_cond(c2, ele, seq_sort);
        result = mk_der_inter(r1, r2);
    }
    else if (m().is_or(cond, c1, c2)) {
        r1 = mk_der_cond(c1, ele, seq_sort);
        r2 = mk_der_cond(c2, ele, seq_sort);
        result = mk_der_union(r1, r2);
    }
    else {
        result = re_predicate(cond, seq_sort);
    }
    STRACE("seq_verbose", tout << "mk_der_cond result: "
        <<  mk_pp(result, m()) << std::endl;);
    CASSERT("seq_regex", check_deriv_normal_form(result));
    return result;
}

expr_ref seq_rewriter::mk_derivative_rec(expr* ele, expr* r) {
    expr_ref result(m());
    sort* seq_sort = nullptr, *ele_sort = nullptr;
    VERIFY(m_util.is_re(r, seq_sort));
    VERIFY(m_util.is_seq(seq_sort, ele_sort));
    SASSERT(ele_sort == ele->get_sort());
    expr* r1 = nullptr, *r2 = nullptr, *p = nullptr;
    auto mk_empty = [&]() { return expr_ref(re().mk_empty(r->get_sort()), m()); };
    unsigned lo = 0, hi = 0;
    if (re().is_concat(r, r1, r2)) {
        expr_ref is_n = is_nullable(r1);
        expr_ref dr1 = mk_derivative(ele, r1);
        result = mk_der_concat(dr1, r2);
        if (m().is_false(is_n)) {
            return result;
        }
        expr_ref dr2 = mk_derivative(ele, r2);
        is_n = re_predicate(is_n, seq_sort);
        // Instead of mk_der_union here, we use mk_der_antimorov_union to
        // force the two cases to be considered separately and lifted to
        // the top level. This avoids blowup in cases where determinization
        // is expensive.
        return mk_der_antimorov_union(result, mk_der_concat(is_n, dr2));
    }
    else if (re().is_star(r, r1)) {
        return mk_der_concat(mk_derivative(ele, r1), r);
    }
    else if (re().is_plus(r, r1)) {
        expr_ref star(re().mk_star(r1), m());
        return mk_derivative(ele, star);
    }
    else if (re().is_union(r, r1, r2)) {
        return mk_der_union(mk_derivative(ele, r1), mk_derivative(ele, r2));
    }
    else if (re().is_intersection(r, r1, r2)) {
        return mk_der_inter(mk_derivative(ele, r1), mk_derivative(ele, r2));
    }
    else if (re().is_diff(r, r1, r2)) {
        return mk_der_inter(mk_derivative(ele, r1), mk_der_compl(mk_derivative(ele, r2)));
    }
    else if (m().is_ite(r, p, r1, r2)) {
        // there is no BDD normalization here
        result = m().mk_ite(p, mk_derivative(ele, r1), mk_derivative(ele, r2));
        return result;
    }
    else if (re().is_opt(r, r1)) {
        return mk_derivative(ele, r1);
    }
    else if (re().is_complement(r, r1)) {
        return mk_der_compl(mk_derivative(ele, r1));
    }
    else if (re().is_loop(r, r1, lo)) {
        if (lo > 0) {
            lo--;
        }
        result = re().mk_loop(r1, lo);
        return mk_der_concat(mk_derivative(ele, r1), result);
    }
    else if (re().is_loop(r, r1, lo, hi)) {
        if (hi == 0) {
            return mk_empty();
        }
        hi--;
        if (lo > 0) {
            lo--;
        }
        result = re().mk_loop(r1, lo, hi);
        return mk_der_concat(mk_derivative(ele, r1), result);
    }
    else if (re().is_full_seq(r) ||
             re().is_empty(r)) {
        return expr_ref(r, m());
    }
    else if (re().is_to_re(r, r1)) {
        // r1 is a string here (not a regexp)
        expr_ref hd(m()), tl(m());
        if (get_head_tail(r1, hd, tl)) {
            // head must be equal; if so, derivative is tail
            // Use mk_der_cond to normalize
            STRACE("seq_verbose", tout << "deriv to_re" << std::endl;);
            result = m().mk_eq(ele, hd);
            result = mk_der_cond(result, ele, seq_sort);
            expr_ref r1(re().mk_to_re(tl), m());
            result = mk_der_concat(result, r1);
            return result;
        }
        else if (str().is_empty(r1)) {
            return mk_empty();
        }
#if 0
        else {
            hd = str().mk_nth_i(r1, m_autil.mk_int(0));
            tl = str().mk_substr(r1, m_autil.mk_int(1), m_autil.mk_sub(str().mk_length(r1), m_autil.mk_int(1)));
            result = re().mk_to_re(tl);
            result = 
                m().mk_ite(m_br.mk_eq_rw(r1, str().mk_empty(m().get_sort(r1))), 
                           mk_empty(),
                           re_and(m_br.mk_eq_rw(ele, hd), result));
            return result;
        }
#endif
    }
    else if (re().is_reverse(r, r1) && re().is_to_re(r1, r2)) {
        // Reverses are rewritten so that the only derivative case is
        // derivative of a reverse of a string. (All other cases stuck)
        // This is analagous to the previous is_to_re case.
        expr_ref hd(m()), tl(m());
        if (get_head_tail_reversed(r2, hd, tl)) {
            // Use mk_der_cond to normalize
            STRACE("seq_verbose", tout << "deriv reverse to_re" << std::endl;);
            result = m().mk_eq(ele, tl);
            result = mk_der_cond(result, ele, seq_sort);
            result = mk_der_concat(result, re().mk_reverse(re().mk_to_re(hd)));
            return result;
        }
        else if (str().is_empty(r2)) {
            return mk_empty();
        }
    }
    else if (re().is_range(r, r1, r2)) {
        // r1, r2 are sequences.
        zstring s1, s2;
        if (str().is_string(r1, s1) && str().is_string(r2, s2)) {
            if (s1.length() == 1 && s2.length() == 1) {
                expr_ref ch1(m_util.mk_char(s1[0]), m());
                expr_ref ch2(m_util.mk_char(s2[0]), m());
                // Use mk_der_cond to normalize
                STRACE("seq_verbose", tout << "deriv range zstring" << std::endl;);
                expr_ref p1(u().mk_le(ch1, ele), m());
                p1 = mk_der_cond(p1, ele, seq_sort);
                expr_ref p2(u().mk_le(ele, ch2), m());
                p2 = mk_der_cond(p2, ele, seq_sort);
                result = mk_der_inter(p1, p2);
                return result;
            }
            else {
                return mk_empty();
            }
        }
        expr* e1 = nullptr, *e2 = nullptr;
        if (str().is_unit(r1, e1) && str().is_unit(r2, e2)) {
            // Use mk_der_cond to normalize
            STRACE("seq_verbose", tout << "deriv range str" << std::endl;);
            expr_ref p1(u().mk_le(e1, ele), m());
            p1 = mk_der_cond(p1, ele, seq_sort);
            expr_ref p2(u().mk_le(ele, e2), m());
            p2 = mk_der_cond(p2, ele, seq_sort);
            result = mk_der_inter(p1, p2);
            return result;
        }
    }
    else if (re().is_full_char(r)) {
        return expr_ref(re().mk_to_re(str().mk_empty(seq_sort)), m());
    }
    else if (re().is_of_pred(r, p)) {
        array_util array(m());
        expr* args[2] = { p, ele };
        result = array.mk_select(2, args);
        // Use mk_der_cond to normalize
        STRACE("seq_verbose", tout << "deriv of_pred" << std::endl;);
        return mk_der_cond(result, ele, seq_sort);
    }
    // stuck cases: re.derivative, variable,
    // str.to_re if the head of the string can't be obtained,
    // and re.reverse if not applied to a string or if the tail char
    // of the string can't be obtained
    return expr_ref(re().mk_derivative(ele, r), m());
}

/*************************************************
 *****          End Derivative Code          *****
 *************************************************/


/*
 * pattern match against all ++ "abc" ++ all ++ "def" ++ all regexes.
*/
bool seq_rewriter::is_re_contains_pattern(expr* r, vector<expr_ref_vector>& patterns) {
    expr* r1 = nullptr, *r2 = nullptr, *s = nullptr;
    if (re().is_concat(r, r1, r2) && re().is_full_seq(r1)) {
        r = r2;
        patterns.push_back(expr_ref_vector(m()));
    }
    else {
        return false;
    }
    while (re().is_concat(r, r1, r2)) {
        if (re().is_to_re(r1, s))
            patterns.back().push_back(s);
        else if (re().is_full_seq(r1))
            patterns.push_back(expr_ref_vector(m()));
        else
            return false;
        r = r2;
    }
    return re().is_full_seq(r);
}

/*
 * return true if the sequences p1, p2 cannot overlap in any way.
 * assume |p1| <= |p2|
 *   no suffix of p1 is a prefix of p2
 *   no prefix of p1 is a suffix of p2
 *   p1 is not properly contained in p2
 */
bool seq_rewriter::non_overlap(zstring const& s1, zstring const& s2) const {
    unsigned sz1 = s1.length(), sz2 = s2.length();
    if (sz1 > sz2) 
        return non_overlap(s2, s1);
    auto can_overlap = [&](unsigned start1, unsigned end1, unsigned start2) {
        for (unsigned i = start1; i < end1; ++i) {
            if (s1[i] != s2[start2 + i])
                return false;
        }
        return true;
    };
    for (unsigned i = 1; i < sz1; ++i) 
        if (can_overlap(i, sz1, 0))
            return false;
    for (unsigned j = 0; j + sz1 < sz2; ++j) 
        if (can_overlap(0, sz1, j))
            return false;
    for (unsigned j = sz2 - sz1; j < sz2; ++j) 
        if (can_overlap(0, sz2 - j, j))
            return false;
    return true;
}

bool seq_rewriter::non_overlap(expr_ref_vector const& p1, expr_ref_vector const& p2) const {
    unsigned sz1 = p1.size(), sz2 = p2.size();
    if (sz1 > sz2) 
        return non_overlap(p2, p1);
    if (sz1 == 0 || sz2 == 0)
        return false;
    zstring s1, s2;
    if (sz1 == 1 && sz2 == 1 && str().is_string(p1[0], s1) && str().is_string(p2[0], s2))
        return non_overlap(s1, s2);
    for (expr* e : p1) 
        if (!str().is_unit(e))
            return false;
    for (expr* e : p2) 
        if (!str().is_unit(e))
            return false;
    auto can_overlap = [&](unsigned start1, unsigned end1, unsigned start2) {
        for (unsigned i = start1; i < end1; ++i) {
            if (m().are_distinct(p1[i], p2[start2 + i]))
                return false;
            if (!m().are_equal(p1[i], p2[start2 + i]))
                return true;
        }
        return true;
    };
    for (unsigned i = 1; i < sz1; ++i) 
        if (can_overlap(i, sz1, 0))
            return false;
    for (unsigned j = 0; j + sz1 < sz2; ++j) 
        if (can_overlap(0, sz1, j))
            return false;
    for (unsigned j = sz2 - sz1; j < sz2; ++j) 
        if (can_overlap(0, sz2 - j, j))
            return false;
    return true;
}

/**
  simplify extended contains patterns into simpler membership constraints
       (x ++ "abc" ++ s) in (all ++ "de" ++ all ++ "ee" ++ all ++ "ff" ++ all)
  => 
       ("abc" ++ s) in (all ++ "de" ++ all ++ "ee" ++ all ++ "ff" ++ all)
   or  x in (all ++ "de" ++ all)                & ("abc" ++ s) in (all ++ "ee" ++ all ++ "ff" ++ all)
   or  x in (all ++ "de" ++ all ++ "ee" ++ all) & ("abc" ++ s) in (all ++ "ff" ++ all)
   or  x in (all ++ "de" ++ all ++ "ee" ++ all ++ "ff" ++ all) & .. simplifies to true ..
*/

bool seq_rewriter::rewrite_contains_pattern(expr* a, expr* b, expr_ref& result) {
    vector<expr_ref_vector> patterns;
    expr* x = nullptr, *y = nullptr, *z = nullptr, *u = nullptr;
    if (!str().is_concat(a, x, y))
        return false;
    if (!is_re_contains_pattern(b, patterns)) 
        return false;
    m_lhs.reset();        
    u = y;
    while (str().is_concat(u, z, u) && (str().is_unit(z) || str().is_string(z))) {
        m_lhs.push_back(z);
    }
    for (auto const& p : patterns)
        if (!non_overlap(p, m_lhs))
            return false;

    expr_ref_vector fmls(m());
    sort* rs = b->get_sort();
    expr_ref full(re().mk_full_seq(rs), m()), prefix(m()), suffix(m());
    fmls.push_back(re().mk_in_re(y, b));
    prefix = full;
    for (unsigned i = 0; i < patterns.size(); ++i) {
        for (expr* e : patterns[i])
            prefix = re().mk_concat(prefix, re().mk_to_re(e));
        prefix = re().mk_concat(prefix, full);
        suffix = full;
        for (unsigned j = i + 1; j < patterns.size(); ++j) {
            for (expr* e : patterns[j])
                suffix = re().mk_concat(suffix, re().mk_to_re(e));
            suffix = re().mk_concat(suffix, full);
        }
        fmls.push_back(m().mk_and(re().mk_in_re(x, prefix),
                                  re().mk_in_re(y, suffix)));
    }
    result = mk_or(fmls);
    return true;    
}

/*
    a in empty -> false
    a in full -> true
    a in (str.to_re a') -> (a == a')
    "" in b -> is_nullable(b)
    (ele + tail) in b -> tail in (derivative e b)
    (head + ele) in b -> head in (right-derivative e b)

Other rewrites:
    s in b1 ++ b2, min_len(b1) = max_len(b2) != UINT_MAX -> 
           (seq.len s) >= min_len(b1) & 
           (seq.extract s 0 min_len(b1)) in b1 & 
           (seq.extract s min_len(b1) (- (seq.len s) min_len(b1))) in b2

    similar for tail of regex

Disabled rewrite:
   s + "ab" + t in all ++ "c" ++ all ++ .... ++ "z" ++ all
   => 
   disjunctions that cover cases where s overlaps given that "ab" does
   not overlap with any of the sequences.
   It is disabled because the solver doesn't handle disjunctions of regexes well.

TBD:
Enable rewrite when R = R1|R2 and derivative cannot make progress: 's in R' ==> 's in R1' | 's in R2'
cannot make progress here means that R1 or R2 starts with an uninterpreted symbol
This will help propagate cases like "abc"X in opt(to_re(X)) to equalities.
*/
br_status seq_rewriter::mk_str_in_regexp(expr* a, expr* b, expr_ref& result) {

    STRACE("seq_verbose", tout << "mk_str_in_regexp: " << mk_pp(a, m())
                               << ", " << mk_pp(b, m()) << std::endl;);

    if (re().is_empty(b)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (re().is_full_seq(b)) {
        result = m().mk_true();
        return BR_DONE;
    }
    expr_ref b_s(m());
    if (lift_str_from_to_re(b, b_s)) {
       result = m_br.mk_eq_rw(a, b_s);
       return BR_REWRITE_FULL;
    }
    expr* b1 = nullptr;
    expr* eps = nullptr;
    if (re().is_opt(b, b1) ||
        (re().is_union(b, b1, eps) && re().is_epsilon(eps)) ||
        (re().is_union(b, eps, b1) && re().is_epsilon(eps)))
    {
        result = m().mk_ite(m().mk_eq(str().mk_length(a), m_autil.mk_int(0)),
            m().mk_true(),
            re().mk_in_re(a, b1));
        return BR_REWRITE_FULL;
    }
    if (str().is_empty(a)) {
        result = is_nullable(b);
        if (str().is_in_re(result))
            return BR_DONE;
        else
            return BR_REWRITE_FULL;
    }

    expr_ref hd(m()), tl(m());
    if (get_head_tail(a, hd, tl)) {
        result = re().mk_in_re(tl, re().mk_derivative(hd, b));
        return BR_REWRITE2;
    }

    if (get_head_tail_reversed(a, hd, tl)) {
        result = re().mk_reverse(re().mk_derivative(tl, re().mk_reverse(b)));
        result = re().mk_in_re(hd, result);
        return BR_REWRITE_FULL;
    }

    if (get_re_head_tail(b, hd, tl)) {
        SASSERT(re().min_length(hd) == re().max_length(hd));
        expr_ref len_hd(m_autil.mk_int(re().min_length(hd)), m()); 
        expr_ref len_a(str().mk_length(a), m());
        expr_ref len_tl(m_autil.mk_sub(len_a, len_hd), m());
        result = m().mk_and(m_autil.mk_ge(len_a, len_hd),
                            re().mk_in_re(str().mk_substr(a, m_autil.mk_int(0), len_hd), hd),
                            re().mk_in_re(str().mk_substr(a, len_hd, len_tl), tl));
        return BR_REWRITE_FULL;
    }
    if (get_re_head_tail_reversed(b, hd, tl)) {
        SASSERT(re().min_length(tl) == re().max_length(tl));
        expr_ref len_tl(m_autil.mk_int(re().min_length(tl)), m()); 
        expr_ref len_a(str().mk_length(a), m());
        expr_ref len_hd(m_autil.mk_sub(len_a, len_tl), m());
        result = m().mk_and(m_autil.mk_ge(len_a, len_tl),
                            re().mk_in_re(str().mk_substr(a, m_autil.mk_int(0), len_hd), hd),
                            re().mk_in_re(str().mk_substr(a, len_hd, len_tl), tl));
        return BR_REWRITE_FULL;
    }

#if 0
    unsigned len = 0;
    if (has_fixed_length_constraint(b, len)) {
        expr_ref len_lim(m().mk_eq(m_autil.mk_int(len), str().mk_length(a)), m());
        // this forces derivatives. Perhaps not a good thing for intersections.
        // alternative is to hoist out the smallest length constraining regex
        // and keep the result for the sequence expression that is kept without rewriting
        // or alternative is to block rewriting on this expression in some way.
        expr_ref_vector args(m());
        for (unsigned i = 0; i < len; ++i) {
            args.push_back(str().mk_unit(str().mk_nth_i(a, m_autil.mk_int(i))));
        }
        expr_ref in_re(re().mk_in_re(str().mk_concat(args, a->get_sort()), b), m());
        result = m().mk_and(len_lim, in_re);
        return BR_REWRITE_FULL;
    }
#endif

    // Disabled rewrites
    if (false && re().is_complement(b, b1)) {
        result = m().mk_not(re().mk_in_re(a, b1));
        return BR_REWRITE2;
    }
    if (false && rewrite_contains_pattern(a, b, result))
        return BR_REWRITE_FULL;

    return BR_FAILED;
}

bool seq_rewriter::has_fixed_length_constraint(expr* a, unsigned& len) {
    unsigned minl = re().min_length(a), maxl = re().max_length(a);
    len = minl;
    return minl == maxl;
}

bool seq_rewriter::lift_str_from_to_re_ite(expr* r, expr_ref& result)
{
    expr* cond = nullptr, * then_r = nullptr, * else_r = nullptr;
    expr_ref then_s(m());
    expr_ref else_s(m());
    if (m().is_ite(r, cond, then_r, else_r) &&
        lift_str_from_to_re(then_r, then_s) &&
        lift_str_from_to_re(else_r, else_s)) {
        result = m().mk_ite(cond, then_s, else_s);
        return true;
    }
    return false;
}

bool seq_rewriter::lift_str_from_to_re(expr* r, expr_ref& result)
{
    expr* s = nullptr;
    if (re().is_to_re(r, s)) {
        result = s;
        return true;
    }
    return lift_str_from_to_re_ite(r, result);
}

br_status seq_rewriter::mk_str_to_regexp(expr* a, expr_ref& result) {
    return BR_FAILED;
}

/*
    easy cases:
    .* ++ .* -> .*
    [] ++ r -> []
    r ++ [] -> []
    r ++ "" -> r
    "" ++ r -> r

    to_re and star:
    (str.to_re s1) ++ (str.to_re s2) -> (str.to_re (s1 ++ s2))
    r* ++ r* -> r*
    r* ++ r -> r ++ r*
*/
br_status seq_rewriter::mk_re_concat(expr* a, expr* b, expr_ref& result) {
    if (re().is_full_seq(a) && re().is_full_seq(b)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_empty(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_empty(b)) {
        result = b;
        return BR_DONE;
    }
    if (re().is_epsilon(a)) {
        result = b;
        return BR_DONE;
    }
    if (re().is_epsilon(b)) {
        result = a;
        return BR_DONE;
    }
    expr_ref a_str(m());
    expr_ref b_str(m());
    if (lift_str_from_to_re(a, a_str) && lift_str_from_to_re(b, b_str)) {
        result = re().mk_to_re(str().mk_concat(a_str, b_str));
        return BR_REWRITE2;
    }
    expr* a1 = nullptr, *b1 = nullptr;
    if (re().is_star(a, a1) && re().is_star(b, b1) && a1 == b1) {
        result = a;
        return BR_DONE;
    }
    if (re().is_star(a, a1) && a1 == b) {
        result = re().mk_concat(b, a);
        return BR_DONE;
    }
    unsigned lo1, hi1, lo2, hi2;

    if (re().is_loop(a, a1, lo1, hi1) && lo1 <= hi1 && re().is_loop(b, b1, lo2, hi2) && lo2 <= hi2 && a1 == b1) {
        result = re().mk_loop(a1, lo1 + lo2, hi1 + hi2);
        return BR_DONE;
    }
    if (re().is_loop(a, a1, lo1) && re().is_loop(b, b1, lo2) && a1 == b1) {
        result = re().mk_loop(a1, lo1 + lo2);
        return BR_DONE;
    }
    for (unsigned i = 0; i < 2; ++i) {
        // (loop a lo1) + (loop a lo2 hi2) = (loop a lo1 + lo2) 
        if (re().is_loop(a, a1, lo1) && re().is_loop(b, b1, lo2, hi2) && lo2 <= hi2 && a1 == b1) {
            result = re().mk_loop(a1, lo1 + lo2);
            return BR_DONE;
        }
        // (loop a lo1 hi1) + a* = (loop a lo1)
        if (re().is_loop(a, a1, lo1, hi1) && re().is_star(b, b1) && a1 == b1) {
            result = re().mk_loop(a1, lo1);
            return BR_DONE;
        }
        // (loop a lo1) + a* = (loop a lo1)
        if (re().is_loop(a, a1, lo1) && re().is_star(b, b1) && a1 == b1) {
            result = a;
            return BR_DONE;
        }
        // (loop a lo1 hi1) + a = (loop a lo1+1 hi1+1)
        if (re().is_loop(a, a1, lo1, hi1) && lo1 <= hi1 && a1 == b) {
            result = re().mk_loop(a1, lo1+1, hi1+1);
            return BR_DONE;
        }
        std::swap(a, b);
    }
    return BR_FAILED;
}

bool seq_rewriter::are_complements(expr* r1, expr* r2) const {
    expr* r = nullptr;
    if (re().is_complement(r1, r) && r == r2)
        return true;
    if (re().is_complement(r2, r) && r == r1)
        return true;
    return false;
}

/*
 * basic subset checker.
 */
bool seq_rewriter::is_subset(expr* r1, expr* r2) const {
    // return false;
    expr* ra1 = nullptr, *ra2 = nullptr, *ra3 = nullptr;
    expr* rb1 = nullptr, *rb2 = nullptr, *rb3 = nullptr;
    if (re().is_complement(r1, ra1) && 
        re().is_complement(r2, rb1)) {
        return is_subset(rb1, ra1);
    }
    auto is_concat = [&](expr* r, expr*& a, expr*& b, expr*& c) {
        return re().is_concat(r, a, b) && re().is_concat(b, b, c);
    };
    while (true) {
        if (r1 == r2)
            return true;
        if (re().is_full_seq(r2))
            return true;
        if (is_concat(r1, ra1, ra2, ra3) &&
            is_concat(r2, rb1, rb2, rb3) && ra1 == rb1 && ra2 == rb2) {
            r1 = ra3;
            r2 = rb3;
            continue;
        }
        if (re().is_concat(r1, ra1, ra2) && 
            re().is_concat(r2, rb1, rb2) && re().is_full_seq(rb1)) {
            r1 = ra2;
            continue;
        }
        return false;
    }
}

br_status seq_rewriter::mk_re_union0(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = a;
        return BR_DONE;
    }
    if (re().is_empty(a)) {
        result = b;
        return BR_DONE;
    }
    if (re().is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_full_seq(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_full_seq(b)) {
        result = b;
        return BR_DONE;
    }
    if (re().is_star(a) && re().is_epsilon(b)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_star(b) && re().is_epsilon(a)) {
        result = b;
        return BR_DONE;
    }
    return BR_FAILED;
}

/*
  (a + a) = a
  (a + eps) = a
  (eps + a) = a
*/
br_status seq_rewriter::mk_re_union(expr* a, expr* b, expr_ref& result) {
    br_status st = mk_re_union0(a, b, result);
    if (st != BR_FAILED)
        return st;
    auto mk_full = [&]() { return re().mk_full_seq(a->get_sort()); };
    if (are_complements(a, b)) {
        result = mk_full();
        return BR_DONE;
    }
        
    expr* a1 = nullptr, *a2 = nullptr;
    expr* b1 = nullptr, *b2 = nullptr;
    // ensure union is right-associative
    // and swap-sort entries 
    if (re().is_union(a, a1, a2)) {
        result = re().mk_union(a1, re().mk_union(a2, b));
        return BR_REWRITE2;
    }
        
    auto get_id = [&](expr* e) { re().is_complement(e, e); return e->get_id(); };
    if (re().is_union(b, b1, b2)) {
        if (is_subset(a, b1)) {
            result = b;
            return BR_DONE;
        }
        if (is_subset(b1, a)) {
            result = re().mk_union(a, b2);
            return BR_REWRITE1;
        }
        if (are_complements(a, b1)) {
            result = mk_full();
            return BR_DONE;
        }
        if (get_id(a) > get_id(b1)) {
            result = re().mk_union(b1, re().mk_union(a, b2));
            return BR_REWRITE2;
        }
    }
    else {
        if (is_subset(a, b)) {
            result = b;
            return BR_DONE;
        }
        if (is_subset(b, a)) {
            result = a;
            return BR_DONE;
        }
        if (get_id(a) > get_id(b)) {
            result = re().mk_union(b, a);
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

/*
    comp(intersect e1 e2) -> union comp(e1) comp(e2)
    comp(union e1 e2) -> intersect comp(e1) comp(e2)
    comp(none) -> all
    comp(all) -> none
    comp(comp(e1)) -> e1
*/
br_status seq_rewriter::mk_re_complement(expr* a, expr_ref& result) {
    expr *e1 = nullptr, *e2 = nullptr;
    if (re().is_intersection(a, e1, e2)) {
        result = re().mk_union(re().mk_complement(e1), re().mk_complement(e2));
        return BR_REWRITE2;
    }
    if (re().is_union(a, e1, e2)) {
        result = re().mk_inter(re().mk_complement(e1), re().mk_complement(e2));
        return BR_REWRITE2;
    }
    if (re().is_empty(a)) {
        result = re().mk_full_seq(a->get_sort());
        return BR_DONE;
    }
    if (re().is_full_seq(a)) {
        result = re().mk_empty(a->get_sort());
        return BR_DONE;
    }
    if (re().is_complement(a, e1)) {
        result = e1;
        return BR_DONE;
    }
    return BR_FAILED;
}


br_status seq_rewriter::mk_re_inter0(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = a;
        return BR_DONE;
    }
    if (re().is_empty(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_empty(b)) {
        result = b;
        return BR_DONE;
    }
    if (re().is_full_seq(a)) {
        result = b;
        return BR_DONE;
    }
    if (re().is_full_seq(b)) {
        result = a;
        return BR_DONE;
    }
    return BR_FAILED;
}

/**
    (r n r) = r
    (emp n r) = emp
    (r n emp) = emp
    (all n r) = r
    (r n all) = r
    (r n comp(r)) = emp
    (comp(r) n r) = emp
    (r n to_re(s)) = ite (s in r) to_re(s) emp
    (to_re(s) n r) = "
 */
br_status seq_rewriter::mk_re_inter(expr* a, expr* b, expr_ref& result) {
    br_status st = mk_re_inter0(a, b, result);
    if (st != BR_FAILED)
        return st;
    auto mk_empty = [&]() { return re().mk_empty(a->get_sort()); };
    if (are_complements(a, b)) {
        result = mk_empty();
        return BR_DONE;
    }
    expr* a1 = nullptr, *a2 = nullptr;
    expr* b1 = nullptr, *b2 = nullptr;

    // ensure intersection is right-associative
    // and swap-sort entries 
    if (re().is_intersection(a, a1, a2)) {
        result = re().mk_inter(a1, re().mk_inter(a2, b));
        return BR_REWRITE2;
    }
    auto get_id = [&](expr* e) { re().is_complement(e, e); return e->get_id(); };
    if (re().is_intersection(b, b1, b2)) {
        if (is_subset(b1, a)) {
            result = b;
            return BR_DONE;
        }
        if (is_subset(a, b1)) {
            result = re().mk_inter(a, b2);
            return BR_REWRITE1;
        }
        if (are_complements(a, b1)) {
            result = mk_empty();
            return BR_DONE;
        }
        if (get_id(a) > get_id(b1)) {
            result = re().mk_inter(b1, re().mk_inter(a, b2));
            return BR_REWRITE2;
        }
    }
    else {
        if (get_id(a) > get_id(b)) {
            result = re().mk_inter(b, a);
            return BR_DONE;
        }
        if (is_subset(a, b)) {
            result = a;
            return BR_DONE;
        }
        if (is_subset(b, a)) {
            result = b;
            return BR_DONE;
        }
    }
    if (re().is_to_re(b)) 
        std::swap(a, b);
    expr* s = nullptr;
    if (re().is_to_re(a, s)) {
        result = m().mk_ite(re().mk_in_re(s, b), a, re().mk_empty(a->get_sort()));
        return BR_REWRITE2;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_re_diff(expr* a, expr* b, expr_ref& result) {
    result = re().mk_inter(a, re().mk_complement(b));
    return BR_REWRITE2;
}


br_status seq_rewriter::mk_re_loop(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    rational n1, n2;
    unsigned lo, hi, lo2, hi2, np;
    expr* a = nullptr;
    switch (num_args) {
    case 1: 
        np = f->get_num_parameters();
        lo2 = np > 0 ? f->get_parameter(0).get_int() : 0;
        hi2 = np > 1 ? f->get_parameter(1).get_int() : lo2;
        if  (np == 2 && (lo2 > hi2 || hi2 < 0)) {
            result = re().mk_empty(args[0]->get_sort());
            return BR_DONE;
        }
        if (np == 1 && lo2 < 0) {
            result = re().mk_empty(args[0]->get_sort());
            return BR_DONE;
        }
        // (loop a 0 0) = ""
        if (np == 2 && lo2 == 0 && hi2 == 0) {
            result = re().mk_to_re(str().mk_empty(re().to_seq(args[0]->get_sort())));
            return BR_DONE;
        }
        // (loop (loop a lo) lo2) = (loop lo*lo2)
        if (re().is_loop(args[0], a, lo) && np == 1) {
            result = re().mk_loop(a, lo2 * lo);
            return BR_REWRITE1;
        }
        // (loop (loop a l l) h h) = (loop a l*h l*h)
        if (re().is_loop(args[0], a, lo, hi) && np == 2 && lo == hi && lo2 == hi2) {
            result = re().mk_loop(a, lo2 * lo, hi2 * hi);
            return BR_REWRITE1;
        }
        // (loop a 1 1) = a
        if (np == 2 && lo2 == 1 && hi2 == 1) {
            result = args[0];
            return BR_DONE;
        }
        // (loop a 0) = a*
        if (np == 1 && lo2 == 0) {
            result = re().mk_star(args[0]);
            return BR_DONE;
        }
        break;
    case 2:
        if (m_autil.is_numeral(args[1], n1) && n1.is_unsigned()) {
            result = re().mk_loop(args[0], n1.get_unsigned());
            return BR_REWRITE1;
        }
        if (m_autil.is_numeral(args[1], n1) && n1 < 0) {
            result = re().mk_empty(args[0]->get_sort());
            return BR_DONE;
        }
        break;
    case 3:
        if (m_autil.is_numeral(args[1], n1) && n1.is_unsigned() &&
            m_autil.is_numeral(args[2], n2) && n2.is_unsigned()) {
            result = re().mk_loop(args[0], n1.get_unsigned(), n2.get_unsigned());
            return BR_REWRITE1;
        }
        break;
    default:
        break;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_re_power(func_decl* f, expr* a, expr_ref& result) {
    unsigned p = f->get_parameter(0).get_int();
    result = re().mk_loop(a, p, p);
    return BR_REWRITE1;
}


/*
  a** = a*
  (a* + b)* = (a + b)*
  (a + b*)* = (a + b)*
  (a*b*)*   = (a + b)*
   a+* = a*
   emp* = ""
   all* = all   
*/
br_status seq_rewriter::mk_re_star(expr* a, expr_ref& result) {
    expr* b, *c, *b1, *c1;
    if (re().is_star(a) || re().is_full_seq(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_full_char(a)) {
        result = re().mk_full_seq(a->get_sort());
        return BR_DONE;
    }
    if (re().is_empty(a)) {
        sort* seq_sort = nullptr;
        VERIFY(m_util.is_re(a, seq_sort));
        result = re().mk_to_re(str().mk_empty(seq_sort));
        return BR_DONE;
    }
    if (re().is_to_re(a, b) && str().is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_plus(a, b)) {
        result = re().mk_star(b);
        return BR_DONE;
    }
    if (re().is_union(a, b, c)) {
        if (re().is_star(b, b1)) {
            result = re().mk_star(re().mk_union(b1, c));
            return BR_REWRITE2;
        }
        if (re().is_star(c, c1)) {
            result = re().mk_star(re().mk_union(b, c1));
            return BR_REWRITE2;
        }
        if (re().is_epsilon(b)) {
            result = re().mk_star(c);
            return BR_REWRITE2;
        }
        if (re().is_epsilon(c)) {
            result = re().mk_star(b);
            return BR_REWRITE2;
        }
    }
    if (re().is_concat(a, b, c) &&
        re().is_star(b, b1) && re().is_star(c, c1)) {
        result = re().mk_star(re().mk_union(b1, c1));
        return BR_REWRITE2;
    }
    if (m().is_ite(a, c, b1, c1)) {
        if ((re().is_full_char(b1) || re().is_full_seq(b1)) &&
            (re().is_full_char(c1) || re().is_full_seq(c1))) {
            result = re().mk_full_seq(b1->get_sort());
            return BR_REWRITE2;
        }

    }
    return BR_FAILED;
}

/*
 * (re.range c_1 c_n) 
 */
br_status seq_rewriter::mk_re_range(expr* lo, expr* hi, expr_ref& result) {
    zstring s;
    unsigned len = 0;
    rational rlen;
    bool is_empty = false;
    if (str().is_string(lo, s) && s.length() != 1) 
        is_empty = true;
    if (str().is_string(hi, s) && s.length() != 1) 
        is_empty = true;
    min_length(lo, len);
    if (len > 1)
        is_empty = true;
    min_length(hi, len);
    if (len > 1)
        is_empty = true;
    if (max_length(lo, rlen) && rlen == 0)
        is_empty = true;
    if (max_length(hi, rlen) && rlen == 0)
        is_empty = true;
    if (is_empty) {
        sort* srt = re().mk_re(lo->get_sort());
        result = re().mk_empty(srt);
        return BR_DONE;
    }

    return BR_FAILED;
}

/*
   emp+ = emp
   all+ = all
   a*+ = a*
   a++ = a+
   a+ = aa*
*/
br_status seq_rewriter::mk_re_plus(expr* a, expr_ref& result) {
    if (re().is_empty(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_full_seq(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_epsilon(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_plus(a)) {
        result = a;
        return BR_DONE;
    }
    if (re().is_star(a)) {
        result = a;
        return BR_DONE;
    }

    result = re().mk_concat(a, re().mk_star(a));
    return BR_REWRITE2;
}

br_status seq_rewriter::mk_re_opt(expr* a, expr_ref& result) {
    sort* s = nullptr;
    VERIFY(m_util.is_re(a, s));
    result = re().mk_union(re().mk_to_re(str().mk_empty(s)), a);
    return BR_REWRITE1;
}

void seq_rewriter::intersect(unsigned lo, unsigned hi, svector<std::pair<unsigned, unsigned>>& ranges) {
    unsigned j = 0;
    for (unsigned i = 0; i < ranges.size(); ++i) {
        unsigned lo1 = ranges[i].first;
        unsigned hi1 = ranges[i].second;        
        if (hi < lo1) 
            break;
        if (hi1 >= lo) 
            ranges[j++] = std::make_pair(std::max(lo1, lo), std::min(hi1, hi));
    }
    ranges.shrink(j);
}

/**
 * Simplify cond using special case rewriting for character equations
 * When elem is uninterpreted compute the simplification of Exists elem . cond
 * if it is possible to solve for elem.
 */
void seq_rewriter::elim_condition(expr* elem, expr_ref& cond) {
    expr_ref_vector conds(m());
    flatten_and(cond, conds);
    expr* lhs = nullptr, *rhs = nullptr, *e1 = nullptr; 
    if (u().is_char(elem)) {
        unsigned ch = 0;
        svector<std::pair<unsigned, unsigned>> ranges, ranges1;
        ranges.push_back(std::make_pair(0, u().max_char()));
        auto exclude_char = [&](unsigned ch) {
            if (ch == 0) {
                intersect(1, u().max_char(), ranges);
            }
            else if (ch == u().max_char()) {
                intersect(0, ch-1, ranges);
            }
            else {
                ranges1.reset();
                ranges1.append(ranges);
                intersect(0, ch - 1, ranges);
                intersect(ch + 1, u().max_char(), ranges1);
                ranges.append(ranges1);
            }
        };
        bool all_ranges = true;
        for (expr* e : conds) {
            if (m().is_eq(e, lhs, rhs) && elem == lhs && u().is_const_char(rhs, ch)) {
                intersect(ch, ch, ranges);                
            }
            else if (m().is_eq(e, lhs, rhs) && elem == rhs && u().is_const_char(lhs, ch)) {
                intersect(ch, ch, ranges);
            }
            else if (u().is_char_le(e, lhs, rhs) && elem == lhs && u().is_const_char(rhs, ch)) {
                intersect(0, ch, ranges);
            }
            else if (u().is_char_le(e, lhs, rhs) && elem == rhs && u().is_const_char(lhs, ch)) {
                intersect(ch, u().max_char(), ranges);
            }
            else if (m().is_not(e, e1) && m().is_eq(e1, lhs, rhs) && elem == lhs && u().is_const_char(rhs, ch)) {
                exclude_char(ch);
            }
            else if (m().is_not(e, e1) && m().is_eq(e1, lhs, rhs) && elem == rhs && u().is_const_char(lhs, ch)) {
                exclude_char(ch);
            }
            else if (m().is_not(e, e1) && u().is_char_le(e1, lhs, rhs) && elem == lhs && u().is_const_char(rhs, ch)) {
                // not (e <= ch)
                if (ch == u().max_char()) 
                    ranges.reset();
                else 
                    intersect(ch+1, u().max_char(), ranges);
            }
            else if (m().is_not(e, e1) && u().is_char_le(e1, lhs, rhs) && elem == rhs && u().is_const_char(lhs, ch)) {
                // not (ch <= e)
                if (ch == 0) 
                    ranges.reset();
                else                 
                    intersect(0, ch-1, ranges);
            }
            else {
                all_ranges = false;
                break;
            }
            if (ranges.empty())
                break;
        }
        if (all_ranges) {
            if (ranges.empty()) {
                cond = m().mk_false();
                return;
            }
            if (is_uninterp_const(elem)) {
                cond = m().mk_true();
                return;
            }
        }
    }
            
    expr* solution = nullptr;
    for (expr* e : conds) {
        if (!m().is_eq(e, lhs, rhs)) 
            continue;
        if (rhs == elem)
            std::swap(lhs, rhs);
        if (lhs != elem)
            continue;
        solution = rhs;
        break;        
    }
    if (solution) {
        expr_safe_replace rep(m());
        rep.insert(elem, solution);
        rep(cond);
        if (!is_uninterp_const(elem)) { 
            cond = m().mk_and(m().mk_eq(elem, solution), cond);
        }
    }    
}


br_status seq_rewriter::reduce_re_is_empty(expr* r, expr_ref& result) {
    expr* r1, *r2, *r3, *r4;
    zstring s1, s2;
    unsigned lo, hi;
    auto eq_empty = [&](expr* r) { return m().mk_eq(r, re().mk_empty(r->get_sort())); };
    if (re().is_union(r, r1, r2)) {
        result = m().mk_and(eq_empty(r1), eq_empty(r2));
        return BR_REWRITE2;
    }
    if (re().is_star(r) ||
        re().is_to_re(r) ||
        re().is_full_char(r) ||
        re().is_full_seq(r)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (re().is_concat(r, r1, r2)) {
        result = m().mk_or(eq_empty(r1), eq_empty(r2));
        return BR_REWRITE2;
    }
    else if (re().is_range(r, r1, r2) && 
             str().is_string(r1, s1) && str().is_string(r2, s2) && 
             s1.length() == 1 && s2.length() == 1) {
        result = m().mk_bool_val(s1[0] <= s2[0]);
        return BR_DONE;
    }
    else if ((re().is_loop(r, r1, lo) ||
              re().is_loop(r, r1, lo, hi)) && lo == 0) {
        result = m().mk_false();
        return BR_DONE;
    }
    else if (re().is_loop(r, r1, lo) ||
             (re().is_loop(r, r1, lo, hi) && lo <= hi)) {
        result = eq_empty(r1);
        return BR_REWRITE1;
    }
    // Partial DNF expansion:
    else if (re().is_intersection(r, r1, r2) && re().is_union(r1, r3, r4)) {
        result = eq_empty(re().mk_union(re().mk_inter(r3, r2), re().mk_inter(r4, r2)));
        return BR_REWRITE3;
    }
    else if (re().is_intersection(r, r1, r2) && re().is_union(r2, r3, r4)) {
        result = eq_empty(re().mk_union(re().mk_inter(r3, r1), re().mk_inter(r4, r1)));
        return BR_REWRITE3;
    }
    return BR_FAILED;
}

br_status seq_rewriter::reduce_re_eq(expr* l, expr* r, expr_ref& result) {
    if (re().is_empty(l)) {
        std::swap(l, r);
    }
    if (re().is_empty(r)) {
        return reduce_re_is_empty(l, result);
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_le_core(expr * l, expr * r, expr_ref & result) {

    return BR_FAILED;

    // k <= len(x) -> true  if k <= 0
    rational n;
    if (str().is_length(r) && m_autil.is_numeral(l, n) && n <= 0) {
        result = m().mk_true();
        return BR_DONE;
    } 
    // len(x) <= 0 -> x = ""
    // len(x) <= k -> false if k < 0
    expr* e = nullptr;
    if (str().is_length(l, e) && m_autil.is_numeral(r, n)) {
        if (n == 0)
            result = str().mk_is_empty(e);
        else if (n < 0)
            result = m().mk_false();
        else
            return BR_FAILED;
        return BR_REWRITE1;
    } 
    return BR_FAILED;
}

br_status seq_rewriter::mk_eq_core(expr * l, expr * r, expr_ref & result) {
    expr_ref_vector res(m());
    expr_ref_pair_vector new_eqs(m());
    if (m_util.is_re(l)) {
        return reduce_re_eq(l, r, result);
    }
    bool changed = false;
    if (reduce_eq_empty(l, r, result)) 
        return BR_REWRITE_FULL;

    if (!reduce_eq(l, r, new_eqs, changed)) {
        result = m().mk_false();
        TRACE("seq_verbose", tout << result << "\n";);
        return BR_DONE;
    }
    if (!changed) {
        return BR_FAILED;
    }
    for (auto const& p : new_eqs) {
        res.push_back(m().mk_eq(p.first, p.second));
    }
    result = mk_and(res);
    TRACE("seq_verbose", tout << result << "\n";);
    return BR_REWRITE3;
}

void seq_rewriter::remove_empty_and_concats(expr_ref_vector& es) {
    unsigned j = 0;
    bool has_concat = false;
    for (expr* e : es) {
        has_concat |= str().is_concat(e);
        if (!str().is_empty(e))
            es[j++] = e;
    }
    es.shrink(j);
    if (has_concat) {
        expr_ref_vector fs(m());
        for (expr* e : es) 
            str().get_concat(e, fs);
        es.swap(fs);
    }
}

void seq_rewriter::remove_leading(unsigned n, expr_ref_vector& es) {
    SASSERT(n <= es.size());
    if (n == 0)
        return;
    for (unsigned i = n; i < es.size(); ++i) {
        es[i-n] = es.get(i);
    }
    es.shrink(es.size() - n);
}

bool seq_rewriter::reduce_back(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs) {    
    expr* a, *b;    
    zstring s, s1, s2;
    while (true) {
        if (ls.empty() || rs.empty()) {
            break;
        }
        expr* l = ls.back();
        expr* r = rs.back();            
        if (str().is_unit(r) && str().is_string(l)) {
            std::swap(l, r);
            ls.swap(rs);
        }
        if (l == r) {
            ls.pop_back();
            rs.pop_back();
        }
        else if(str().is_unit(l, a) &&
                str().is_unit(r, b)) {
            if (m().are_distinct(a, b)) {
                return false;
            }
            new_eqs.push_back(a, b);
            ls.pop_back();
            rs.pop_back();
        }
        else if (str().is_unit(l, a) && str().is_string(r, s)) {
            SASSERT(s.length() > 0);
            
            app_ref ch(str().mk_char(s, s.length()-1), m());
            SASSERT(ch->get_sort() == a->get_sort());
            new_eqs.push_back(ch, a);
            ls.pop_back();
            if (s.length() == 1) {
                rs.pop_back();
            }
            else {
                expr_ref s2(str().mk_string(s.extract(0, s.length()-1)), m());
                rs[rs.size()-1] = s2;
            }
        }
        else if (str().is_string(l, s1) && str().is_string(r, s2)) {
            unsigned min_l = std::min(s1.length(), s2.length());
            for (unsigned i = 0; i < min_l; ++i) {
                if (s1[s1.length()-i-1] != s2[s2.length()-i-1]) {
                    return false;
                }
            }
            ls.pop_back();          
            rs.pop_back();
            if (min_l < s1.length()) {
                ls.push_back(str().mk_string(s1.extract(0, s1.length()-min_l)));
            }
            if (min_l < s2.length()) {
                rs.push_back(str().mk_string(s2.extract(0, s2.length()-min_l)));
            }        
        }
        else {
            break;
        }
    }
    return true;
}

bool seq_rewriter::reduce_front(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs) {    
    expr* a, *b;    
    zstring s, s1, s2;
    unsigned head1 = 0, head2 = 0;
    while (true) {
        if (head1 == ls.size() || head2 == rs.size()) {
            break;
        }
        SASSERT(head1 < ls.size() && head2 < rs.size());

        expr* l = ls.get(head1);
        expr* r = rs.get(head2);
        if (str().is_unit(r) && str().is_string(l)) {
            std::swap(l, r);
            ls.swap(rs);
            std::swap(head1, head2);
        }
        if (l == r) {
            ++head1;
            ++head2;
        }
        else if(str().is_unit(l, a) &&
                str().is_unit(r, b)) {
            if (m().are_distinct(a, b)) {
                return false;
            }
            new_eqs.push_back(a, b);
            ++head1;
            ++head2;
        }
        else if (str().is_unit(l, a) && str().is_string(r, s)) {
            SASSERT(s.length() > 0);
            app* ch = str().mk_char(s, 0);
            SASSERT(ch->get_sort() == a->get_sort());
            new_eqs.push_back(ch, a);
            ++head1;
            if (s.length() == 1) {
                ++head2;
            }
            else {
                expr_ref s2(str().mk_string(s.extract(1, s.length()-1)), m());
                rs[head2] = s2;
            }            
        }
        else if (str().is_string(l, s1) &&
                 str().is_string(r, s2)) {
            TRACE("seq", tout << s1 << " - " << s2 << " " << s1.length() << " " << s2.length() << "\n";);
            unsigned min_l = std::min(s1.length(), s2.length());
            for (unsigned i = 0; i < min_l; ++i) {
                if (s1[i] != s2[i]) {
                    TRACE("seq", tout << "different at position " << i << " " << s1[i] << " " << s2[i] << "\n";);
                    return false;
                }
            }
            if (min_l == s1.length()) {
                ++head1;            
            }
            else {
                ls[head1] = str().mk_string(s1.extract(min_l, s1.length()-min_l));
            }
            if (min_l == s2.length()) {
                ++head2;            
            }
            else {
                rs[head2] = str().mk_string(s2.extract(min_l, s2.length()-min_l));
            }
        }
        else {
            break;
        }
    }
    remove_leading(head1, ls);
    remove_leading(head2, rs);
    return true;
}

/**
   \brief simplify equality ls = rs
   - New equalities are inserted into eqs.
   - Last remaining equalities that cannot be simplified further are kept in ls, rs
   - returns false if equality is unsatisfiable   
   - sets change to true if some simplification occurred
*/
bool seq_rewriter::reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs, bool& change) {
    TRACE("seq_verbose", tout << ls << "\n"; tout << rs << "\n";);
    unsigned hash_l = ls.hash();
    unsigned hash_r = rs.hash();
    unsigned sz_eqs = eqs.size();
    remove_empty_and_concats(ls);
    remove_empty_and_concats(rs);
    return 
        reduce_back(ls, rs, eqs) && 
        reduce_front(ls, rs, eqs) &&
        reduce_itos(ls, rs, eqs) &&
        reduce_itos(rs, ls, eqs) &&
        reduce_by_length(ls, rs, eqs) &&
        reduce_subsequence(ls, rs, eqs) &&
        reduce_non_overlap(ls, rs, eqs) && 
        reduce_non_overlap(rs, ls, eqs) && 
        (change = (hash_l != ls.hash() || hash_r != rs.hash() || eqs.size() != sz_eqs), 
         true);
}

bool seq_rewriter::reduce_eq(expr* l, expr* r, expr_ref_pair_vector& new_eqs, bool& changed) {
    m_lhs.reset();
    m_rhs.reset();
    str().get_concat(l, m_lhs);
    str().get_concat(r, m_rhs);
    bool change = false;
    if (reduce_eq(m_lhs, m_rhs, new_eqs, change)) {
        if (!change) {
            new_eqs.push_back(l, r);
        }
        else {
            add_seqs(m_lhs, m_rhs, new_eqs);
        }
        changed |= change;
        return true;
    }
    else {
        TRACE("seq", tout << mk_bounded_pp(l, m()) << " != " << mk_bounded_pp(r, m()) << "\n";);
        return false;
    }
}

void seq_rewriter::add_seqs(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref_pair_vector& eqs) {
    if (!ls.empty() || !rs.empty()) {
        sort * s = (ls.empty() ? rs[0] : ls[0])->get_sort();
        eqs.push_back(str().mk_concat(ls, s), str().mk_concat(rs, s));
    }
}


bool seq_rewriter::reduce_contains(expr* a, expr* b, expr_ref_vector& disj) {
    m_lhs.reset();
    str().get_concat(a, m_lhs);
    TRACE("seq", tout << expr_ref(a, m()) << " " << expr_ref(b, m()) << "\n";);
    sort* sort_a = a->get_sort();
    zstring s;
    for (unsigned i = 0; i < m_lhs.size(); ++i) {
        expr* e = m_lhs.get(i);
        if (str().is_empty(e)) {
            continue;
        }

        if (str().is_string(e, s)) {
            unsigned sz = s.length();
            expr_ref_vector es(m());
            for (unsigned j = 0; j < sz; ++j) {
                es.push_back(str().mk_unit(str().mk_char(s, j)));
            }
            es.append(m_lhs.size() - i, m_lhs.data() + i);
            for (unsigned j = 0; j < sz; ++j) {
                disj.push_back(str().mk_prefix(b, str().mk_concat(es.size() - j, es.data() + j, sort_a)));
            }
            continue;
        }
        if (str().is_unit(e)) {
            disj.push_back(str().mk_prefix(b, str().mk_concat(m_lhs.size() - i, m_lhs.data() + i, sort_a)));
            continue;
        }

        if (str().is_string(b, s)) {
            expr* all = re().mk_full_seq(re().mk_re(b->get_sort()));
            disj.push_back(re().mk_in_re(str().mk_concat(m_lhs.size() - i, m_lhs.data() + i, sort_a),
                                              re().mk_concat(all, re().mk_concat(re().mk_to_re(b), all))));
            return true;
        }

        if (i == 0) {
            return false;
        }
        disj.push_back(str().mk_contains(str().mk_concat(m_lhs.size() - i, m_lhs.data() + i, sort_a), b));
        return true;
    }
    disj.push_back(str().mk_is_empty(b));
    return true;
}


expr* seq_rewriter::concat_non_empty(expr_ref_vector& es) {
    sort* s = es[0]->get_sort();
    unsigned j = 0;
    for (expr* e : es) {
        if (str().is_unit(e) || str().is_string(e))
            es[j++] = e;
    }
    es.shrink(j);
    return str().mk_concat(es, s);
}

/**
  \brief assign the non-unit and non-string elements to the empty sequence.
  If all is true, then return false if there is a unit or non-empty substring.
*/

bool seq_rewriter::set_empty(unsigned sz, expr* const* es, bool all, expr_ref_pair_vector& eqs) {
    zstring s;
    expr* emp = nullptr;
    for (unsigned i = 0; i < sz; ++i) {
        if (str().is_unit(es[i])) {
            if (all) return false;
        }
        else if (str().is_empty(es[i])) {
            continue;
        }
        else if (str().is_string(es[i], s)) {
            if (s.length() == 0)
                continue;
            if (all) {
                return false;
            }
        }
        else {
            emp = emp?emp:str().mk_empty(es[i]->get_sort());
            eqs.push_back(emp, es[i]);
        }
    }
    return true;
}

lbool seq_rewriter::eq_length(expr* x, expr* y) {
    unsigned xl = 0, yl = 0;
    if (min_length(x, xl) && min_length(y, yl))
        return xl == yl ? l_true : l_false;
    return l_undef;
}

/***
    \brief extract the minimal length of the sequence.
    Return true if the minimal length is equal to the 
    maximal length (the sequence is bounded).
*/

bool seq_rewriter::min_length(expr* e, unsigned& len) {
    zstring s;
    len = 0;
    if (str().is_unit(e)) {
        len = 1;
        return true;
    }
    else if (str().is_empty(e)) {
        len = 0;
        return true;
    }
    else if (str().is_string(e, s)) {
        len = s.length();
        return true;
    }
    else if (str().is_concat(e)) {
        unsigned min_l = 0;
        bool bounded = true;
        for (expr* arg : *to_app(e)) {
            if (!min_length(arg, min_l))
                bounded = false;
            len += min_l;
        }
        return bounded;
    }
    return false;
}

bool seq_rewriter::min_length(expr_ref_vector const& es, unsigned& len) {
    unsigned min_l = 0;
    bool bounded = true;
    len = 0;
    for (expr* arg : es) {
        if (!min_length(arg, min_l))
            bounded = false;
        len += min_l;
    }
    return bounded;
}

bool seq_rewriter::max_length(expr* e, rational& len) {
    if (str().is_unit(e)) {
        len = 1;
        return true;
    }
    if (str().is_at(e)) {
        len = 1;
        return true;
    }
    zstring s;
    if (str().is_string(e, s)) {
        len = rational(s.length());
        return true;
    }
    if (str().is_empty(e)) {
        len = 0;
        return true;
    }
    expr* s1 = nullptr, *i = nullptr, *l = nullptr;
    rational n;
    if (str().is_extract(e, s1, i, l) && m_autil.is_numeral(l, n) && !n.is_neg()) {
        len = n;
        return true;
    }
    if (str().is_concat(e)) {
        rational l(0);
        len = 0;
        for (expr* arg : *to_app(e)) {
            if (!max_length(arg, l))
                return false;
            len += l;
        }
        return true;
    }
    return false;
}

bool seq_rewriter::is_string(unsigned n, expr* const* es, zstring& s) const {
    zstring s1;
    expr* e;
    unsigned ch;
    for (unsigned i = 0; i < n; ++i) {
        if (str().is_string(es[i], s1)) {
            s = s + s1;
        }
        else if (str().is_unit(es[i], e) && m_util.is_const_char(e, ch)) {
            s = s + zstring(ch);
        }
        else {
            return false;
        }
    }
    return true;
}

expr_ref seq_rewriter::mk_length(expr* s) {
    expr_ref result(m());
    if (BR_FAILED == mk_seq_length(s, result))
        result = str().mk_length(s);
    return result;
}


/**
 * itos(n) = <numeric string> -> n = numeric
 */

bool seq_rewriter::reduce_itos(expr_ref_vector& ls, expr_ref_vector& rs,
                              expr_ref_pair_vector& eqs) {
    expr* n = nullptr;
    zstring s;
    if (ls.size() == 1 && 
        str().is_itos(ls.get(0), n) &&
        is_string(rs.size(), rs.data(), s)) {
        std::string s1 = s.encode();
        try {
            rational r(s1.c_str());
            if (s1 == r.to_string()) {
                eqs.push_back(n, m_autil.mk_numeral(r, true));
                ls.reset();
                rs.reset();
                return true;
            }
        }
        catch (...)
        { }
    }
    return true;
}

bool seq_rewriter::reduce_eq_empty(expr* l, expr* r, expr_ref& result) {
    if (str().is_empty(r))
        std::swap(l, r);
    if (str().is_length(r))
        std::swap(l, r);
#if 0
    rational n;
    if (str().is_length(l) && m_autil.is_numeral(r, n) && n.is_zero()) {
        VERIFY(str().is_length(l, l));
        result = m().mk_eq(l, str().mk_empty(l->get_sort()));
        return true;
    }
#endif
    if (!str().is_empty(l))
        return false;
    expr* s = nullptr, *offset = nullptr, *len = nullptr;
    if (str().is_extract(r, s, offset, len)) {
        expr_ref len_s(str().mk_length(s), m()); 
        expr_ref_vector fmls(m());
        fmls.push_back(m_autil.mk_lt(offset, m_autil.mk_int(0)));
        fmls.push_back(m().mk_eq(s, l));
        fmls.push_back(m_autil.mk_le(len, m_autil.mk_int(0)));
        fmls.push_back(m_autil.mk_le(len_s, offset));
        result = m().mk_or(fmls);
        return true;
    }
    return false;
}

bool seq_rewriter::reduce_by_length(expr_ref_vector& ls, expr_ref_vector& rs,
                                    expr_ref_pair_vector& eqs) {

    if (ls.empty() && rs.empty())
        return true;

    unsigned len1 = 0, len2 = 0;
    bool bounded1 = min_length(ls, len1);
    bool bounded2 = min_length(rs, len2);
    if (bounded1 && len1 < len2) 
        return false;
    if (bounded2 && len2 < len1) 
        return false;
    if (bounded1 && len1 == len2 && len1 > 0) {
        if (!set_empty(rs.size(), rs.data(), false, eqs))
            return false;
        eqs.push_back(concat_non_empty(ls), concat_non_empty(rs));
        ls.reset(); 
        rs.reset();
    }
    else if (bounded2 && len1 == len2 && len1 > 0) {
        if (!set_empty(ls.size(), ls.data(), false, eqs))
            return false;
        eqs.push_back(concat_non_empty(ls), concat_non_empty(rs));
        ls.reset(); 
        rs.reset();
    }    
    return true;
}

/**
   reduce for the case where rs = a constant string, 
   ls contains a substring that matches no substring of rs.
 */
bool seq_rewriter::reduce_non_overlap(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs) {
    for (expr* u : rs)
        if (!str().is_unit(u))
            return true;
    expr_ref_vector pattern(m());
    for (expr* x : ls) {
        if (str().is_unit(x))
            pattern.push_back(x);
        else if (!pattern.empty()) {
            if (non_overlap(pattern, rs))
                return false;
            pattern.reset();
        }
    }
    if (!pattern.empty() && non_overlap(pattern, rs))
        return false;
    return true;
}

bool seq_rewriter::reduce_subsequence(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs) {

    if (ls.size() > rs.size()) 
        ls.swap(rs);

    if (ls.size() == rs.size())
        return true;

    if (ls.empty() && rs.size() == 1)
        return true;
    
    uint_set rpos;
    for (expr* x : ls) {
        unsigned j = 0;
        bool is_unit = str().is_unit(x);
        for (expr* y : rs) {
            if (!rpos.contains(j) && (x == y || (is_unit && str().is_unit(y)))) {
                rpos.insert(j);
                break;
            }
            ++j;
        }
        if (j == rs.size())
            return true;
    }
    // if we reach here, then every element of l is contained in r in some position.
    // or each non-unit in l is matched by a non-unit in r, and otherwise, the non-units match up.
    unsigned i = 0, j = 0;
    for (expr* y : rs) {
        if (rpos.contains(i)) {
            rs[j++] = y;
        }
        else if (!set_empty(1, &y, true, eqs)) {
            return false;
        }
        ++i;
    }
    if (j == rs.size()) {
        return true;
    }
    rs.shrink(j);
    SASSERT(ls.size() == rs.size());
    if (!ls.empty()) {
        sort* srt = ls[0]->get_sort();
        eqs.push_back(str().mk_concat(ls, srt),
                      str().mk_concat(rs, srt));
        ls.reset();
        rs.reset();
        TRACE("seq", tout << "subsequence " << eqs << "\n";);
    }
    return true;
} 

seq_rewriter::op_cache::op_cache(ast_manager& m):
    m_trail(m)
{}

expr* seq_rewriter::op_cache::find(decl_kind op, expr* a, expr* b) {
    op_entry e(op, a, b, nullptr);
    m_table.find(e, e);

    return e.r;
}

void seq_rewriter::op_cache::insert(decl_kind op, expr* a, expr* b, expr* r) {
    cleanup();
    if (a) m_trail.push_back(a);
    if (b) m_trail.push_back(b);
    if (r) m_trail.push_back(r);
    m_table.insert(op_entry(op, a, b, r));
}

void seq_rewriter::op_cache::cleanup() {
    if (m_table.size() >= m_max_cache_size) {
        m_trail.reset();
        m_table.reset();
        STRACE("seq_regex", tout << "Op cache reset!" << std::endl;);
        STRACE("seq_regex_brief", tout << "(OP CACHE RESET) ";);
        STRACE("seq_verbose", tout << "Derivative op cache reset" << std::endl;);
    }
}
