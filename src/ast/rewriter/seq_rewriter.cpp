/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_rewriter.cpp

Abstract:

    Basic rewriting rules for sequences constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5
    Murphy Berzish 2017-02-21

Notes:

--*/

#include "ast/rewriter/seq_rewriter.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "util/uint_set.h"
#include "math/automata/automaton.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/bool_rewriter.h"
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
        SASSERT(m.get_sort(e) == m.get_sort(m_t));
        SASSERT(m.get_sort(e) == m_sort);
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
        bool_rewriter br(m);
        expr_ref fml(m);
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
        if (!m_var || m.get_sort(m_var) != x->get_sort()) {
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

re2automaton::~re2automaton() {}

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
        TRACE("seq", display_expr1 disp(m); r->display(tout, disp););
    }
    return r;
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
        if (u.str.is_string(e1, s1) && u.str.is_string(e2, s2) &&
            s1.length() == 1 && s2.length() == 1) {
            unsigned start = s1[0];
            unsigned stop = s2[0];
            expr_ref _start(u.mk_char(start), m);
            expr_ref _stop(u.mk_char(stop), m);
            TRACE("seq", tout << "Range: " << start << " " << stop << "\n";);
            a = alloc(eautomaton, sm, sym_expr::mk_range(_start, _stop));
            return a.detach();
        }
        else {
            TRACE("seq", tout << "Range expression is not handled: " << mk_pp(e, m) << "\n";);
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
        VERIFY (u.is_re(m.get_sort(e), seq_s));
        VERIFY (u.is_seq(seq_s, char_s));
        sym_expr* _true = sym_expr::mk_pred(tt, char_s);
        return eautomaton::mk_loop(sm, _true);
    }
    else if (u.re.is_full_char(e)) {
        expr_ref tt(m.mk_true(), m);
        sort *seq_s = nullptr, *char_s = nullptr;
        VERIFY (u.is_re(m.get_sort(e), seq_s));
        VERIFY (u.is_seq(seq_s, char_s));
        sym_expr* _true = sym_expr::mk_pred(tt, char_s);
        a = alloc(eautomaton, sm, _true);
        return a.detach();
    }
    else if (u.re.is_intersection(e, e1, e2) && m_sa && (a = re2aut(e1)) && (b = re2aut(e2))) {
        return m_sa->mk_product(*a, *b);
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
    case OP_RE_INTERSECT:
        SASSERT(num_args == 2);
        st = mk_re_inter(args[0], args[1], result);
        break;
    case OP_RE_COMPLEMENT:
        SASSERT(num_args == 1);
        st = mk_re_complement(args[0], result);
        break;
    case OP_RE_LOOP:
        st = mk_re_loop(num_args, args, result);
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
#if 0
    case OP_SEQ_NTH:
        SASSERT(num_args == 2);
        return mk_seq_nth(args[0], args[1], result); 
#endif
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
            expr_ref arg3(m_autil.mk_int(0), m());
            result = m_util.str.mk_index(args[0], args[1], arg3);
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
    case OP_SEQ_TO_RE:
        SASSERT(num_args == 1);
        st = mk_str_to_regexp(args[0], result);
        break;
    case OP_SEQ_IN_RE:
        SASSERT(num_args == 2);
        st = mk_str_in_regexp(args[0], args[1], result);
        break;
    case OP_STRING_CONST:
        return BR_FAILED;
    case OP_STRING_ITOS: 
        SASSERT(num_args == 1);
        st = mk_str_itos(args[0], result);
        break;
    case OP_STRING_STOI: 
        SASSERT(num_args == 1);
        st = mk_str_stoi(args[0], result);
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
    CTRACE("seq", st != BR_FAILED, tout << result << "\n";);
    return st;
}

/*
 * (seq.unit (_ BitVector 8)) ==> String constant
 */
br_status seq_rewriter::mk_seq_unit(expr* e, expr_ref& result) {
    unsigned ch;
    // specifically we want (_ BitVector 8)
    if (m_util.is_const_char(e, ch)) {
        // convert to string constant
        zstring str(ch);
        TRACE("seq_verbose", tout << "rewrite seq.unit of 8-bit value " << ch << " to string constant \"" << str<< "\"" << std::endl;);
        result = m_util.str.mk_string(str);
        return BR_DONE;
    }

    return BR_FAILED;
}

/*
   string + string = string
   a + (b + c) = (a + b) + c
   a + "" = a
   "" + a = a
   (a + string) + string = a + string
*/
br_status seq_rewriter::mk_seq_concat(expr* a, expr* b, expr_ref& result) {
    zstring s1, s2;
    expr* c, *d;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        result = m_util.str.mk_string(s1 + s2);
        return BR_DONE;
    }
    if (m_util.str.is_concat(a, c, d)) {
        result = m_util.str.mk_concat(c, m_util.str.mk_concat(d, b));
        return BR_REWRITE2;
    }
    if (m_util.str.is_empty(a)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    // TBD concatenation is right-associative
    if (isc2 && m_util.str.is_concat(a, c, d) && m_util.str.is_string(d, s1)) {
        result = m_util.str.mk_concat(c, m_util.str.mk_string(s1 + s2));
        return BR_DONE;
    }
    if (isc1 && m_util.str.is_concat(b, c, d) && m_util.str.is_string(c, s2)) {
        result = m_util.str.mk_concat(m_util.str.mk_string(s1 + s2), d);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_length(expr* a, expr_ref& result) {
    zstring b;
    m_es.reset();
    m_util.str.get_concat(a, m_es);
    unsigned len = 0;
    unsigned j = 0;
    for (unsigned i = 0; i < m_es.size(); ++i) {
        if (m_util.str.is_string(m_es[i].get(), b)) {
            len += b.length();
        }
        else if (m_util.str.is_unit(m_es[i].get())) {
            len += 1;
        }
        else if (m_util.str.is_empty(m_es[i].get())) {
            // skip
        }
        else {
            m_es[j] = m_es[i].get();
            ++j;
        }
    }
    if (j == 0) {
        result = m_autil.mk_numeral(rational(len, rational::ui64()), true);
        return BR_DONE;
    }
    if (j != m_es.size() || j != 1) {
        expr_ref_vector es(m());        
        for (unsigned i = 0; i < j; ++i) {
            es.push_back(m_util.str.mk_length(m_es[i].get()));
        }
        if (len != 0) {
            es.push_back(m_autil.mk_numeral(rational(len, rational::ui64()), true));
        }
        result = m_autil.mk_add(es.size(), es.c_ptr());
        return BR_REWRITE2;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_extract(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s;
    rational pos, len;

    TRACE("seq", tout << mk_pp(a, m()) << " " << mk_pp(b, m()) << " " << mk_pp(c, m()) << "\n";);
    bool constantBase = m_util.str.is_string(a, s);
    bool constantPos = m_autil.is_numeral(b, pos);
    bool constantLen = m_autil.is_numeral(c, len);

    
    // case 1: pos<0 or len<=0
    // rewrite to ""
    if ( (constantPos && pos.is_neg()) || (constantLen && !len.is_pos()) ) {
        result = m_util.str.mk_empty(m().get_sort(a));
        return BR_DONE;
    }
    // case 1.1: pos >= length(base)
    // rewrite to ""
    if (constantPos && constantBase && pos >= rational(s.length())) {
        result = m_util.str.mk_empty(m().get_sort(a));
        return BR_DONE;
    }

    constantPos &= pos.is_unsigned();
    constantLen &= len.is_unsigned();

    if (constantPos && constantLen && constantBase) {
        unsigned _pos = pos.get_unsigned();
        unsigned _len = len.get_unsigned();
        if (_pos + _len >= s.length()) {
            // case 2: pos+len goes past the end of the string
            unsigned _len = s.length() - _pos + 1;
            result = m_util.str.mk_string(s.extract(_pos, _len));
        } else {
            // case 3: pos+len still within string
            result = m_util.str.mk_string(s.extract(_pos, _len));
        }
        return BR_DONE;
    }


    expr_ref_vector as(m()), bs(m());
    m_util.str.get_concat_units(a, as);
    if (as.empty()) {
        result = m_util.str.mk_empty(m().get_sort(a));
        return BR_DONE;
    }

    if (!constantPos) {
        return BR_FAILED;
    }
    unsigned _pos = pos.get_unsigned();

    // (extract s 0 (len s)) = s 
    expr* a2 = nullptr;
    if (_pos == 0 && m_util.str.is_length(c, a2) && a == a2) {
        result = a;
        return BR_DONE;
    }

    unsigned offset = 0;
    for (; offset < as.size() && m_util.str.is_unit(as.get(offset)) && offset < _pos; ++offset) {};
    if (offset == 0 && _pos > 0) {
        return BR_FAILED;
    }
    if (_pos == 0 && !constantLen) {
        return BR_FAILED;
    }
    // (extract (++ (unit x) (unit y)) 3 c) = empty
    if (offset == as.size()) {
        result = m_util.str.mk_empty(m().get_sort(a));
        return BR_DONE;
    }
    SASSERT(offset != 0 || _pos == 0);
    
    if (constantLen && _pos == offset) {
        unsigned _len = len.get_unsigned();
        // (extract (++ (unit a) (unit b) (unit c) x) 1 2) = (++ (unit b) (unit c))
        unsigned i = offset;
        for (; i < as.size() && m_util.str.is_unit(as.get(i)) && i - offset < _len; ++i);
        if (i - offset == _len) {
            result = m_util.str.mk_concat(_len, as.c_ptr() + offset);
            return BR_DONE;
        }
    }
    if (offset == 0) {
        return BR_FAILED;
    }
    expr_ref pos1(m());
    pos1 = m_autil.mk_sub(b, m_autil.mk_int(offset));
    result = m_util.str.mk_concat(as.size() - offset, as.c_ptr() + offset);
    result = m_util.str.mk_substr(result, pos1, c);
    return BR_REWRITE3;
}

bool seq_rewriter::cannot_contain_suffix(expr* a, expr* b) {
    
    if (m_util.str.is_unit(a) && m_util.str.is_unit(b) && m().are_distinct(a, b)) {
        return true;
    }
    zstring A, B;
    if (m_util.str.is_string(a, A) && m_util.str.is_string(b, B)) {
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
    
    if (m_util.str.is_unit(a) && m_util.str.is_unit(b) && m().are_distinct(a, b)) {
        return true;
    }
    zstring A, B;
    if (m_util.str.is_string(a, A) && m_util.str.is_string(b, B)) {
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
    if (m_util.str.is_string(a, c) && m_util.str.is_string(b, d)) {
        result = m().mk_bool_val(c.contains(d));
        return BR_DONE;
    }
    expr* x = nullptr, *y, *z;
    if (m_util.str.is_extract(b, x, y, z) && x == a) {
        result = m().mk_true();
        return BR_DONE;
    }

    // check if subsequence of a is in b.
    expr_ref_vector as(m()), bs(m());
    m_util.str.get_concat_units(a, as);
    m_util.str.get_concat_units(b, bs);
    
    TRACE("seq", tout << mk_pp(a, m()) << " contains " << mk_pp(b, m()) << "\n";);
   
    if (bs.empty()) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (as.empty()) {
        result = m_util.str.mk_is_empty(b);
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
    bool lA = min_length(as.size(), as.c_ptr(), lenA);
    if (lA) {
        min_length(bs.size(), bs.c_ptr(), lenB);
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
        result = m_util.str.mk_is_empty(b);
        return BR_REWRITE2;
    }
    if (offs > 0 || sz < as.size()) {
        SASSERT(sz > offs);
        result = m_util.str.mk_contains(m_util.str.mk_concat(sz-offs, as.c_ptr()+offs), b);
        return BR_REWRITE2;
    }    

    std::function<bool(expr*)> is_unit = [&](expr *e) { return m_util.str.is_unit(e); };

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
            ors.push_back(m_util.str.mk_contains(ai, bs.get(0)));
        }
        result = ::mk_or(ors);
        return BR_REWRITE_FULL;
    }


    return BR_FAILED;
}

/*
 * (str.at s i), constants s/i, i < 0 or i >= |s| ==> (str.at s i) = ""
 */
br_status seq_rewriter::mk_seq_at(expr* a, expr* b, expr_ref& result) {
    zstring c;
    rational r;
    if (!m_autil.is_numeral(b, r)) {
        return BR_FAILED;
    }
    if (r.is_neg()) {
        result = m_util.str.mk_empty(m().get_sort(a));
        return BR_DONE;
    } 
    if (!r.is_unsigned()) {
        return BR_FAILED;
    }
    unsigned len = r.get_unsigned();

    expr_ref_vector as(m());
    m_util.str.get_concat_units(a, as);

    for (unsigned i = 0; i < as.size(); ++i) {
        expr* a = as.get(i);
        if (m_util.str.is_unit(a)) {
            if (len == i) {
                result = a;
                return BR_REWRITE1;
            }            
        }
        else if (i > 0) {
            SASSERT(len >= i);
            result = m_util.str.mk_concat(as.size() - i, as.c_ptr() + i);
            result = m().mk_app(m_util.get_family_id(), OP_SEQ_AT, result, m_autil.mk_int(len - i));
            return BR_REWRITE2;
        }
        else {
            return BR_FAILED;
        }
    }
    result = m_util.str.mk_empty(m().get_sort(a));
    return BR_DONE;
}

br_status seq_rewriter::mk_seq_nth(expr* a, expr* b, expr_ref& result) {
    zstring c;
    rational r;
    if (!m_autil.is_numeral(b, r) || !r.is_unsigned()) {
        return BR_FAILED;
    }
    unsigned len = r.get_unsigned();

    expr_ref_vector as(m());
    m_util.str.get_concat_units(a, as);

    for (unsigned i = 0; i < as.size(); ++i) {
        expr* a = as.get(i), *u = nullptr;
        if (m_util.str.is_unit(a, u)) {
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
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        int idx = s1.last_indexof(s2);
        result = m_autil.mk_numeral(rational(idx), true);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_index(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s1, s2;
    rational r;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);

    if (isc1 && isc2 && m_autil.is_numeral(c, r) && r.is_unsigned()) {
        int idx = s1.indexof(s2, r.get_unsigned());
        result = m_autil.mk_numeral(rational(idx), true);
        return BR_DONE;
    }
    if (m_autil.is_numeral(c, r) && r.is_neg()) {
        result = m_autil.mk_numeral(rational(-1), true);
        return BR_DONE;
    }
    
    if (m_util.str.is_empty(b) && m_autil.is_numeral(c, r) && r.is_zero()) {
        result = c;
        return BR_DONE;
    }
    // Enhancement: walk segments of a, determine which segments must overlap, must not overlap, may overlap.
    return BR_FAILED;
}

//  (str.replace s t t') is the string obtained by replacing the first occurrence 
//  of t in s, if any, by t'. Note that if t is empty, the result is to prepend
//  t' to s; also, if t does not occur in s then the result is s.

br_status seq_rewriter::mk_seq_replace(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s1, s2, s3;
    if (m_util.str.is_string(a, s1) && m_util.str.is_string(b, s2) && 
        m_util.str.is_string(c, s3)) {
        result = m_util.str.mk_string(s1.replace(s2, s3));
        return BR_DONE;
    }
    if (b == c) {
        result = a;
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = m_util.str.mk_concat(c, a);
        return BR_REWRITE1;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_prefix(expr* a, expr* b, expr_ref& result) {
    TRACE("seq", tout << mk_pp(a, m()) << " " << mk_pp(b, m()) << "\n";);
    zstring s1, s2;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        result = m().mk_bool_val(s1.prefixof(s2));
        TRACE("seq", tout << result << "\n";);
        return BR_DONE;
    }
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    expr* a1 = m_util.str.get_leftmost_concat(a);
    expr* b1 = m_util.str.get_leftmost_concat(b);
    isc1 = m_util.str.is_string(a1, s1);
    isc2 = m_util.str.is_string(b1, s2);
    expr_ref_vector as(m()), bs(m());

    if (a1 != b1 && isc1 && isc2) {
        if (s1.length() <= s2.length()) {
            if (s1.prefixof(s2)) {
                if (a == a1) {
                    result = m().mk_true();
                    TRACE("seq", tout << s1 << " " << s2 << " " << result << "\n";);
                    return BR_DONE;
                }               
                m_util.str.get_concat(a, as);
                m_util.str.get_concat(b, bs);
                SASSERT(as.size() > 1);
                s2 = s2.extract(s1.length(), s2.length()-s1.length());
                bs[0] = m_util.str.mk_string(s2);
                result = m_util.str.mk_prefix(m_util.str.mk_concat(as.size()-1, as.c_ptr()+1),
                                              m_util.str.mk_concat(bs.size(), bs.c_ptr()));
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
                m_util.str.get_concat(a, as);
                m_util.str.get_concat(b, bs);
                SASSERT(bs.size() > 1);
                s1 = s1.extract(s2.length(), s1.length() - s2.length());
                as[0] = m_util.str.mk_string(s1);
                result = m_util.str.mk_prefix(m_util.str.mk_concat(as.size(), as.c_ptr()),
                                     m_util.str.mk_concat(bs.size()-1, bs.c_ptr()+1));
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
    m_util.str.get_concat_units(a, as);
    m_util.str.get_concat_units(b, bs);
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
        if (m_util.str.is_unit(ai) && m_util.str.is_unit(bi)) {
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
            eqs.push_back(m_util.str.mk_is_empty(as.get(j)));
        }
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }
    if (i > 0) {
        SASSERT(i < as.size() && i < bs.size());
        a = m_util.str.mk_concat(as.size() - i, as.c_ptr() + i);
        b = m_util.str.mk_concat(bs.size() - i, bs.c_ptr() + i); 
        eqs.push_back(m_util.str.mk_prefix(a, b));
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }

    return BR_FAILED;    
}

br_status seq_rewriter::mk_seq_suffix(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = m().mk_true();
        return BR_DONE;
    }
    zstring s1, s2;
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = m_util.str.mk_is_empty(a);
        return BR_REWRITE3;
    }

    bool isc1 = false;
    bool isc2 = false;
    expr *a1 = nullptr, *a2 = nullptr, *b1 = nullptr, *b2 = nullptr;
    if (m_util.str.is_concat(a, a1, a2) && m_util.str.is_string(a2, s1)) {
        isc1 = true;
    }
    else if (m_util.str.is_string(a, s1)) {
        isc1 = true;
        a2 = a;
        a1 = nullptr;
    }

    if (m_util.str.is_concat(b, b1, b2) && m_util.str.is_string(b2, s2)) {
        isc2 = true;
    }
    else if (m_util.str.is_string(b, s2)) {
        isc2 = true;
        b2 = b;
        b1 = nullptr;
    }
    if (isc1 && isc2) {
        if (s1.length() == s2.length()) {
            //SASSERT(s1 != s2);
            result = m().mk_false();
            return BR_DONE;
        }
        else if (s1.length() < s2.length()) {
            bool suffix = s1.suffixof(s2);
            if (suffix && a1 == nullptr) {
                result = m().mk_true();
                return BR_DONE;
            }
            else if (suffix) {
                s2 = s2.extract(0, s2.length()-s1.length());
                b2 = m_util.str.mk_string(s2);
                result = m_util.str.mk_suffix(a1, b1?m_util.str.mk_concat(b1, b2):b2);
                return BR_DONE;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }
        else {
            SASSERT(s1.length() > s2.length());
            if (b1 == nullptr) {
                result = m().mk_false();
                return BR_DONE;
            }
            bool suffix = s2.suffixof(s1);
            if (suffix) {
                s1 = s1.extract(0, s1.length()-s2.length());
                a2 = m_util.str.mk_string(s1);
                result = m_util.str.mk_suffix(a1?m_util.str.mk_concat(a1, a2):a2, b1);
                return BR_DONE;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }            
        }
    }
    expr_ref_vector as(m()), bs(m()), eqs(m());
    m_util.str.get_concat_units(a, as);
    m_util.str.get_concat_units(b, bs);
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
        if (m_util.str.is_unit(ai) && m_util.str.is_unit(bi)) {
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
            eqs.push_back(m_util.str.mk_is_empty(aj));
        }
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }

    if (i > 1) {
        SASSERT(i <= sza && i <= szb);
        a = m_util.str.mk_concat(sza - i + 1, as.c_ptr());
        b = m_util.str.mk_concat(szb - i + 1, bs.c_ptr());
        eqs.push_back(m_util.str.mk_suffix(a, b));
        result = mk_and(eqs);
        TRACE("seq", tout << result << "\n";);
        return BR_REWRITE3;
    }

    return BR_FAILED;
}

br_status seq_rewriter::mk_str_itos(expr* a, expr_ref& result) {
    rational r;
    if (m_autil.is_numeral(a, r)) {
        if (r.is_int() && !r.is_neg()) {
            result = m_util.str.mk_string(symbol(r.to_string().c_str()));
        }
        else {
            result = m_util.str.mk_string(symbol(""));
        }
        return BR_DONE;
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
    zstring str;
    if (m_util.str.is_string(a, str)) {
        std::string s = str.encode();
        if (s.length() == 0) {
            result = m_autil.mk_int(-1);
            return BR_DONE;
        } 
        for (unsigned i = 0; i < s.length(); ++i) {
            if (!('0' <= s[i] && s[i] <= '9')) {
                result = m_autil.mk_int(-1);
                return BR_DONE;
            }
        }
        rational r(s.c_str());
        result = m_autil.mk_numeral(r, true);
        return BR_DONE;
    }
    expr* b;
    if (m_util.str.is_itos(a, b)) {
        result = m().mk_ite(m_autil.mk_ge(b, m_autil.mk_int(0)), b, m_autil.mk_int(-1));
        return BR_DONE;
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
        seq.push_back(m_util.str.mk_unit(t->get_char()));
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
        if (m_util.str.is_string(e, s)) {
            for (unsigned i = 0; i < s.length(); ++i) {
                seq.push_back(m_util.str.mk_char(s, i));
            }
        }
        else if (m_util.str.is_empty(e)) {
            continue;
        }
        else if (m_util.str.is_unit(e, e1)) {
            seq.push_back(e1);
        }
        else if (m_util.str.is_concat(e, e1, e2)) {
            todo.push_back(e2);
            todo.push_back(e1);
        }
        else {
            return false;
        }
    }
    return true;
}

br_status seq_rewriter::mk_str_in_regexp(expr* a, expr* b, expr_ref& result) {
    if (m_util.re.is_empty(b)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(b)) {
        result = m().mk_true();
        return BR_DONE;
    }
    scoped_ptr<eautomaton> aut;
    expr_ref_vector seq(m());
    if (!(aut = m_re2aut(b))) {
        TRACE("seq", tout << "not translated to automaton " << mk_pp(b, m()) << "\n";);
        return BR_FAILED;
    }

    if (is_sequence(*aut, seq)) {
        TRACE("seq", tout << seq << "\n";);
              
        if (seq.empty()) {
            result = m_util.str.mk_is_empty(a);
        }
        else {
            result = m().mk_eq(a, m_util.str.mk_concat(seq));
        }
        return BR_REWRITE3;
    }

    if (!is_sequence(a, seq)) {
        TRACE("seq", tout << "not a sequence " << mk_pp(a, m()) << "\n";);
        return BR_FAILED;
    } 
        
    expr_ref_vector trail(m());
    u_map<expr*> maps[2];
    bool select_map = false;
    expr_ref ch(m()), cond(m());
    eautomaton::moves mvs;
    maps[0].insert(aut->init(), m().mk_true());
    // is_accepted(a, aut) & some state in frontier is final.
    
    for (unsigned i = 0; i < seq.size(); ++i) {
        u_map<expr*>& frontier = maps[select_map];
        u_map<expr*>& next = maps[!select_map];
        select_map = !select_map;
        ch = seq[i].get();
        next.reset();
        u_map<expr*>::iterator it = frontier.begin(), end = frontier.end();
        for (; it != end; ++it) {
            mvs.reset();
            unsigned state = it->m_key;
            expr*    acc  = it->m_value;
            aut->get_moves_from(state, mvs, false);
            for (unsigned j = 0; j < mvs.size(); ++j) {
                eautomaton::move const& mv = mvs[j];
                SASSERT(mv.t());
                if (mv.t()->is_char() && m().is_value(mv.t()->get_char()) && m().is_value(ch)) {
                    if (mv.t()->get_char() == ch) {
                        add_next(next, trail, mv.dst(), acc);
                    }
                    else {
                        continue;
                    }
                }
                else {
                    cond = mv.t()->accept(ch);
                    if (m().is_false(cond)) {
                        continue;
                    }
                    if (m().is_true(cond)) {
                        add_next(next, trail, mv.dst(), acc);
                        continue;
                    }
                    expr* args[2] = { cond, acc };
                    cond = mk_and(m(), 2, args);
                    add_next(next, trail, mv.dst(), cond);
                }
            }                
        }
    }
    u_map<expr*> const& frontier = maps[select_map];
    expr_ref_vector ors(m());
    for (auto const& kv : frontier) {
        unsigned_vector states;
        bool has_final = false;
        aut->get_epsilon_closure(kv.m_key, states);
        for (unsigned i = 0; i < states.size() && !has_final; ++i) {
            has_final = aut->is_final_state(states[i]);
        }
        if (has_final) {
            ors.push_back(kv.m_value);
        }
    }
    result = mk_or(ors);
    TRACE("seq", tout << result << "\n";);
    return BR_REWRITE_FULL;
}
br_status seq_rewriter::mk_str_to_regexp(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_concat(expr* a, expr* b, expr_ref& result) {
    if (m_util.re.is_full_seq(a) && m_util.re.is_full_seq(b)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_empty(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_empty(b)) {
        result = b;
        return BR_DONE;
    }
    if (is_epsilon(a)) {
        result = b;
        return BR_DONE;
    }
    if (is_epsilon(b)) {
        result = a;
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
    if (a == b) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_empty(a)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.re.is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(b)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.re.is_star(a) && is_epsilon(b)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_star(b) && is_epsilon(a)) {
        result = b;
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_re_complement(expr* a, expr_ref& result) {
    expr* e1, *e2;
    if (m_util.re.is_intersection(a, e1, e2)) {
        result = m_util.re.mk_union(m_util.re.mk_complement(e1), m_util.re.mk_complement(e2));
        return BR_REWRITE2;
    }
    if (m_util.re.is_union(a, e1, e2)) {
        result = m_util.re.mk_inter(m_util.re.mk_complement(e1), m_util.re.mk_complement(e2));
        return BR_REWRITE2;
    }
    if (m_util.re.is_empty(a)) {
        result = m_util.re.mk_full_seq(m().get_sort(a));
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(a)) {
        result = m_util.re.mk_empty(m().get_sort(a));
        return BR_DONE;
    }
    return BR_FAILED;
}

/**
   (emp n r) = emp
   (r n emp) = emp
   (all n r) = r
   (r n all) = r
   (r n r) = r
 */
br_status seq_rewriter::mk_re_inter(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_empty(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_empty(b)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(a)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(b)) {
        result = a;
        return BR_DONE;
    }
    expr* ac = nullptr, *bc = nullptr;
    if ((m_util.re.is_complement(a, ac) && ac == b) ||
        (m_util.re.is_complement(b, bc) && bc == a)) {
        sort* seq_sort = nullptr;
        VERIFY(m_util.is_re(a, seq_sort));
        result = m_util.re.mk_empty(seq_sort);
        return BR_DONE;
    }
    return BR_FAILED;
}


br_status seq_rewriter::mk_re_loop(unsigned num_args, expr* const* args, expr_ref& result) {
    rational n1, n2;
    switch (num_args) {
    case 1: 
        break;
    case 2:
        if (m_autil.is_numeral(args[1], n1) && n1.is_unsigned()) {
            result = m_util.re.mk_loop(args[0], n1.get_unsigned());
            return BR_DONE;
        }
        break;
    case 3:
        if (m_autil.is_numeral(args[1], n1) && n1.is_unsigned() &&
            m_autil.is_numeral(args[2], n2) && n2.is_unsigned()) {
            result = m_util.re.mk_loop(args[0], n1.get_unsigned(), n2.get_unsigned());
            return BR_DONE;
        }
        break;
    default:
        break;
    }
    return BR_FAILED;
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
    if (m_util.re.is_star(a) || m_util.re.is_full_seq(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_full_char(a)) {
        result = m_util.re.mk_full_seq(m().get_sort(a));
        return BR_DONE;
    }
    if (m_util.re.is_empty(a)) {
        sort* seq_sort = nullptr;
        VERIFY(m_util.is_re(a, seq_sort));
        result = m_util.re.mk_to_re(m_util.str.mk_empty(seq_sort));
        return BR_DONE;
    }
    if (m_util.re.is_plus(a, b)) {
        result = m_util.re.mk_star(b);
        return BR_DONE;
    }
    if (m_util.re.is_union(a, b, c)) {
        if (m_util.re.is_star(b, b1)) {
            result = m_util.re.mk_star(m_util.re.mk_union(b1, c));
            return BR_REWRITE2;
        }
        if (m_util.re.is_star(c, c1)) {
            result = m_util.re.mk_star(m_util.re.mk_union(b, c1));
            return BR_REWRITE2;
        }
        if (is_epsilon(b)) {
            result = m_util.re.mk_star(c);
            return BR_REWRITE2;
        }
        if (is_epsilon(c)) {
            result = m_util.re.mk_star(b);
            return BR_REWRITE2;
        }
    }
    if (m_util.re.is_concat(a, b, c) &&
        m_util.re.is_star(b, b1) && m_util.re.is_star(c, c1)) {
        result = m_util.re.mk_star(m_util.re.mk_union(b1, c1));
        return BR_REWRITE2;
    }

    return BR_FAILED;
}

/*
 * (re.range c_1 c_n) 
 */
br_status seq_rewriter::mk_re_range(expr* lo, expr* hi, expr_ref& result) {
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
    if (m_util.re.is_empty(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_full_seq(a)) {
        result = a;
        return BR_DONE;
    }
    if (is_epsilon(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_plus(a)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.re.is_star(a)) {
        result = a;
        return BR_DONE;
    }

    //return BR_FAILED;
    result = m_util.re.mk_concat(a, m_util.re.mk_star(a));
    return BR_REWRITE2;
}

br_status seq_rewriter::mk_re_opt(expr* a, expr_ref& result) {
    sort* s = nullptr;
    VERIFY(m_util.is_re(a, s));
    result = m_util.re.mk_union(m_util.re.mk_to_re(m_util.str.mk_empty(s)), a);
    return BR_REWRITE1;
}

br_status seq_rewriter::mk_eq_core(expr * l, expr * r, expr_ref & result) {
    TRACE("seq", tout << mk_pp(l, m()) << " = " << mk_pp(r, m()) << "\n";);
    expr_ref_vector lhs(m()), rhs(m()), res(m());
    bool changed = false;
    if (!reduce_eq(l, r, lhs, rhs, changed)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (!changed) {
        return BR_FAILED;
    }
    for (unsigned i = 0; i < lhs.size(); ++i) {
        res.push_back(m().mk_eq(lhs.get(i), rhs.get(i)));
    }
    result = mk_and(res);
    return BR_REWRITE3;
}

bool seq_rewriter::reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_vector& lhs, expr_ref_vector& rhs, bool& change) {
    expr* a, *b;
    zstring s;
    bool lchange = false;
    SASSERT(lhs.empty());
    TRACE("seq", tout << ls << "\n"; tout << rs << "\n";);
    // solve from back
    while (true) {
        while (!rs.empty() && m_util.str.is_empty(rs.back())) {
            rs.pop_back();
        }
        while (!ls.empty() && m_util.str.is_empty(ls.back())) {
            ls.pop_back();
        }
        if (ls.empty() || rs.empty()) {
            break;
        }
        expr* l = ls.back();
        expr* r = rs.back();
        if (m_util.str.is_unit(r) && m_util.str.is_string(l)) {
            std::swap(l, r);
            ls.swap(rs);
        }
        if (l == r) {
            ls.pop_back();
            rs.pop_back();
        }
        else if(m_util.str.is_unit(l, a) &&
                m_util.str.is_unit(r, b)) {
            if (m().are_distinct(a, b)) {
                return false;
            }
            lhs.push_back(a);
            rhs.push_back(b);
            ls.pop_back();
            rs.pop_back();
        }
        else if (m_util.str.is_unit(l, a) && m_util.str.is_string(r, s)) {
            SASSERT(s.length() > 0);
            
            app* ch = m_util.str.mk_char(s, s.length()-1);
            SASSERT(m().get_sort(ch) == m().get_sort(a));
            lhs.push_back(ch);
            rhs.push_back(a);
            ls.pop_back();
            if (s.length() == 1) {
                rs.pop_back();
            }
            else {
                expr_ref s2(m_util.str.mk_string(s.extract(0, s.length()-1)), m());
                rs[rs.size()-1] = s2;
            }
        }
        else {
            break;
        }
        change = true;
        lchange = true;
    }

    // solve from front
    unsigned head1 = 0, head2 = 0;
    while (true) {
        while (head1 < ls.size() && m_util.str.is_empty(ls[head1].get())) {
            ++head1;
        }
        while (head2 < rs.size() && m_util.str.is_empty(rs[head2].get())) {
            ++head2;
        }
        if (head1 == ls.size() || head2 == rs.size()) {
            break;
        }
        SASSERT(head1 < ls.size() && head2 < rs.size());

        expr* l = ls[head1].get();
        expr* r = rs[head2].get();
        if (m_util.str.is_unit(r) && m_util.str.is_string(l)) {
            std::swap(l, r);
            ls.swap(rs);
            std::swap(head1, head2);
        }
        if (l == r) {
            ++head1;
            ++head2;
        }
        else if(m_util.str.is_unit(l, a) &&
                m_util.str.is_unit(r, b)) {
            if (m().are_distinct(a, b)) {
                return false;
            }
            lhs.push_back(a);
            rhs.push_back(b);
            ++head1;
            ++head2;
        }
        else if (m_util.str.is_unit(l, a) && m_util.str.is_string(r, s)) {
            SASSERT(s.length() > 0);
            app* ch = m_util.str.mk_char(s, 0);
            SASSERT(m().get_sort(ch) == m().get_sort(a));
            lhs.push_back(ch);
            rhs.push_back(a);
            ++head1;
            if (s.length() == 1) {
                ++head2;
            }
            else {
                expr_ref s2(m_util.str.mk_string(s.extract(1, s.length()-1)), m());
                rs[head2] = s2;
            }            
        }
        else {
            break;
        }
        TRACE("seq", tout << ls << " == " << rs << "\n";);
       
        change = true;
        lchange = true;
    }
    // reduce strings
    zstring s1, s2;
    while (head1 < ls.size() && 
           head2 < rs.size() && 
           m_util.str.is_string(ls[head1].get(), s1) &&
           m_util.str.is_string(rs[head2].get(), s2)) {
        TRACE("seq", tout << s1 << " - " << s2 << " " << s1.length() << " " << s2.length() << "\n";);
        unsigned l = std::min(s1.length(), s2.length());
        for (unsigned i = 0; i < l; ++i) {
            if (s1[i] != s2[i]) {
                TRACE("seq", tout << "different at position " << i << " " << s1[i] << " " << s2[i] << "\n";);
                return false;
            }
        }
        if (l == s1.length()) {
            ++head1;            
        }
        else {
            ls[head1] = m_util.str.mk_string(s1.extract(l, s1.length()-l));
        }
        if (l == s2.length()) {
            ++head2;            
        }
        else {
            rs[head2] = m_util.str.mk_string(s2.extract(l, s2.length()-l));
        }
        TRACE("seq", tout << "change string\n";);
        change = true;
        lchange = true;
    }
    while (head1 < ls.size() && 
           head2 < rs.size() &&
           m_util.str.is_string(ls.back(), s1) &&
           m_util.str.is_string(rs.back(), s2)) {
        unsigned l = std::min(s1.length(), s2.length());
        for (unsigned i = 0; i < l; ++i) {
            if (s1[s1.length()-i-1] != s2[s2.length()-i-1]) {
                return false;
            }
        }
        ls.pop_back();          
        rs.pop_back();
        if (l < s1.length()) {
            ls.push_back(m_util.str.mk_string(s1.extract(0, s1.length()-l)));
        }
        if (l < s2.length()) {
            rs.push_back(m_util.str.mk_string(s2.extract(0, s2.length()-l)));
        }        
        TRACE("seq", tout << "change string back\n";);
        change = true;
        lchange = true;
    }

    bool is_sat = true;
    unsigned szl = ls.size() - head1, szr = rs.size() - head2;
    expr* const* _ls = ls.c_ptr() + head1, * const* _rs = rs.c_ptr() + head2;

    if (solve_itos(szl, _ls, szr, _rs, lhs, rhs, is_sat)) {
        ls.reset(); rs.reset();
        change = true;
        return is_sat;
    }

    if (length_constrained(szl, _ls, szr, _rs, lhs, rhs, is_sat)) {
        ls.reset(); rs.reset();
        change = true;
        return is_sat;
    }

    if (szr == 0 && szl == 0) {
        ls.reset();
        rs.reset();
        return true;
    }
    if (szr == 0 && szl > 0) {
        std::swap(szr, szl);
        std::swap(_ls, _rs);
    }
    if (szl == 0 && szr > 0) {
        if (set_empty(szr, _rs, true, lhs, rhs)) {
            lchange |= szr > 1; 
            change  |= szr > 1;
            if (szr == 1 && !lchange) {
                lhs.reset();
                rhs.reset();
            }
            else {
                ls.reset();        
                rs.reset();
            }
            return true;
        }
        else {
            return false;
        }
    }
    SASSERT(szl > 0 && szr > 0);

    if (is_subsequence(szl, _ls, szr, _rs, lhs, rhs, is_sat)) {
        ls.reset(); rs.reset();
        change = true;
        return is_sat;
    }

    if (lchange) {
        if (head1 > 0) {
            for (unsigned i = 0; i < szl; ++i) {
                ls[i] = ls[i + head1].get();
            }
        }
        ls.shrink(szl);
        if (head2 > 0) {
            for (unsigned i = 0; i < szr; ++i) {
                rs[i] = rs[i + head2].get();
            }
        }
        rs.shrink(szr);
    }
    SASSERT(rs.empty() == ls.empty());
    change |= lchange;
    return true;
}

void seq_rewriter::add_seqs(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref_vector& lhs, expr_ref_vector& rhs) {
    if (ls.empty() && !rs.empty()) {
        rhs.push_back(m_util.str.mk_concat(rs));
        lhs.push_back(m_util.str.mk_empty(m().get_sort(rhs.back())));
    }
    else if (rs.empty() && !ls.empty()) {
        lhs.push_back(m_util.str.mk_concat(ls));
        rhs.push_back(m_util.str.mk_empty(m().get_sort(lhs.back())));
    }
    else if (!rs.empty() && !ls.empty()) {
        lhs.push_back(m_util.str.mk_concat(ls));
        rhs.push_back(m_util.str.mk_concat(rs));
    }
}


bool seq_rewriter::reduce_eq(expr* l, expr* r, expr_ref_vector& lhs, expr_ref_vector& rhs, bool& changed) {
    m_lhs.reset();
    m_rhs.reset();
    m_util.str.get_concat(l, m_lhs);
    m_util.str.get_concat(r, m_rhs);
    bool change = false;
    if (reduce_eq(m_lhs, m_rhs, lhs, rhs, change)) {
        SASSERT(lhs.size() == rhs.size());
        if (!change) {
            lhs.push_back(l);
            rhs.push_back(r);
        }
        else {
            add_seqs(m_lhs, m_rhs, lhs, rhs);
        }
        changed |= change;
        return true;
    }
    else {
        TRACE("seq", tout << mk_pp(l, m()) << " != " << mk_pp(r, m()) << "\n";);
        return false;
    }
}

bool seq_rewriter::reduce_contains(expr* a, expr* b, expr_ref_vector& disj) {
    m_lhs.reset();
    m_util.str.get_concat(a, m_lhs);
    TRACE("seq", tout << expr_ref(a, m()) << " " << expr_ref(b, m()) << "\n";);
    zstring s;
    for (unsigned i = 0; i < m_lhs.size(); ++i) {
        expr* e = m_lhs.get(i);
        if (m_util.str.is_empty(e)) {
            continue;
        }

        if (m_util.str.is_string(e, s)) {
            unsigned sz = s.length();
            expr_ref_vector es(m());
            for (unsigned j = 0; j < sz; ++j) {
                es.push_back(m_util.str.mk_unit(m_util.str.mk_char(s, j)));
            }
            es.append(m_lhs.size() - i, m_lhs.c_ptr() + i);
            for (unsigned j = 0; j < sz; ++j) {
                disj.push_back(m_util.str.mk_prefix(b, m_util.str.mk_concat(es.size() - j, es.c_ptr() + j)));
            }
            continue;
        }
        if (m_util.str.is_unit(e)) {
            disj.push_back(m_util.str.mk_prefix(b, m_util.str.mk_concat(m_lhs.size() - i, m_lhs.c_ptr() + i)));
            continue;
        }

        if (m_util.str.is_string(b, s)) {
            expr* all = m_util.re.mk_full_seq(m_util.re.mk_re(m().get_sort(b)));
            disj.push_back(m_util.re.mk_in_re(m_util.str.mk_concat(m_lhs.size() - i, m_lhs.c_ptr() + i),
                                              m_util.re.mk_concat(all, m_util.re.mk_concat(m_util.re.mk_to_re(b), all))));
            return true;
        }

        if (i == 0) {
            return false;
        }
        disj.push_back(m_util.str.mk_contains(m_util.str.mk_concat(m_lhs.size() - i, m_lhs.c_ptr() + i), b));
        return true;
    }
    disj.push_back(m_util.str.mk_is_empty(b));
    return true;
}


expr* seq_rewriter::concat_non_empty(unsigned n, expr* const* as) {
    SASSERT(n > 0);
    ptr_vector<expr> bs;
    for (unsigned i = 0; i < n; ++i) {
        if (m_util.str.is_unit(as[i]) ||
            m_util.str.is_string(as[i])) {
            bs.push_back(as[i]);
        }
    }    
    if (bs.empty()) {
        return m_util.str.mk_empty(m().get_sort(as[0]));
    }
    else {
        return m_util.str.mk_concat(bs.size(), bs.c_ptr());
    }
}

bool seq_rewriter::set_empty(unsigned sz, expr* const* es, bool all, expr_ref_vector& lhs, expr_ref_vector& rhs) {
    zstring s;
    expr* emp = nullptr;
    for (unsigned i = 0; i < sz; ++i) {
        if (m_util.str.is_unit(es[i])) {
            if (all) return false;
        }
        else if (m_util.str.is_empty(es[i])) {
            continue;
        }
        else if (m_util.str.is_string(es[i], s)) {
            if (all) {
                SASSERT(s.length() > 0);
                return false;
            }
        }
        else {
            emp = emp?emp:m_util.str.mk_empty(m().get_sort(es[i]));
            lhs.push_back(emp);
            rhs.push_back(es[i]);
        }
    }
    return true;
}

bool seq_rewriter::min_length(unsigned n, expr* const* es, unsigned& len) {
    zstring s;
    bool bounded = true;
    len = 0;
    for (unsigned i = 0; i < n; ++i) {
        if (m_util.str.is_unit(es[i])) {
            ++len;
        }
        else if (m_util.str.is_empty(es[i])) {
            continue;
        }
        else if (m_util.str.is_string(es[i], s)) {
            len += s.length();
        }
        else {
            bounded = false;
        }
    }
    return bounded;
}

bool seq_rewriter::is_string(unsigned n, expr* const* es, zstring& s) const {
    zstring s1;
    expr* e;
    unsigned ch;
    for (unsigned i = 0; i < n; ++i) {
        if (m_util.str.is_string(es[i], s1)) {
            s = s + s1;
        }
        else if (m_util.str.is_unit(es[i], e) && m_util.is_const_char(e, ch)) {
            s = s + zstring(ch);
        }
        else {
            return false;
        }
    }
    return true;
}

bool seq_rewriter::solve_itos(unsigned szl, expr* const* ls, unsigned szr, expr* const* rs, 
                              expr_ref_vector& lhs, expr_ref_vector& rhs, bool& is_sat) {

    expr* l, *r;
    is_sat = true;
    if (szl == 1 && m_util.str.is_itos(ls[0], l)) {
        if (szr == 1 && m_util.str.is_itos(rs[0], r)) {
            lhs.push_back(l);
            rhs.push_back(r);
            return true;
        }
        zstring s;
        if (is_string(szr, rs, s)) {
            std::string s1 = s.encode();
            rational r(s1.c_str());
            if (s1 == r.to_string()) {
                lhs.push_back(l);
                rhs.push_back(m_autil.mk_numeral(r, true));
                return true;
            }
        }
    }

    if (szr == 1 && szl >= 1 && m_util.str.is_itos(rs[0], r) && !m_util.str.is_itos(ls[0])) {
        return solve_itos(szr, rs, szl, ls, rhs, lhs, is_sat);
    }

    return false;
}

bool seq_rewriter::length_constrained(unsigned szl, expr* const* l, unsigned szr, expr* const* r, 
                                      expr_ref_vector& lhs, expr_ref_vector& rhs, bool& is_sat) {
    is_sat = true;
    unsigned len1 = 0, len2 = 0;
    bool bounded1 = min_length(szl, l, len1);
    bool bounded2 = min_length(szr, r, len2);
    if (bounded1 && len1 < len2) {
        is_sat = false;
        return true;
    }
    if (bounded2 && len2 < len1) {
        is_sat = false;
        return true;
    }
    if (bounded1 && len1 == len2 && len1 > 0) {
        is_sat = set_empty(szr, r, false, lhs, rhs);
        if (is_sat) {
            lhs.push_back(concat_non_empty(szl, l));
            rhs.push_back(concat_non_empty(szr, r));
            //split_units(lhs, rhs);
        }
        return true;
    }
    if (bounded2 && len1 == len2 && len1 > 0) {
        is_sat = set_empty(szl, l, false, lhs, rhs);
        if (is_sat) {
            lhs.push_back(concat_non_empty(szl, l));
            rhs.push_back(concat_non_empty(szr, r));
            //split_units(lhs, rhs);
        }
        return true;
    }    
    return false;
}

void seq_rewriter::split_units(expr_ref_vector& lhs, expr_ref_vector& rhs) {
    expr* a, *b, *a1, *b1, *a2, *b2;
    while (true) {
        if (m_util.str.is_unit(lhs.back(), a) &&
            m_util.str.is_unit(rhs.back(), b)) {
            lhs[lhs.size()-1] = a;
            rhs[rhs.size()-1] = b;
            break;
        }
        if (m_util.str.is_concat(lhs.back(), a, a2) && 
            m_util.str.is_unit(a, a1) && 
            m_util.str.is_concat(rhs.back(), b, b2) &&
            m_util.str.is_unit(b, b1)) {
            expr_ref _pin_a(lhs.back(), m()), _pin_b(rhs.back(), m());
            lhs[lhs.size()-1] = a1;
            rhs[rhs.size()-1] = b1;
            lhs.push_back(a2);
            rhs.push_back(b2);
        }
        else {
            break;
        }
    }
}



bool seq_rewriter::is_epsilon(expr* e) const {
    expr* e1;
    return m_util.re.is_to_re(e, e1) && m_util.str.is_empty(e1);
}

bool seq_rewriter::is_subsequence(unsigned szl, expr* const* l, unsigned szr, expr* const* r, 
                                  expr_ref_vector& lhs, expr_ref_vector& rhs, bool& is_sat) {
    is_sat = true;
    if (szl == szr) return false;
    if (szr < szl) {
        std::swap(szl, szr);
        std::swap(l, r);
    }

    uint_set rpos;
    for (unsigned i = 0; i < szl; ++i) {
        bool found = false;
        unsigned j = 0;
        bool is_unit = m_util.str.is_unit(l[i]);
        for (; !found && j < szr; ++j) {
            found = !rpos.contains(j) && (l[i] == r[j] || (is_unit && m_util.str.is_unit(r[j])));
        }
        
        if (!found) {
            return false;
        }
        SASSERT(0 < j && j <= szr);
        rpos.insert(j-1);
    }
    // if we reach here, then every element of l is contained in r in some position.
    // or each non-unit in l is matched by a non-unit in r, and otherwise, the non-units match up.
    bool change = false;
    ptr_vector<expr> rs;
    for (unsigned j = 0; j < szr; ++j) {
        if (rpos.contains(j)) {
            rs.push_back(r[j]);
        }
        else if (!set_empty(1, r + j, true, lhs, rhs)) {
            is_sat = false;
            return true;
        }
        else {
            change = true;
        }
    }
    if (!change) {
        return false;
    }
    SASSERT(szl == rs.size());
    if (szl > 0) {
        lhs.push_back(m_util.str.mk_concat(szl, l));
        rhs.push_back(m_util.str.mk_concat(szl, rs.c_ptr()));
    }
    return true;
} 
