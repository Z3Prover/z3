/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_rewriter.h

Abstract:

    Basic rewriting rules for sequences constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5

Notes:

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "ast/rewriter/bool_rewriter.h"
#include "util/params.h"
#include "util/lbool.h"
#include "util/sign.h"
#include "math/automata/automaton.h"
#include "math/automata/symbolic_automata.h"


inline std::ostream& operator<<(std::ostream& out, expr_ref_pair_vector const& es) {
    for (auto const& p : es) {
        out << expr_ref(p.first, es.get_manager()) << "; " << expr_ref(p.second, es.get_manager()) << "\n";
    }
    return out;
}

class sym_expr {
    enum ty {
        t_char,
        t_pred,
        t_not,
        t_range
    };
    ty        m_ty;
    sort*     m_sort;
    sym_expr* m_expr;
    expr_ref  m_t;
    expr_ref  m_s;
    unsigned  m_ref;
    sym_expr(ty ty, expr_ref& t, expr_ref& s, sort* srt, sym_expr* e) : 
        m_ty(ty), m_sort(srt), m_expr(e), m_t(t), m_s(s), m_ref(0) {}
public:
    ~sym_expr() { if (m_expr) m_expr->dec_ref(); }
    expr_ref accept(expr* e);
    static sym_expr* mk_char(expr_ref& t) { return alloc(sym_expr, t_char, t, t, t->get_sort(), nullptr); }
    static sym_expr* mk_char(ast_manager& m, expr* t) { expr_ref tr(t, m); return mk_char(tr); }
    static sym_expr* mk_pred(expr_ref& t, sort* s) { return alloc(sym_expr, t_pred, t, t, s, nullptr); }
    static sym_expr* mk_range(expr_ref& lo, expr_ref& hi) { return alloc(sym_expr, t_range, lo, hi, hi->get_sort(), nullptr); }
    static sym_expr* mk_not(ast_manager& m, sym_expr* e) { expr_ref f(m); e->inc_ref(); return alloc(sym_expr, t_not, f, f, e->get_sort(), e); }
    void inc_ref() { ++m_ref;  }
    void dec_ref() { --m_ref; if (m_ref == 0) dealloc(this); }
    std::ostream& display(std::ostream& out) const;
    bool is_char() const { return m_ty == t_char; }
    bool is_pred() const { return !is_char(); }
    bool is_range() const { return m_ty == t_range; }
    bool is_not() const { return m_ty == t_not; }
    sort* get_sort() const { return m_sort; }
    expr* get_char() const { SASSERT(is_char()); return m_t; }
    expr* get_pred() const { SASSERT(is_pred()); return m_t; }
    expr* get_lo() const { SASSERT(is_range()); return m_t; }
    expr* get_hi() const { SASSERT(is_range()); return m_s; }
    sym_expr* get_arg() const { SASSERT(is_not()); return m_expr; }
};

class sym_expr_manager {
public:
    void inc_ref(sym_expr* s) { if (s) s->inc_ref(); }
    void dec_ref(sym_expr* s) { if (s) s->dec_ref(); }
};

class expr_solver {
public:
    virtual ~expr_solver() {}
    virtual lbool check_sat(expr* e) = 0;
};

typedef automaton<sym_expr, sym_expr_manager> eautomaton;
class re2automaton {
    typedef boolean_algebra<sym_expr*> boolean_algebra_t;
    typedef symbolic_automata<sym_expr, sym_expr_manager> symbolic_automata_t;
    ast_manager& m;
    sym_expr_manager sm;
    seq_util     u;     
    scoped_ptr<expr_solver>         m_solver;
    scoped_ptr<boolean_algebra_t>   m_ba;
    scoped_ptr<symbolic_automata_t> m_sa;

    bool is_unit_char(expr* e, expr_ref& ch);
    eautomaton* re2aut(expr* e);
    eautomaton* seq2aut(expr* e);
public:
    re2automaton(ast_manager& m);
    eautomaton* operator()(expr* e);
    void set_solver(expr_solver* solver);
    bool has_solver() const { return m_solver; }
    eautomaton* mk_product(eautomaton *a1, eautomaton *a2);
};

/**
   \brief Cheap rewrite rules for seq constraints
*/
class seq_rewriter {

    class op_cache {
        struct op_entry {
            decl_kind k;
            expr* a, *b, *r;
            op_entry(decl_kind k, expr* a, expr* b, expr* r): k(k), a(a), b(b), r(r) {}
            op_entry():k(0), a(nullptr), b(nullptr), r(nullptr) {}
        };

        struct hash_entry {
            unsigned operator()(op_entry const& e) const { 
                return mk_mix(e.k, e.a ? e.a->get_id() : 0, e.b ? e.b->get_id() : 0);
            }
        };

        struct eq_entry {
            bool operator()(op_entry const& a, op_entry const& b) const { 
                return a.k == b.k && a.a == b.a && a.b == b.b;
            }
        };

        typedef hashtable<op_entry, hash_entry, eq_entry> op_table;

        unsigned        m_max_cache_size { 10000 };
        expr_ref_vector m_trail;
        op_table        m_table;
        void cleanup();

    public:
        op_cache(ast_manager& m);
        expr* find(decl_kind op, expr* a, expr* b);
        void insert(decl_kind op, expr* a, expr* b, expr* r);
    };

    seq_util       m_util;
    arith_util     m_autil;
    bool_rewriter  m_br;
    re2automaton   m_re2aut;
    op_cache       m_op_cache;
    expr_ref_vector m_es, m_lhs, m_rhs;
    bool           m_coalesce_chars;    

    enum length_comparison {
        shorter_c, 
        longer_c,
        same_length_c,
        unknown_c
    };



    length_comparison compare_lengths(expr_ref_vector const& as, expr_ref_vector const& bs) {
        return compare_lengths(as.size(), as.data(), bs.size(), bs.data());
    }
    length_comparison compare_lengths(unsigned sza, expr* const* as, unsigned szb, expr* const* bs);


    bool get_head_tail(expr* e, expr_ref& head, expr_ref& tail);
    bool get_head_tail_reversed(expr* e, expr_ref& head, expr_ref& tail);
    bool get_re_head_tail(expr* e, expr_ref& head, expr_ref& tail);
    bool get_re_head_tail_reversed(expr* e, expr_ref& head, expr_ref& tail);

    expr_ref re_and(expr* cond, expr* r);
    expr_ref re_predicate(expr* cond, sort* seq_sort);

    expr_ref mk_seq_concat(expr* a, expr* b);    

    // Calculate derivative, memoized and enforcing a normal form
    expr_ref is_nullable_rec(expr* r);
    expr_ref mk_derivative_rec(expr* ele, expr* r);
    expr_ref mk_der_op(decl_kind k, expr* a, expr* b);
    expr_ref mk_der_op_rec(decl_kind k, expr* a, expr* b);
    expr_ref mk_der_concat(expr* a, expr* b);
    expr_ref mk_der_union(expr* a, expr* b);
    expr_ref mk_der_inter(expr* a, expr* b);
    expr_ref mk_der_compl(expr* a);
    expr_ref mk_der_cond(expr* cond, expr* ele, sort* seq_sort);
    expr_ref mk_der_antimorov_union(expr* r1, expr* r2);
    bool ite_bdds_compatabile(expr* a, expr* b);
    /* if r has the form deriv(en..deriv(e1,to_re(s))..) returns 's = [e1..en]' else returns '() in r'*/
    expr_ref is_nullable_symbolic_regex(expr* r, sort* seq_sort);
    #ifdef Z3DEBUG
    bool check_deriv_normal_form(expr* r, int level = 3);
    #endif

    bool lt_char(expr* ch1, expr* ch2);
    bool eq_char(expr* ch1, expr* ch2);
    bool le_char(expr* ch1, expr* ch2);
    bool pred_implies(expr* a, expr* b);
    bool are_complements(expr* r1, expr* r2) const;
    bool is_subset(expr* r1, expr* r2) const;

    br_status mk_seq_unit(expr* e, expr_ref& result);
    br_status mk_seq_concat(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_length(expr* a, expr_ref& result);
    expr_ref mk_len(rational const& offset, expr_ref_vector const& xs);
    bool extract_pop_suffix(expr_ref_vector const& as, expr* b, expr* c, expr_ref& result);
    bool extract_push_offset(expr_ref_vector const& as, expr* b, expr* c, expr_ref& result);
    bool extract_push_length(expr_ref_vector& as, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_extract(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_contains(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_at(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_nth(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_nth_i(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_index(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_last_index(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_replace(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_replace_all(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_replace_re_all(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_replace_re(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_prefix(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_suffix(expr* a, expr* b, expr_ref& result);
    br_status mk_str_units(func_decl* f, expr_ref& result);
    br_status mk_str_itos(expr* a, expr_ref& result);
    br_status mk_str_stoi(expr* a, expr_ref& result);
    br_status mk_str_ubv2s(expr* a, expr_ref& result);
    br_status mk_str_in_regexp(expr* a, expr* b, expr_ref& result);
    br_status mk_str_to_regexp(expr* a, expr_ref& result);
    br_status mk_str_le(expr* a, expr* b, expr_ref& result);
    br_status mk_str_lt(expr* a, expr* b, expr_ref& result);
    br_status mk_str_from_code(expr* a, expr_ref& result);
    br_status mk_str_to_code(expr* a, expr_ref& result);
    br_status mk_str_is_digit(expr* a, expr_ref& result);
    br_status mk_re_concat(expr* a, expr* b, expr_ref& result);
    br_status mk_re_union(expr* a, expr* b, expr_ref& result);
    br_status mk_re_inter(expr* a, expr* b, expr_ref& result);
    br_status mk_re_union0(expr* a, expr* b, expr_ref& result);
    br_status mk_re_inter0(expr* a, expr* b, expr_ref& result);
    br_status mk_re_complement(expr* a, expr_ref& result);
    br_status mk_re_star(expr* a, expr_ref& result);
    br_status mk_re_diff(expr* a, expr* b, expr_ref& result);
    br_status mk_re_plus(expr* a, expr_ref& result);
    br_status mk_re_opt(expr* a, expr_ref& result);
    br_status mk_re_power(func_decl* f, expr* a, expr_ref& result);
    br_status mk_re_loop(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
    br_status mk_re_range(expr* lo, expr* hi, expr_ref& result);
    br_status mk_re_reverse(expr* r, expr_ref& result);
    br_status mk_re_derivative(expr* ele, expr* r, expr_ref& result);

    br_status lift_ites_throttled(func_decl* f, unsigned n, expr* const* args, expr_ref& result);
    bool lift_ites_filter(func_decl* f, expr* ite);

    br_status reduce_re_eq(expr* a, expr* b, expr_ref& result);
    br_status reduce_re_is_empty(expr* r, expr_ref& result);

    bool non_overlap(expr_ref_vector const& p1, expr_ref_vector const& p2) const;
    bool non_overlap(zstring const& p1, zstring const& p2) const;
    bool rewrite_contains_pattern(expr* a, expr* b, expr_ref& result);
    bool has_fixed_length_constraint(expr* a, unsigned& len);
    /* r = ite(c1,ite(c2,to_re(s),to_re(t)),to_re(u)) ==> returns true, result = ite(c1,ite(c2,s,t),u)*/
    bool lift_str_from_to_re_ite(expr * r, expr_ref & result);
    /* same as lift_to_re_from_ite and also: r = to_re(u) ==> returns true, result = u */
    bool lift_str_from_to_re(expr * r, expr_ref & result);

    br_status mk_bool_app_helper(bool is_and, unsigned n, expr* const* args, expr_ref& result);
    br_status mk_eq_helper(expr* a, expr* b, expr_ref& result);

    bool cannot_contain_prefix(expr* a, expr* b);
    bool cannot_contain_suffix(expr* a, expr* b);
    expr_ref zero() { return expr_ref(m_autil.mk_int(0), m()); }
    expr_ref one() { return expr_ref(m_autil.mk_int(1), m()); }
    expr_ref minus_one() { return expr_ref(m_autil.mk_int(-1), m()); }

    bool is_suffix(expr* s, expr* offset, expr* len);
    bool is_prefix(expr* s, expr* offset, expr* len);
    bool sign_is_determined(expr* len, sign& s);

    bool set_empty(unsigned sz, expr* const* es, bool all, expr_ref_pair_vector& eqs);
    bool reduce_non_overlap(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool reduce_subsequence(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool reduce_by_length(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool reduce_itos(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool reduce_eq_empty(expr* l, expr* r, expr_ref& result);    
    bool min_length(expr_ref_vector const& es, unsigned& len);
    bool min_length(expr* e, unsigned& len);
    bool max_length(expr* e, rational& len);
    lbool eq_length(expr* x, expr* y);
    expr* concat_non_empty(expr_ref_vector& es);
    bool reduce_by_char(expr_ref& r, expr* ch, unsigned depth);

    bool is_string(unsigned n, expr* const* es, zstring& s) const;

    void add_next(u_map<expr*>& next, expr_ref_vector& trail, unsigned idx, expr* cond);
    bool is_sequence(expr* e, expr_ref_vector& seq);
    bool is_sequence(eautomaton& aut, expr_ref_vector& seq);
    bool get_lengths(expr* e, expr_ref_vector& lens, rational& pos);
    bool reduce_back(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs);
    bool reduce_front(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs);
    void remove_empty_and_concats(expr_ref_vector& es);
    void remove_leading(unsigned n, expr_ref_vector& es);

    class seq_util::rex& re() { return u().re; }
    class seq_util::rex const& re() const { return u().re; }
    class seq_util::str& str() { return u().str; }
    class seq_util::str const& str() const { return u().str; }

    void intersect(unsigned lo, unsigned hi, svector<std::pair<unsigned, unsigned>>& ranges);

public:
    seq_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m_util(m), m_autil(m), m_br(m), m_re2aut(m), m_op_cache(m), m_es(m), 
        m_lhs(m), m_rhs(m), m_coalesce_chars(true) {
    }
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    seq_util const& u() const { return m_util; }
    seq_util& u() { return m_util; }

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void set_solver(expr_solver* solver) { m_re2aut.set_solver(solver); }
    bool has_solver() { return m_re2aut.has_solver(); }

    bool coalesce_chars() const { return m_coalesce_chars; }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);
    br_status mk_le_core(expr* lhs, expr* rhs, expr_ref& result);
    br_status mk_bool_app(func_decl* f, unsigned n, expr* const* args, expr_ref& result);

    expr_ref mk_app(func_decl* f, expr_ref_vector const& args) { return mk_app(f, args.size(), args.data()); }
    expr_ref mk_app(func_decl* f, unsigned n, expr* const* args) { 
        expr_ref result(m());
        if (f->get_family_id() != u().get_family_id() || 
            BR_FAILED == mk_app_core(f, n, args, result))
            result = m().mk_app(f, n, args);
        return result;
    }

    /**
     * check if regular expression is of the form all ++ s ++ all ++ t + u ++ all, where, s, t, u are sequences
     */
    bool is_re_contains_pattern(expr* r, vector<expr_ref_vector>& patterns);
        
    bool reduce_eq(expr* l, expr* r, expr_ref_pair_vector& new_eqs, bool& change);

    bool reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs, bool& change);

    bool reduce_contains(expr* a, expr* b, expr_ref_vector& disj);

    expr_ref mk_length(expr* s);

    void add_seqs(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref_pair_vector& new_eqs);

    // Expose derivative and nullability check
    expr_ref is_nullable(expr* r);
    expr_ref mk_derivative(expr* ele, expr* r);

    // heuristic elimination of element from condition that comes form a derivative.
    // special case optimization for conjunctions of equalities, disequalities and ranges.
    void elim_condition(expr* elem, expr_ref& cond);
};

