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
#ifndef SEQ_REWRITER_H_
#define SEQ_REWRITER_H_

#include "ast/seq_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/ref_pair_vector.h"
#include "util/params.h"
#include "util/lbool.h"
#include "util/sign.h"
#include "math/automata/automaton.h"
#include "math/automata/symbolic_automata.h"

typedef ref_pair_vector<expr, ast_manager> expr_ref_pair_vector;

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
    static sym_expr* mk_char(expr_ref& t) { return alloc(sym_expr, t_char, t, t, t.get_manager().get_sort(t), nullptr); }
    static sym_expr* mk_char(ast_manager& m, expr* t) { expr_ref tr(t, m); return mk_char(tr); }
    static sym_expr* mk_pred(expr_ref& t, sort* s) { return alloc(sym_expr, t_pred, t, t, s, nullptr); }
    static sym_expr* mk_range(expr_ref& lo, expr_ref& hi) { return alloc(sym_expr, t_range, lo, hi, lo.get_manager().get_sort(hi), nullptr); }
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
    ~re2automaton();
    eautomaton* operator()(expr* e);
    void set_solver(expr_solver* solver);
    bool has_solver() const { return m_solver; }
    eautomaton* mk_product(eautomaton *a1, eautomaton *a2);
};

/**
   \brief Cheap rewrite rules for seq constraints
*/
class seq_rewriter {
    seq_util       m_util;
    arith_util     m_autil;
    re2automaton   m_re2aut;
    expr_ref_vector m_es, m_lhs, m_rhs;
    bool           m_coalesce_chars;

    enum length_comparison {
        shorter_c, 
        longer_c,
        same_length_c,
        unknown_c
    };

    length_comparison compare_lengths(expr_ref_vector const& as, expr_ref_vector const& bs) {
        return compare_lengths(as.size(), as.c_ptr(), bs.size(), bs.c_ptr());
    }
    length_comparison compare_lengths(unsigned sza, expr* const* as, unsigned szb, expr* const* bs);

    br_status mk_seq_unit(expr* e, expr_ref& result);
    br_status mk_seq_concat(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_length(expr* a, expr_ref& result);
    br_status mk_seq_extract(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_contains(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_at(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_nth(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_nth_i(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_index(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_last_index(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_replace(expr* a, expr* b, expr* c, expr_ref& result);
    br_status mk_seq_prefix(expr* a, expr* b, expr_ref& result);
    br_status mk_seq_suffix(expr* a, expr* b, expr_ref& result);
    br_status mk_str_units(func_decl* f, expr_ref& result);
    br_status mk_str_itos(expr* a, expr_ref& result);
    br_status mk_str_stoi(expr* a, expr_ref& result);
    br_status mk_str_in_regexp(expr* a, expr* b, expr_ref& result);
    br_status mk_str_to_regexp(expr* a, expr_ref& result);
    br_status mk_str_le(expr* a, expr* b, expr_ref& result);
    br_status mk_str_lt(expr* a, expr* b, expr_ref& result);
    br_status mk_re_concat(expr* a, expr* b, expr_ref& result);
    br_status mk_re_union(expr* a, expr* b, expr_ref& result);
    br_status mk_re_inter(expr* a, expr* b, expr_ref& result);
    br_status mk_re_complement(expr* a, expr_ref& result);
    br_status mk_re_star(expr* a, expr_ref& result);
    br_status mk_re_plus(expr* a, expr_ref& result);
    br_status mk_re_opt(expr* a, expr_ref& result);
    br_status mk_re_loop(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
    br_status mk_re_range(expr* lo, expr* hi, expr_ref& result);

    bool cannot_contain_prefix(expr* a, expr* b);
    bool cannot_contain_suffix(expr* a, expr* b);
    expr_ref zero() { return expr_ref(m_autil.mk_int(0), m()); }
    expr_ref one() { return expr_ref(m_autil.mk_int(1), m()); }
    expr_ref minus_one() { return expr_ref(m_autil.mk_int(-1), m()); }

    bool is_suffix(expr* s, expr* offset, expr* len);
    bool sign_is_determined(expr* len, sign& s);

    bool set_empty(unsigned sz, expr* const* es, bool all, expr_ref_pair_vector& eqs);
    bool reduce_subsequence(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool reduce_by_length(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool reduce_itos(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& eqs);
    bool min_length(expr_ref_vector const& es, unsigned& len);
    expr* concat_non_empty(expr_ref_vector& es);

    bool is_string(unsigned n, expr* const* es, zstring& s) const;

    void add_next(u_map<expr*>& next, expr_ref_vector& trail, unsigned idx, expr* cond);
    bool is_sequence(expr* e, expr_ref_vector& seq);
    bool is_sequence(eautomaton& aut, expr_ref_vector& seq);
    bool is_epsilon(expr* e) const;
    bool get_lengths(expr* e, expr_ref_vector& lens, rational& pos);
    bool reduce_back(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs);
    bool reduce_front(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs);
    void remove_empty_and_concats(expr_ref_vector& es);
    void remove_leading(unsigned n, expr_ref_vector& es);

public:    
    seq_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m_util(m), m_autil(m), m_re2aut(m), m_es(m), m_lhs(m), m_rhs(m), m_coalesce_chars(true) {
    }
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);

    void set_solver(expr_solver* solver) { m_re2aut.set_solver(solver); }
    bool has_solver() { return m_re2aut.has_solver(); }


    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);

    bool reduce_eq(expr* l, expr* r, expr_ref_pair_vector& new_eqs, bool& change);

    bool reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_pair_vector& new_eqs, bool& change);

    bool reduce_contains(expr* a, expr* b, expr_ref_vector& disj);

    void add_seqs(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref_pair_vector& new_eqs);


};

#endif
