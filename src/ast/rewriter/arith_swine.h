/*++
Copyright (c) 2026 Microsoft Corporation

Integer exponentiation refinements from Frohn and Giesl,
"Satisfiability Modulo Exponential Integer Arithmetic", arXiv:2402.01501.
--*/
#pragma once

#include <functional>
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/lbool.h"
#include "util/statistics.h"

class arith_swine {
public:
    struct power {
        expr* term;
        expr* base;
        expr* exponent;
        rational x, y, value;
    };
    using value_fn = std::function<bool(expr*, rational&)>;

private:
    ast_manager& m;
    arith_util a;
    th_rewriter m_rw;
    struct point { rational x, y; };
    vector<point> m_points;
    unsigned m_lemmas[6] = {};
    expr_ref m_phase;
    rational m_bound{1};
    bool m_bounded = true;
    unsigned m_phases = 0;

    expr_ref num(rational const& n);
    bool add(unsigned kind, expr* lemma, expr_ref_vector& lemmas);
    bool compute_power(rational const& x, rational const& y, rational& result);
    void symmetry(vector<power> const& powers, value_fn const& value, expr_ref_vector& lemmas);
    void monotonicity(vector<power> const& powers, expr_ref_vector& lemmas);
    void bounding(vector<power> const& powers, expr_ref_vector& lemmas);
    void prime(vector<power> const& powers, expr_ref_vector& lemmas);
    void induction(vector<power> const& powers, expr_ref_vector& lemmas);
    void interpolation(vector<power> const& powers, expr_ref_vector& lemmas);
    expr_ref interpolant(expr* x, expr* y, point const& lo, point const& hi,
                         rational& denominator, bool& success);

public:
    explicit arith_swine(ast_manager& m): m(m), a(m), m_rw(m), m_phase(m) {}
    void add_assumptions(ptr_vector<expr> const& terms, expr_ref_vector& assumptions, expr_ref_vector& lemmas);
    bool should_research(expr_ref_vector const& core);
    lbool check_model(vector<power> const& powers);
    lbool check(ptr_vector<expr> const& terms, value_fn const& value, expr_ref_vector& lemmas);
    lbool check(vector<power> const& powers, value_fn const& value, expr_ref_vector& lemmas);
    void reset();
    void collect_statistics(::statistics& st) const;
};
