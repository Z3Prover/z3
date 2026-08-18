/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_approx.h

Abstract:

    Regular over-approximation of a word equation.

    Both sides of L = R are lifted to regexes: constants map to themselves, any other
    part to its image under a mapping h, or to Sigma^* when h does not mention it.

        L = x.a.y   =>   h(L) = h(x) . (str.to_re "a") . h(y)

    The equation is then tested by intersecting the two languages, which is decided by
    seq::regex_witness.  An empty intersection refutes the equation, because every
    value of a side lies in the language of its image.  A non-empty intersection says
    nothing: occurrences of a variable are abstracted apart, so x.x = a is consistent
    here.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_regex_witness.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/statistics.h"

class seq_eq_approx {

    struct statistics {
        unsigned m_checks = 0;
        unsigned m_unsupported = 0;    // a side the module cannot lift to a regex
        unsigned m_giveup = 0;         // the emptiness search gave up
    };

    ast_manager&        m;
    seq_rewriter&       m_rw;
    th_rewriter         m_thrw;        // normalizes the images
    seq::regex_witness  m_search;
    seq::transition_mode m_mode;
    statistics          m_stats;
    obj_map<expr, expr*> m_h;          // term -> regex
    expr_ref_vector     m_h_pin;
    expr_ref            m_lhs_image;
    expr_ref            m_rhs_image;
    lbool               m_last_result = l_undef;

    seq_util&      u() const { return m_rw.u(); }
    seq_util::rex& re() const { return m_rw.u().re; }

    // Append the regexes over-approximating `t` to `parts`.  False when h maps a part
    // to a regex over the wrong sequence sort.
    bool abstract_rec(expr* t, expr_ref_vector& parts, sort* re_sort);

public:

    seq_eq_approx(seq_rewriter& rw,
                  seq::transition_mode mode = seq::transition_mode::brzozowski_tm,
                  unsigned max_states = 1u << 14) :
        m(rw.m()), m_rw(rw), m_thrw(rw.m()), m_search(rw, mode, max_states), m_mode(mode),
        m_h_pin(rw.m()), m_lhs_image(rw.m()), m_rhs_image(rw.m()) {}

    void collect_statistics(::statistics& st) const;

    std::ostream& display(std::ostream& out) const;

    seq::transition_mode mode() const { return m_mode; }

    // Constrain the values of `t` to L(regex), overwriting a previous entry.  h is
    // consulted before a concatenation is decomposed, so `t` may be compound.
    void set_regex(expr* t, expr* regex);
    void unset_regex(expr* t);
    void reset_regexes();
    expr* get_regex(expr* t) const;
    unsigned num_regexes() const { return m_h.size(); }

    // Decide whether the images of the two sides share a word.  l_false refutes the
    // equation under h, l_true is inconclusive, l_undef gave up (unsupported sorts, or
    // the emptiness search hit its state bound / an undecidable guard).
    lbool check(expr* lhs, expr* rhs);
    lbool check(expr* eq);

    // The regex over-approximating `term`.  False when h maps a part of `term` at the
    // wrong sort.
    bool abstract(expr* term, expr_ref& result);

    expr* lhs_image() const { return m_lhs_image; }
    expr* rhs_image() const { return m_rhs_image; }

    // Derivative states the emptiness search may explore before giving up.
    void set_max_states(unsigned n) { m_search.set_max_states(n); }
    unsigned max_states() const { return m_search.max_states(); }

    lbool last_result() const { return m_last_result; }
};
