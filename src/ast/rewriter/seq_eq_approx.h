/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_approx.h

Abstract:

    Emptiness of the intersection of two concatenations of views, and the word-equation
    check built on it.

    A view constrains one value against a derivative automaton: a membership view by the
    language of its state, a reach view by the runs from its state to its target.  Both
    sides of an equation L = R are read as a sequence of SEGMENTS, one per part, each a
    conjunction of views -- constants included, since a constant is the membership view
    of its own language, an unknown element the view of Sigma, and an unconstrained part
    the view of Sigma^*:

        L = x.a.y   =>   segments(L) = [ views(x), <to_re "a">, views(y) ]

    The two segment sequences are intersected directly, without turning any view into a
    regex: a reach language is the runs between two states and has no regex term
    (materializing one is the state elimination seq_monadic exists to avoid).  The search
    is a product of the two sides, each side a cursor of a segment index plus one
    derivative state per view of that segment:

      - a character step advances every view of both current segments at once, over the
        combinations of cofactor branches whose guards share an element;
      - an epsilon step ends the current segment on one side and starts the next, and is
        available exactly when every view of the segment is satisfied -- a membership
        view at a nullable state, a reach view at its target;
      - the intersection is non-empty iff a state where both sides have ended their last
        segment is reachable.

    A reach view is relative to the transition relation it was produced under, so the
    engine has to run in the mode its producer ran in (the constructor takes it).

    So the test is exact.  An empty intersection refutes the equation, because every
    value of a side lies in the language of its segments.  A non-empty intersection says
    nothing about the equation: two occurrences of a variable are separate segments and
    are constrained apart, so x.x = a is consistent here.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_view.h"
#include "ast/rewriter/guard_set.h"
#include "util/lbool.h"
#include "util/obj_hashtable.h"
#include "util/statistics.h"

class seq_eq_approx {

    struct statistics {
        unsigned m_checks = 0;
        unsigned m_unsupported = 0;    // a side the module cannot read as segments
        unsigned m_giveup = 0;         // the search gave up
        unsigned m_refuted = 0;
        unsigned m_states = 0;         // product states expanded
    };

public:

    typedef vector<seq::view_vector> segments;

private:

    ast_manager&        m;
    seq_rewriter&       m_rw;
    seq::transition_mode m_mode;
    statistics          m_stats;
    obj_map<expr, seq::view_vector> m_views;   // term -> the views constraining it
    expr_ref_vector     m_pin;         // keeps the map's terms, the view states and the
                                       // regexes built for constant segments alive: the
                                       // derivative caches key on them, so they have to
                                       // outlive every search that touched them
    ptr_vector<expr>    m_used;        // constrained terms the last check() consulted
    guard_set::cache    m_rp_cache;
    unsigned            m_max_states;
    unsigned            m_budget = 0;
    lbool               m_last_result = l_undef;

    seq_util&      u() const { return m_rw.u(); }
    seq_util::rex& re() const { return m_rw.u().re; }

    lbool nullable(expr* r);
    expr_ref_pair_vector const& cofactors(expr* r);

    // Charge one product state and poll the resource limit.
    bool out_of_budget();

    // Append the segment of a constant / unconstrained part, i.e. the membership view
    // of `r`, to `out`, pinning `r`.
    void add_segment(expr* r, segments& out);

    // Whether every view of the segment is satisfied at `states`, i.e. whether the
    // segment may end here.  l_undef when a nullability is undecided.
    lbool segment_done(seq::view_vector const& views, ptr_vector<expr> const& states);

public:

    seq_eq_approx(seq_rewriter& rw, unsigned max_states = 1u << 14,
                  seq::transition_mode mode = seq::transition_mode::light_antimirov_tm) :
        m(rw.m()), m_rw(rw), m_mode(mode), m_pin(rw.m()), m_rp_cache(rw.m()),
        m_max_states(max_states) {}

    void collect_statistics(::statistics& st) const;

    std::ostream& display(std::ostream& out) const;

    // Constrain the values of `t`.  The views of a term are conjunctive: add_view narrows
    // it further, set_views replaces what it carries.  A term is looked up before it is
    // decomposed as a concatenation, so `t` may be compound.
    void add_view(expr* t, seq::view const& v);
    void set_views(expr* t, seq::view_vector const& views);
    void unset_views(expr* t);
    void reset_views();
    seq::view_vector const* get_views(expr* t) const;
    unsigned num_terms() const { return m_views.size(); }

    // Read `term` as a sequence of segments, appending the constrained terms it consults
    // to used().  False when a view constrains a part over the wrong sequence sort.  The
    // segments stay valid until the views are reset.
    bool to_segments(expr* term, segments& out);

    // Emptiness of  L(V_1)...L(V_m) & L(W_1)...L(W_n).  A view holds raw pointers, so
    // segments a caller builds itself must outlive the call; the ones to_segments
    // builds are pinned by this object.
    //   l_true  = the two concatenations share a word,
    //   l_false = they share none,
    //   l_undef = gave up (state bound, resource limit, an undecidable guard or
    //             nullability, or segments over different sorts).
    lbool intersect_nonempty(segments const& lhs, segments const& rhs);

    // Decide whether the two sides of an equation share a word.  l_false refutes the
    // equation under the views installed, l_true is inconclusive, l_undef gave up.
    lbool check(expr* lhs, expr* rhs);
    lbool check(expr* eq);

    // The constrained terms whose views the last check() used.  A refutation rests on
    // these and on the constants of the equation, so a caller justifying it needs no
    // others.
    ptr_vector<expr> const& used() const { return m_used; }

    // Product states one call may expand before giving up.
    void set_max_states(unsigned n) { m_max_states = n; }
    unsigned max_states() const { return m_max_states; }

    lbool last_result() const { return m_last_result; }
};
