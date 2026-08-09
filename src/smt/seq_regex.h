/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    seq_regex.h

Abstract:

    Solver for regexes 

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-22

--*/
#pragma once

#include "util/scoped_vector.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_monadic.h"
#include "ast/rewriter/seq_regex_live.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "smt/smt_context.h"

/*
    *** Tracing and debugging in this module and related modules ***

    Tracing and debugging for the regex solver are split across several
    command-line flags.

        TRACING

        -tr:seq_regex and -tr:seq_regex_brief
        These are the main tags to trace what the regex solver is doing.
        They mostly trace the same things, except that seq_regex_brief
        avoids printing out expressions and tries to abbreviate the output
        as much as possible. seq_regex_brief shows the following output:
            Top-level propagations:
                PIR:      Propagating an in_re constraint
                PE/PNE:   Propagating an empty/non-empty constraint
                PEQ/PNEQ: Propagating a not-equal constraint
                PA:       Propagating an accept constraint
            In tracing, arguments are generally put in parentheses.
            To achieve abbreviated output, expressions are traced in one of two
            ways:
                id243 (expr ID):  the regex or expression with id 243
                3     (state ID): the regex with state ID 3
            When a regex is newly assigned to a state ID, we print this:
                new(id606)=4
            Of these, PA is the most important, and traces as follows:
                PA(x@i,r): propagate accept for string x at index i, regex r.
                (empty), (dead), (blocked), (unfold): info about whether this
                    PA was cut off early, or unfolded into the derivatives
                    (next states)
                d(r1)=r2: r2 is the derivative of r1
                n(r1)=b:  b = whether r1 is nullable or not

        -tr:seq_regex_verbose
        Used for some more frequent tracing (in the style of seq_regex,
        not in the style of seq_regex_brief)

        -tr:seq and -tr:seq_verbose
        These are the underlying sequence theory tracing, often used by
        the rewriter.

        DEBUGGING

        -dbg:seq_regex
        Debugging that checks invariants. Currently, checks that derivative
        normal form is correctly preserved in the rewriter.

*/

namespace smt {

    class theory_seq;

    class seq_regex {
        // Data about a constraint of the form (str.in_re s R)
        struct s_in_re {
            literal m_lit;
            expr*   m_s;
            expr*   m_re;
            bool    m_active;
        s_in_re(literal l, expr* s, expr* r):
            m_lit(l), m_s(s), m_re(r), m_active(true) {}
        };

        theory_seq&                      th;
        context&                         ctx;
        ast_manager&                     m;
        vector<s_in_re>                  m_s_in_re;

        struct monadic_membership {
            literal  m_lit;
            expr_ref m_s;            // original membership term (used for the legacy fallback)
            expr_ref m_re;
            expr_ref m_s_expanded;   // term canonized through theory_seq's equalities; this is
                                     // what the monadic solver decides so that a variable defined
                                     // as a concatenation is seen with its structure, not atomically
            void*    m_dep;          // theory_seq::dependency* (as void*) for the equalities used to
                                     // expand m_s -> m_s_expanded; folded into an unsat core

            monadic_membership(ast_manager& m, literal lit, expr* s, expr* re, expr* s_expanded, void* dep) :
                m_lit(lit), m_s(s, m), m_re(re, m), m_s_expanded(s_expanded, m), m_dep(dep) {}
        };

        struct monadic_assumption {
            unsigned m_generation;
            enode*   m_var;
            enode*   m_witness;
        };

        // A length-bound constraint fed to the monadic solver as an extra length regex.
        // Recorded so the justifying arithmetic literal(s) can be materialized if the
        // bound participates in an unsat core.  m_len is the length term (str.len s).
        struct bound_constraint {
            enum kind_t { LO, HI, LEN };
            expr_ref m_len;
            kind_t   m_kind;
            unsigned m_value;
            bound_constraint(ast_manager& m, kind_t k, expr* len, unsigned v):
                m_len(len, m), m_kind(k), m_value(v) {}
        };

        // A candidate length bound (for term m_term, with length term m_len) that MAY be
        // enforced on the monadic solver.  final_check adds these lazily: only bounds that
        // the current monadic model actually violates are turned into length regexes via
        // record_bound.  This avoids eagerly loading loop regexes that the model already
        // respects.
        struct candidate_bound {
            expr_ref m_term;
            expr_ref m_len;
            bound_constraint::kind_t m_kind;
            unsigned m_value;
            candidate_bound(ast_manager& m, expr* term, expr* len, bound_constraint::kind_t k, unsigned v):
                m_term(term, m), m_len(len, m), m_kind(k), m_value(v) {}
        };

        seq_monadic                       m_monadic;
        vector<monadic_membership>         m_monadic_memberships;
        svector<monadic_assumption>        m_monadic_assumptions;
        vector<bound_constraint>           m_monadic_bounds;
        unsigned                          m_monadic_generation = 0;
        unsigned                          m_monadic_assumption_generation = UINT_MAX;
        unsigned                          m_monadic_fallback_generation = UINT_MAX;

        seq::live_states               m_live_states;
        /* map from uninterpreted regex constants to assigned regex expressions by EQ */
        // expr_map                       m_const_to_expr;

        // Printing expressions for seq_regex_brief
        std::string state_str(expr* e);
        std::string expr_id_str(expr* e);

        /*
            Solvers and utilities
        */
        seq_util& u();
        class seq_util::rex& re();
        class seq_util::str& str();
        seq_rewriter& seq_rw();
        seq::skolem& sk();
        arith_util& a();

        bool is_string_equality(literal lit);

        // Get a regex which overapproximates a given string
        expr_ref get_overapprox_regex(expr* s);

        void rewrite(expr_ref& e);

        bool coallesce_in_re(literal lit);

        bool block_unfolding(literal lit, unsigned i);

        bool unfold_prefix(literal lit, expr *s, expr *r);

        bool unfold_complement(literal lit, expr *s, expr *r);

        bool factor_membership(literal lit, expr *s, expr *r);

        bool factor_ite(literal lit, expr *s, expr *r);

        expr_ref mk_first(expr* r, expr* n);

        bool is_member(expr* r, expr* u);

        expr_ref symmetric_diff(expr* r1, expr* r2);

        expr_ref is_nullable_wrapper(expr* r);
        expr_ref mk_derivative_wrapper(expr* hd, expr* r);

        // Various support for unfolding derivative expressions that are
        // returned by derivative_wrapper
        expr_ref mk_deriv_accept(expr* s, unsigned i, expr* r);
        void get_derivative_targets(expr* r, expr_ref_vector& targets);

        // Decide emptiness of a ground regex by antimirov-mode NFA
        // reachability: explore derivative target states, short-circuiting to
        // "non-empty" on the first reachable nullable or classical state.
        // Returns l_true (empty), l_false (non-empty), l_undef (gave up).
        lbool re_is_empty(expr* r);

        /* 
           Pretty print the regex of the state id to the out stream, 
           seq_regex_ptr must be a pointer to seq_regex and the 
           id must be a valid state id or else nothing is printed. 
        */
        bool block_if_empty(expr* r, literal lit);
        void add_monadic_membership(literal lit, expr* s, expr* r);
        // Expand a term through theory_seq's solution map, but substitute a sub-term only
        // when the substitution stays monadic-decidable.  In particular a free variable is
        // kept atomic even after theory_seq fixes its length and represents it as a
        // concatenation of seq.unit(nth v i) skolems (which the monadic solver cannot
        // decide).  This exposes a term's defining word-equation structure (x = a ++ v ++ b)
        // without the length representation that would otherwise force a bail.  Equalities
        // used are accumulated into `deps` (a theory_seq::dependency*).
        expr_ref expand_shallow(expr* e, void*& deps, unsigned depth);
        // Choose the term the monadic solver decides for membership term s: full
        // canonization when decidable, else a shallow expansion (see expand_shallow) that
        // keeps length-only variables atomic, else s itself.  `dep` receives the equalities
        // used (a theory_seq::dependency* held as void*).
        expr_ref compute_expansion(expr* s, void*& dep);
        // Re-canonize each monadic membership term through theory_seq's current equalities
        // and, when the expansion changed, re-point the monadic solver at the expanded term.
        // Called at final_check time because the solution map is only populated during
        // solving (it is empty when propagate_in_re first registers the membership).
        void refresh_expansions();
        // Compute the candidate arithmetic length bounds of each monadic membership term
        // -- and, by decomposing the term into a concatenation of string constants and
        // variables, of each variable occurring in it.  These are NOT added to the monadic
        // solver; final_check enforces (via record_bound) only the ones a proposed model
        // violates.
        void collect_candidate_bounds(vector<candidate_bound>& out);
        // Length of term t under the monadic solver's current model (variables replaced by
        // their witnesses).  Returns false if some variable/atom is unassigned or the shape
        // is unsupported, in which case the length cannot be evaluated.
        bool model_len(expr* t, unsigned& len);
        // True if the current monadic model satisfies candidate bound cb (or the bound
        // cannot be evaluated against the model -- length regexes only prune, so an
        // unevaluable bound is left to the arithmetic solver).
        bool model_satisfies_bound(candidate_bound const& cb);
        // Collect the distinct sequence variables of a term viewed as a concatenation of
        // string constants and variables (mirrors seq_monadic's own term decomposition).
        void collect_vars(expr* s, ptr_vector<expr>& vars);
        void record_bound(expr* s, expr* len, bound_constraint::kind_t k, unsigned v);
        // Encode a monadic membership index / bounds-constraint index as the void*
        // dependency handed to the monadic solver.  seq_monadic OMITS null dependencies
        // from its unsat core, so the encoding must never produce a null pointer (in
        // particular 2*idx would map membership index 0 to null and silently drop it,
        // yielding an empty -- i.e. spurious global -- conflict).  We therefore use
        // 2*(idx+1) for memberships (even, >= 2) -- from which add_core_literal recovers
        // both the in_re literal and the canonization dependency -- and 2*idx+1 for bounds
        // constraints (odd, >= 1).
        static void* dep_of_membership(unsigned idx) {
            return reinterpret_cast<void*>(static_cast<size_t>(2 * (idx + 1)));
        }
        static void* dep_of_bound(unsigned idx) {
            return reinterpret_cast<void*>(static_cast<size_t>(2 * idx + 1));
        }
        // Decode a dependency returned by m_monadic.core() into conflict literal(s), also
        // accumulating (into deps, a theory_seq::dependency* held as void*) the equalities
        // used to canonize any participating membership term.
        void add_core_literal(void* dep, literal_vector& lits, void*& deps);
        // Whether every literal is currently assigned true, i.e. whether the negated
        // clause is a legitimate theory conflict.
        bool all_true(literal_vector const& lits) const;
        void propagate_accept_legacy(literal lit, expr* s, expr* r);
        void propagate_length_residue(literal lit, expr* s, expr* r);
        void enable_legacy_fallback();

    public:

        seq_regex(theory_seq& th);

        void push_scope() {}
        void pop_scope(unsigned num_scopes) {}
        bool can_propagate() const { return false; }
        bool propagate() const { return false; }
        final_check_status final_check();
        void collect_statistics(::statistics& st) const { m_monadic.collect_statistics(st); }

        void propagate_in_re(literal lit);

        // (accept s i r) means 
        // the suffix of s after the first i characters is a member of r
        void propagate_accept(literal lit);

        void propagate_eq(expr* r1, expr* r2);

        void propagate_ne(expr* r1, expr* r2);        

        void propagate_is_empty(literal lit);

        void propagate_is_non_empty(literal lit);
        
    };

}
