/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_witness.h

Abstract:

    Self-contained extraction of a non-emptiness witness for a regular
    expression: a term w such that (str.in_re w r) holds, or, more generally,
    a term over any sequence-of-element sort such that w is in the language
    of r.

    The search is a Brzozowski/Antimirov derivative reachability search: from
    r, follow derivative cofactors (guard, target) pairs -- the same symbolic
    transition relation seq_derive.cpp computes for regex rewriting -- until a
    nullable state is reached.  Cofactor guard satisfiability, and the
    concrete element used to build the witness, are decided by the general
    purpose guard_set cofactor algebra: the exact range_predicate over the
    character sort, and a sound and complete candidate-basis evaluation over
    any other element sort.  This mirrors, in a single-state specialization,
    the general purpose cofactor / guard_set machinery seq_monadic.cpp uses to
    find non-emptiness witnesses for monadic decomposition components
    (seq_monadic::product_nonempty), but is otherwise independent of it.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_derive.h"
#include "ast/rewriter/guard_set.h"
#include "util/zstring.h"
#include "util/lbool.h"

namespace seq {

    class regex_witness {
        ast_manager&      m;
        seq_rewriter&     m_rw;
        transition_mode   m_mode;
        unsigned          m_max_states;
        expr_ref_vector   m_pin;         // pins witness elements / states referenced by the result
        guard_set::cache  m_rp_cache;    // guard -> range predicate, reused across searches

        seq_util& u() const { return m_rw.u(); }
        seq_util::rex& re() const { return m_rw.u().re; }

        // Nullability of a derivative state: the regex info cache first (structural,
        // never evicted), falling back to the symbolic nullability formula.
        lbool nullable(expr* r) const;

        // Symbolic transition cofactors of `r` in the configured derivative mode.
        expr_ref_pair_vector const& cofactors(expr* r) const;

        // Derivative reachability search from `r`.  When `witness` is non-null it is
        // set to a member of the language on l_true; otherwise no word is built.
        lbool search(expr* r, expr_ref* witness);

        // Decode a witness term built by get_witness (a concatenation of seq.unit
        // elements, seq.empty, or a string literal) into a zstring. False if some part
        // of the term is not a constant character.
        static bool decode_string(seq_util& u, expr* e, zstring& out);

    public:
        // `mode` selects the derivative cofactor flavor (Brzozowski vs. light
        // Antimirov), and `max_states` bounds the number of derivative states
        // explored before giving up (l_undef).
        regex_witness(seq_rewriter& rw,
                      transition_mode mode = transition_mode::light_antimirov_tm,
                      unsigned max_states = 1u << 14);

        void set_max_states(unsigned n) { m_max_states = n; }
        unsigned max_states() const { return m_max_states; }

        // Find a witness term `witness`, over the sequence sort of `r`, such that
        // `witness` is a member of `r`.  The witness is a concatenation of
        // (seq.unit element) terms, or (as . mk_empty) when r accepts the empty
        // sequence.
        //   l_true  = r is non-empty; `witness` is set to a member.
        //   l_false = r is empty.
        //   l_undef = gave up (state budget exhausted, resource limit, or a
        //             cofactor guard outside the supported grammar), or `r` is
        //             not a regular expression term.
        lbool get_witness(expr* r, expr_ref& witness);

        // Specialization for regular expressions over the string sort: same search,
        // decoded into a zstring.
        //   l_true  = r is non-empty; `s` is set to a member string.
        //   l_false = r is empty.
        //   l_undef = gave up, or `r` does not range over strings.
        lbool get_witness(expr* r, zstring& s);

        // Non-emptiness of L(r), the same search without building a member.
        //   l_true = non-empty, l_false = empty, l_undef = gave up.
        lbool nonempty(expr* r);

        // Non-emptiness of L(r1) & L(r2).  It is decided on the derivatives of
        // re.inter, which conjoins the cofactor guards of the two regexes as it goes.
        lbool intersect_nonempty(expr* r1, expr* r2);
    };

}
