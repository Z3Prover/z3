/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_charclass.h

Abstract:

    Collapse  A & ~C  into a character class when A is one.

    seq_range_collapse canonicalizes boolean combinations of character-class
    regexes into a single range predicate, but deliberately excludes
    re.complement: it is a SEQUENCE-level complement, so ~(str.to_re "a")
    contains the empty word and every word of length two or more, and reading
    it as a character class on its own would be wrong.

    Under an intersection with a character class the reading IS correct: a
    character class only accepts words of length one, so

        L(A) & complement(L(C))  =  L(A) \ L(C)   whenever  L(A) subseteq Sigma

    and the right-hand side is a character class again.  When C has no word of
    length one at all (its length bounds prove it) the complement removes
    nothing and the result is just A.

    This matters because  (re.inter re.allchar (re.comp (str.to_re "a")))  --
    "any character except a" -- is the standard way to write a negated
    character class, and it otherwise stays a four-node sequence-level boolean
    term that also makes the whole regex non-classical.

Author:

    Clemens Eisenhofer 2026-08-31

--*/
#pragma once

#include "ast/rewriter/seq_range_predicate.h"
#include "ast/seq_decl_plugin.h"

class seq_charclass {
    ast_manager&         m;
    seq_util&            m_seq;
    obj_map<expr, expr*> m_cache;
    expr_ref_vector      m_pin;

    // recursion guard: deeper subterms are left unchanged
    static const unsigned max_depth = 512;

    seq_util::rex& re() const { return m_seq.re; }

    // True when L(r) is a set of one-character words, with out its character
    // set.  Extends seq::regex_to_range_predicate by the one-character
    // str.to_re leaf, which that fragment does not recognize.
    bool charset(expr* r, seq::range_predicate& out, unsigned depth) const;

    // a & ~c, when a is a character class
    bool collapse(expr* a, expr* c, expr_ref& out) const;

    expr* rec(expr* r, unsigned depth);

public:
    seq_charclass(seq_util& seq) : m(seq.get_manager()), m_seq(seq), m_pin(seq.get_manager()) {}

    // Language-preserving rewrite of r, collapsing every negated character
    // class it contains.
    expr* operator()(expr* r) { return rec(r, 0); }

    void reset() { m_cache.reset(); m_pin.reset(); }
};
