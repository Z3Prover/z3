/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ssnf.h

Abstract:

    Strong star normal form (SSNF) for regular expressions.

    Bruggemann-Klein's star normal form rewrites every starred subexpression
    r* into (r_deg)*, where r_deg is epsilon-free and L((r_deg)*) = L(r*).
    A nullable star body is what makes a derivative automaton large: every
    derivative of the body is then also a derivative of the star, so the
    states of the body and of the star collapse into each other only after
    the fact.  The "strong" variant additionally drops the epsilon
    alternative of a union whose other side is already nullable.

    The transformation preserves the language of the whole expression, so the
    result can replace the input anywhere.  Subterms it has no rule for are
    returned unchanged, i.e. the normal form is partial on the boolean
    closure (complement / intersection / difference).

Author:

    Clemens Eisenhofer 2026-08-31

--*/
#pragma once

#include "ast/seq_decl_plugin.h"

class seq_ssnf {
    ast_manager&         m;
    seq_util&            m_seq;
    obj_map<expr, expr*> m_ssnf;   // r -> ssnf(r)
    obj_map<expr, expr*> m_circ;   // r -> r_deg, for r already in SSNF
    expr_ref_vector      m_pin;    // pins keys and values of both caches

    // recursion guard: deeper subterms are left unchanged
    static const unsigned max_depth = 512;

    seq_util::rex& re() const { return m_seq.re; }
    lbool nullable(expr* r) const { return re().get_info(r).nullable; }

    expr* ssnf_rec(expr* r, unsigned depth);
    expr* circ(expr* r, unsigned depth);
    expr* rebuild(expr* r, unsigned depth);

public:
    seq_ssnf(seq_util& seq) : m(seq.get_manager()), m_seq(seq), m_pin(seq.get_manager()) {}

    // Language-preserving rewrite of the regex r into strong star normal form.
    expr* operator()(expr* r) { return ssnf_rec(r, 0); }

    void reset() { m_ssnf.reset(); m_circ.reset(); m_pin.reset(); }
};
