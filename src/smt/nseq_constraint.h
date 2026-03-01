/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    nseq_constraint.h

Abstract:

    Constraint types for the Nielsen-based string theory solver.
    Defines word equations, disequalities, regex memberships,
    and string predicate constraints with dependency tracking.

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "util/scoped_vector.h"
#include "util/dependency.h"
#include "smt/smt_enode.h"

namespace smt {

    // Dependency tracking for conflict explanations.
    // Each assumption is either an enode equality or a literal.
    struct nseq_assumption {
        enode* n1;
        enode* n2;
        literal lit;
        nseq_assumption(enode* n1, enode* n2) : n1(n1), n2(n2), lit(null_literal) {}
        nseq_assumption(literal lit) : n1(nullptr), n2(nullptr), lit(lit) {}
    };

    typedef scoped_dependency_manager<nseq_assumption> nseq_dep_manager;
    typedef nseq_dep_manager::dependency nseq_dependency;

    // A word equation: lhs_1 · lhs_2 · ... = rhs_1 · rhs_2 · ...
    // Each side is a concatenation of string expressions (variables, constants, units).
    class nseq_eq {
        unsigned          m_id;
        expr_ref_vector   m_lhs;
        expr_ref_vector   m_rhs;
        nseq_dependency*  m_dep;
    public:
        nseq_eq(unsigned id, expr_ref_vector& lhs, expr_ref_vector& rhs, nseq_dependency* dep)
            : m_id(id), m_lhs(lhs), m_rhs(rhs), m_dep(dep) {}

        unsigned id() const { return m_id; }
        expr_ref_vector const& lhs() const { return m_lhs; }
        expr_ref_vector const& rhs() const { return m_rhs; }
        nseq_dependency* dep() const { return m_dep; }
    };

    // A disequality constraint: lhs != rhs
    // with decomposed sub-equations and justification literals.
    class nseq_ne {
        eq_ref                   m_eq;
        eq_refs                  m_eqs;
        literal_vector           m_lits;
        nseq_dependency*         m_dep;
    public:
        nseq_ne(expr_ref const& l, expr_ref const& r, nseq_dependency* dep)
            : m_eq(l, r), m_dep(dep) {
            m_eqs.push_back(eq_ref(l, r));
        }

        expr_ref const& l() const { return m_eq.left; }
        expr_ref const& r() const { return m_eq.right; }
        eq_refs const& eqs() const { return m_eqs; }
        literal_vector const& lits() const { return m_lits; }
        nseq_dependency* dep() const { return m_dep; }
    };

    // A regex membership constraint: str.in_re(s, r)
    // Tracks the string expression, regex, and sign.
    class nseq_mem {
        expr_ref          m_str;
        expr_ref          m_regex;
        bool              m_sign;     // true = in_re, false = not in_re
        nseq_dependency*  m_dep;
    public:
        nseq_mem(expr_ref const& s, expr_ref const& r, bool sign, nseq_dependency* dep)
            : m_str(s), m_regex(r), m_sign(sign), m_dep(dep) {}

        expr* str() const { return m_str; }
        expr* regex() const { return m_regex; }
        bool sign() const { return m_sign; }
        nseq_dependency* dep() const { return m_dep; }
    };

    // String predicate constraints: contains, prefix, suffix
    enum nseq_pred_kind { NSEQ_CONTAINS, NSEQ_PREFIX, NSEQ_SUFFIX };

    class nseq_pred {
        nseq_pred_kind    m_kind;
        expr_ref          m_arg1;     // the haystack or the full string
        expr_ref          m_arg2;     // the needle or the prefix/suffix
        bool              m_sign;     // true = positive, false = negated
        nseq_dependency*  m_dep;
    public:
        nseq_pred(nseq_pred_kind kind, expr_ref const& a1, expr_ref const& a2, bool sign, nseq_dependency* dep)
            : m_kind(kind), m_arg1(a1), m_arg2(a2), m_sign(sign), m_dep(dep) {}

        nseq_pred_kind kind() const { return m_kind; }
        expr* arg1() const { return m_arg1; }
        expr* arg2() const { return m_arg2; }
        bool sign() const { return m_sign; }
        nseq_dependency* dep() const { return m_dep; }
    };
}
