/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    rw_rule.h

Abstract:

    Abstract machine for pattern-based term rewriting.

    A rewriting rule lhs -> rhs is represented by storing the lhs as a
    pattern in which VAR(i) nodes act as wildcards, and the rhs as a
    template where the same VAR(i) nodes are substituted with the
    matched subterms.  For example, the arithmetic simplification

        0 + x  ->  x

    is encoded with lhs = (+ 0_int VAR(0)) and rhs = VAR(0).

    The abstract machine rw_table stores rules indexed by the head
    function symbol of each lhs pattern and provides a reduce_app hook
    used by the evaluator rw_evaluator.  The evaluator derives from
    rewriter_tpl so that it traverses terms bottom-up, applying the
    first matching rule at every node.

    populate_rules() seeds the machine with a representative set of
    arithmetic, Boolean, and ITE simplifications.

Author:

    Copilot 2026

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/obj_hashtable.h"
#include "util/scoped_ptr_vector.h"

// ---------------------------------------------------------------------------
// rw_rule: one rewriting rule  lhs -> rhs.
// VAR(i) nodes for i < m_num_vars act as pattern wildcards.
// ---------------------------------------------------------------------------
struct rw_rule {
    unsigned  m_num_vars;
    expr_ref  m_lhs;
    expr_ref  m_rhs;

    rw_rule(ast_manager & m, unsigned num_vars, expr * lhs, expr * rhs)
        : m_num_vars(num_vars), m_lhs(lhs, m), m_rhs(rhs, m) {}
};

// ---------------------------------------------------------------------------
// rw_table: abstract machine.
// Rules are indexed by the head func_decl of the lhs pattern.
// The class also satisfies the Cfg concept expected by rewriter_tpl.
// ---------------------------------------------------------------------------
class rw_table : public default_rewriter_cfg {
    ast_manager &                        m;
    scoped_ptr_vector<rw_rule>           m_rules;
    obj_map<func_decl, unsigned_vector>  m_index;

    // Recursive structural matcher.
    // VAR(i) in the pattern is unified with the corresponding subterm of term,
    // extending bindings[i].  Returns false on conflict or mismatch.
    bool match(expr * pattern, expr * term, ptr_vector<expr> & bindings);

public:
    explicit rw_table(ast_manager & m) : m(m) {}

    // Add a rewriting rule  lhs -> rhs.
    // lhs must be an application; VAR(i) for i < num_vars may appear inside
    // lhs and rhs as pattern variables / replacement slots.
    void add_rule(unsigned num_vars, expr * lhs, expr * rhs);

    // Try to rewrite the application (f args[0] ... args[num-1]).
    // Returns BR_DONE with result set on success, BR_FAILED otherwise.
    br_status apply(func_decl * f, unsigned num, expr * const * args, expr_ref & result);

    // Cfg hook called by rewriter_tpl for every application node.
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args,
                         expr_ref & result, proof_ref & /*result_pr*/) {
        return apply(f, num, args, result);
    }

    // Seed the machine with a representative set of simplification rules
    // covering arithmetic (Int and Real), Boolean connectives, and ITE.
    void populate_rules();

    ast_manager & get_manager() { return m; }
};

// ---------------------------------------------------------------------------
// rw_evaluator: full-term bottom-up evaluator built on top of rw_table.
// ---------------------------------------------------------------------------
class rw_evaluator : public rewriter_tpl<rw_table> {
    rw_table m_table;
public:
    explicit rw_evaluator(ast_manager & m)
        : rewriter_tpl<rw_table>(m, false, m_table)
        , m_table(m) {
        m_table.populate_rules();
    }

    using rewriter_tpl<rw_table>::operator();
};
