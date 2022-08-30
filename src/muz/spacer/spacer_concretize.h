#pragma once
/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_concretize.h

Abstract:

  Concretize a pob

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "util/obj_ref_hashtable.h"
#include "util/rational.h"

namespace spacer {

class pob_concretizer {
    ast_manager &m;
    arith_util m_arith;

    model_ref &m_model;

    const expr *m_pattern;

    expr_fast_mark2 m_var_marks;

    // Marks all constants to be split in the pattern
    void mark_pattern_vars();

    // Adds a literal to \p out (unless it is already there)
    bool push_out(expr_ref_vector &out, const expr_ref &e);
    // Determines whether \p e is a*var, for some variable in \p m_var_marks
    // Sets \p pos to sign(a)
    bool is_split_var(expr *e, expr *&var, bool &pos);
    // Splits a < or <= literal using the model
    void split_lit_le_lt(expr *lit, expr_ref_vector &out);
    // See split_lit_le_lt
    void split_lit_ge_gt(expr *lit, expr_ref_vector &out);

  public:
    pob_concretizer(ast_manager &_m, model_ref &model, const expr *pattern)
        : m(_m), m_arith(m), m_model(model), m_pattern(pattern) {}

    /// Concretize \p cube into conjunction of simpler literals
    ///
    /// Returns true on success and adds new literals to out
    /// ensures: mk_and(out) ==> cube
    bool apply(expr *cube, expr_ref_vector &out) {
        expr_ref_vector flat(m);
        flatten_and(cube, flat);
        return apply(flat, out);
    }

    /// Concretizes a vector of literals
    bool apply(const expr_ref_vector &cube, expr_ref_vector &out);

    /// Concretizes a single literal
    ///
    /// Returns true on success, new literals are added to \p out
    bool apply_lit(expr *lit, expr_ref_vector &out);
};

} // namespace spacer
