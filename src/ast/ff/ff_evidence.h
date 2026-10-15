/*++
Copyright (c) 2026 Romain Soulat

    Evidence at the frontend-independent finite-field boundary. The proof is
    bound to the original signed premises; no normalized fact is an assumption.
--*/
#pragma once
#include "ast/ast.h"
#include "util/params.h"
#include "math/ff/ff_polynomial.h"
#include <memory>

namespace ff {
    // Bounded exhaustive propositional checking for native proof obligations.
    // Field equalities are opaque atoms; no field reasoning is trusted here.
    bool check_boolean_tautology(ast_manager &m, expr *formula);
    // Exact bounded ring normalization, optionally modulo a nonzero scalar
    // on both sides of an equality of field equations. No solver is called.
    bool check_polynomial_rewrite(ast_manager& m, expr* formula);
    // One original-premise encoding, engine and recording session. Frontends
    // consume its model or refutation; no separate proof-first solve is run.
    class recorded_problem {
        struct imp;
        std::unique_ptr<imp> m_imp;
    public:
        recorded_problem(ast_manager &m, sort *field, engine &algebra,
                         expr_ref_vector const &premises);
        ~recorded_problem();
        lbool check();
        app *evidence() const;
        rational value(expr *term);
    };

    // Record native polynomial operations, including wire substitution, on a
    // definitional encoding of the original AST DAG. A null result is
    // inconclusive; it must never authorize an unproved conflict.
    app_ref record_refutation(ast_manager &m, expr_ref_vector const &premises, params_ref const &params);
    // Replay only the supplied PAC DAG; do not invoke a solver or reconstruct
    // missing evidence. The premises and all extension equations are rebound.
    bool check_refutation(ast_manager &m, app *evidence);
    expr_ref_vector refutation_clause(ast_manager &m, app *evidence);
    // Native proof wrapper owns its PAC DAG as an AST declaration parameter.
    proof_ref mk_refutation_lemma(ast_manager &m, expr *fact, app *evidence);
    bool check_refutation_lemma(ast_manager &m, proof *lemma);
}  // namespace ff
