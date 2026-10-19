/*++
Copyright (c) 2026 Microsoft Corporation

Abstract:
    Native, replayable proofs for LP evidence.
--*/
#pragma once

#include "ast/ast.h"
#include "math/lp/evidence.h"

namespace lp {
    class evidence_proof_checker {
        class imp;
        std::unique_ptr<imp> m_imp;
    public:
        explicit evidence_proof_checker(ast_manager& m);
        ~evidence_proof_checker();
        bool check(proof* p);
    };

    expr_ref evidence_fact(ast_manager& m, evidence_manager::fact const& fact,
                           expr_ref_vector const& variables);

    // Bindings use stable evidence variable indices, not recycled LP columns.
    // Inputs are indexed by proof step. Null inputs must be tautologies or
    // hypotheses discharged before the root; otherwise export returns null.
    proof_ref mk_evidence_proof(ast_manager& m,
                               evidence_manager::proof_expression const& evidence,
                               expr_ref_vector const& variables,
                               proof_ref_vector const& inputs);

    // Match native premises by their formulas; input indices may have been recycled.
    bool bind_evidence_inputs(ast_manager& m,
                              evidence_manager::proof_expression const& evidence,
                              expr_ref_vector const& variables,
                              proof_ref_vector const& premises,
                              proof_ref_vector& inputs);

    bool is_evidence_proof(proof const* p);
    bool check_evidence_proof(ast_manager& m, proof* p);
}
