/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    dt2bv_proof_converter.h

Abstract:

    Transport finite-domain refutations by substituting enumeration encodings.

--*/
#pragma once

#include "ast/converters/proof_converter.h"
#include "ast/rewriter/expr_safe_replace.h"

class dt2bv_proof_converter : public proof_converter {
    ast_manager& m;
    expr_safe_replace m_substitution;
    expr_ref_vector m_sources, m_encodings;
    proof_ref_vector m_proofs;
    obj_hashtable<expr> m_assertions;

    proof_ref prove(expr* fact);

public:
    dt2bv_proof_converter(ast_manager& m);
    void insert_enum(func_decl* original, func_decl* fresh);
    void insert(proof* original, expr* translated);
    void insert_bound(expr* bound);
    proof_ref operator()(ast_manager& m, unsigned num_source, proof* const* source) override;
    proof_converter* translate(ast_translation& translator) override;
    void display(std::ostream& out) override;
};
