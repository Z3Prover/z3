/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    proof_converter.cpp

Abstract:

    Abstract interface for converting proofs, and basic combinators

Author:

    Leonardo (leonardo) 2011-11-14

Notes:

--*/
#include "ast/converters/proof_converter.h"
#include "ast/ast_smt2_pp.h"

class concat_proof_converter : public concat_converter<proof_converter> {
public:
    concat_proof_converter(proof_converter * pc1, proof_converter * pc2):concat_converter<proof_converter>(pc1, pc2) {}

    char const * get_name() const override { return "concat-proof-converter"; }

    proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) override {
        proof_ref tmp(m);
        tmp = this->m_c2->operator()(m, num_source, source);
        proof * new_source = tmp.get();
        return this->m_c1->operator()(m, 1, &new_source);
    }

    proof_converter * translate(ast_translation & translator) override {
        return this->translate_core<concat_proof_converter>(translator);
    }
};

proof_converter * concat(proof_converter * pc1, proof_converter * pc2) {
    if (pc1 == nullptr)
        return pc2;
    if (pc2 == nullptr)
        return pc1;
    return alloc(concat_proof_converter, pc1, pc2);
}


class proof2pc : public proof_converter {
    proof_ref m_pr;
public:
    proof2pc(ast_manager & m, proof * pr):m_pr(pr, m) {}

    proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) override {
        SASSERT(num_source == 0);
        return m_pr;
    }

    proof_converter * translate(ast_translation & translator) override {
        return alloc(proof2pc, translator.to(), translator(m_pr.get()));
    }

    void display(std::ostream & out) override {
        out << "(proof->proof-converter-wrapper\n" << mk_ismt2_pp(m_pr.get(), m_pr.get_manager()) << ")\n";
    }    
};

proof_converter * proof2proof_converter(ast_manager & m, proof * pr) {
    if (pr == nullptr)
        return nullptr;
    return alloc(proof2pc, m, pr);
}

void apply(ast_manager & m, proof_converter * pc, proof_ref & pr) {
    if (pc) {
        proof * _pr = pr.get();
        pr = (*pc)(m, 1, &_pr);
    }
}

/**
   Let pc2s be a buffer of proof converters that are wrappers for proofs.
   That is, they are functors of the form: unit -> Proof
   Then, this function applies pc1 to the proofs produced by pc2s's and store
   the resultant proof in result.
   
   pc1 and pc2s must be different from 0.
*/
proof_ref apply(ast_manager & m, proof_converter_ref & pc1, proof_converter_ref_buffer & pc2s) {
    SASSERT(pc1);
    proof_ref_buffer prs(m);
    unsigned sz = pc2s.size();
    for (unsigned i = 0; i < sz; i++) {
        proof_ref pr(m);
        SASSERT(pc2s[i]); // proof production is enabled
        pr = pc2s[i]->operator()(m, 0, nullptr);
        prs.push_back(pr);
    }
    return (*pc1)(m, sz, prs.data());
}
