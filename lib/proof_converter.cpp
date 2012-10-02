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
#include"proof_converter.h"
#include"ast_smt2_pp.h"

class concat_proof_converter : public concat_converter<proof_converter> {
public:
    concat_proof_converter(proof_converter * pc1, proof_converter * pc2):concat_converter<proof_converter>(pc1, pc2) {}

    virtual char const * get_name() const { return "concat-proof-converter"; }

    virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
        proof_ref tmp(m);
        this->m_c2->operator()(m, num_source, source, tmp);
        proof * new_source = tmp.get();
        this->m_c1->operator()(m, 1, &new_source, result);
    }

    virtual proof_converter * translate(ast_translation & translator) {
        return this->translate_core<concat_proof_converter>(translator);
    }
};

proof_converter * concat(proof_converter * pc1, proof_converter * pc2) {
    if (pc1 == 0)
        return pc2;
    if (pc2 == 0)
        return pc1;
    return alloc(concat_proof_converter, pc1, pc2);
}

class concat_star_proof_converter : public concat_star_converter<proof_converter> {
public:
    concat_star_proof_converter(proof_converter * pc1, unsigned num, proof_converter * const * pc2s, unsigned * szs):
        concat_star_converter<proof_converter>(pc1, num, pc2s, szs) {
    }

    virtual char const * get_name() const { return "concat-star-proof-converter"; }

    virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
        unsigned num = this->m_szs.size();
#ifdef Z3DEBUG
        unsigned sum = 0;
        for (unsigned i = 0; i < num; i++) {
            sum += this->m_szs[i];
        }
        SASSERT(sum == num_source);
#endif
        proof_ref_buffer tmp_prs(m);
        for (unsigned i = 0; i < num; i++) {
            unsigned sz = m_szs[i];
            proof_converter * c2 = m_c2s[i];
            proof_ref pr(m);
            if (c2) {
                (*c2)(m, sz, source, pr);
            }
            else {
                SASSERT(sz == 1);
                pr = *source;
            }
            source += sz;
            tmp_prs.push_back(pr.get());
        }
        if (m_c1) {
            (*m_c1)(m, tmp_prs.size(), tmp_prs.c_ptr(), result);
        }
        else {
            SASSERT(tmp_prs.size() == 1);
            result = tmp_prs[0];
        }
    }

    virtual proof_converter * translate(ast_translation & translator) {
        return this->translate_core<concat_star_proof_converter>(translator);
    }
};

proof_converter * concat(proof_converter * pc1, unsigned num, proof_converter * const * pc2s, unsigned * szs) {
    SASSERT(num > 0);
    if (num == 1)
        return concat(pc1, pc2s[0]);
    unsigned i;
    for (i = 0; i < num; i++) {
        if (pc2s[i] != 0)
            break;
    }
    if (i == num) {
        // all pc2s are 0
        return pc1;
    }
    return alloc(concat_star_proof_converter, pc1, num, pc2s, szs);
}

class proof2pc : public proof_converter {
    proof_ref m_pr;
public:
    proof2pc(ast_manager & m, proof * pr):m_pr(pr, m) {}
    virtual ~proof2pc() {}

    virtual void operator()(ast_manager & m, unsigned num_source, proof * const * source, proof_ref & result) {
        SASSERT(num_source == 0);
        result = m_pr;
    }

    virtual proof_converter * translate(ast_translation & translator) {
        return alloc(proof2pc, translator.to(), translator(m_pr.get()));
    }

    virtual void display(std::ostream & out) {
        out << "(proof->proof-converter-wrapper\n" << mk_ismt2_pp(m_pr.get(), m_pr.get_manager()) << ")\n";
    }    
};

proof_converter * proof2proof_converter(ast_manager & m, proof * pr) {
    if (pr == 0)
        return 0;
    return alloc(proof2pc, m, pr);
}

void apply(ast_manager & m, proof_converter * pc, proof_ref & pr) {
    if (pc) {
        proof * _pr = pr.get();
        (*pc)(m, 1, &_pr, pr);
    }
}

/**
   Let pc2s be a buffer of proof converters that are wrappers for proofs.
   That is, they are functors of the form: unit -> Proof
   Then, this function applies pc1 to the proofs produced by pc2s's and store
   the resultant proof in result.
   
   pc1 and pc2s must be different from 0.
*/
void apply(ast_manager & m, proof_converter_ref & pc1, proof_converter_ref_buffer & pc2s, proof_ref & result) {
    SASSERT(pc1);
    proof_ref_buffer prs(m);
    unsigned sz = pc2s.size();
    for (unsigned i = 0; i < sz; i++) {
        proof_ref pr(m);
        SASSERT(pc2s[i]); // proof production is enabled
        pc2s[i]->operator()(m, 0, 0, pr);
        prs.push_back(pr);
    }
    (*pc1)(m, sz, prs.c_ptr(), result);
}
