/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    smt_clause_proof.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-15

Revision History:

--*/
#ifndef SMT_CLAUSE_PROOF_H_
#define SMT_CLAUSE_PROOF_H_

#include "smt/smt_theory.h"
#include "smt/smt_clause.h"

namespace smt {
    class context;
    class justification;

    class clause_proof {
        enum status {
            lemma,
            hypothesis,
            deleted
        };

        struct info {
            status          m_status;
            expr_ref_vector m_clause;     
            proof_ref       m_proof;
            info(status st, expr_ref_vector& v, proof* p): m_status(st), m_clause(v), m_proof(p, m_clause.m()) {}
        };
        context&     ctx;
        ast_manager& m;
        vector<info> m_trail;
        void update(clause& c, status st, proof* p);
        status kind2st(clause_kind k);
    public:
        clause_proof(context& ctx);
        void add(literal lit, clause_kind k, justification* j);
        void add(literal lit1, literal lit2, clause_kind k, justification* j);
        void add(clause& c);
        void add_lemma(clause& c);
        void del(clause& c);
        proof_ref get_proof();
    };

};

#endif /* SMT_CLAUSE_PROOF_H_ */

