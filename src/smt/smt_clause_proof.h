/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    smt_clause_proof.h

Abstract:

    This module tracks clausal proof objects as a trail of added and removed assumptions (input clauses)
    theory lemmas and axioms, and lemmas produced from conflict resolution (possibly using theory propagation).
   
    Clausal proofs may serve a set of purposes:
    - detailed diagnostics of general properties of the search.
    - an interface to proof checking 
    - an interface to replay in trusted bases
    - an interface to proof pruning methods
    - an interface to clausal interpolation methods.

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
    public:
        enum status {
            lemma,
            assumption,
            th_lemma,
            th_assumption,
            deleted
        };
    private:

        struct info {
            status          m_status;
            expr_ref_vector m_clause;     
            proof_ref       m_proof;
            info(status st, expr_ref_vector& v, proof* p): m_status(st), m_clause(v), m_proof(p, m_clause.m()) {}
        };
        context&     ctx;
        ast_manager& m;
        expr_ref_vector m_lits;
        vector<info> m_trail;
        void update(status st, expr_ref_vector& v, proof* p);
        void update(clause& c, status st, proof* p);
        status kind2st(clause_kind k);
        proof* justification2proof(justification* j);
    public:
        clause_proof(context& ctx);
        void shrink(clause& c, unsigned new_size);
        void add(literal lit, clause_kind k, justification* j);
        void add(literal lit1, literal lit2, clause_kind k, justification* j);
        void add(clause& c);
        void add(unsigned n, literal const* lits, clause_kind k, justification* j);
        void del(clause& c);
        proof_ref get_proof();
    };

    std::ostream& operator<<(std::ostream& out, clause_proof::status st);
};

#endif /* SMT_CLAUSE_PROOF_H_ */

