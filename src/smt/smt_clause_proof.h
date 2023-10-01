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
#pragma once

#include "ast/ast_pp_util.h"
#include "smt/smt_theory.h"
#include "smt/smt_clause.h"
#include "smt/smt_justification.h"
#include "tactic/user_propagator_base.h"

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
        context&        ctx;
        ast_manager&    m;
        expr_ref_vector m_lits;
        vector<info>    m_trail;
        bool            m_enabled = false;
        bool            m_has_log = false;
        user_propagator::on_clause_eh_t m_on_clause_eh;
        void*                           m_on_clause_ctx = nullptr;
        ast_pp_util                     m_pp;
        scoped_ptr<std::ofstream>       m_pp_out;
        proof_ref m_assumption, m_rup, m_del, m_smt;

        void init_pp_out();
        
        void update(status st, expr_ref_vector& v, proof* p);
        void update(clause& c, status st, proof* p, literal_buffer const* simp_lits);
        status kind2st(clause_kind k);
        proof_ref justification2proof(status st, justification* j);
        void log(status st, proof* p);
        void declare(std::ostream& out, expr* e);
        std::ostream& display_literals(std::ostream& out, expr_ref_vector const& v);
        std::ostream& display_hint(std::ostream& out, proof* p);
    public:
        clause_proof(context& ctx);
        void shrink(clause& c, unsigned new_size);
        void add(literal lit, clause_kind k, justification* j);
        void add(literal lit1, literal lit2, clause_kind k, justification* j, literal_buffer const* simp_lits = nullptr);
        void add(clause& c, literal_buffer const* simp_lits = nullptr);
        void add(unsigned n, literal const* lits, clause_kind k, justification* j);
        void propagate(literal lit, justification const& j, literal_vector const& ante);
        void del(clause& c);
        proof_ref get_proof(bool inconsistent);
        bool is_enabled() const { return m_enabled; }
        void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) {
            m_on_clause_eh = on_clause;
            m_on_clause_ctx = ctx;
            m_enabled |= !!m_on_clause_eh;
        }
    };

    std::ostream& operator<<(std::ostream& out, clause_proof::status st);
};


