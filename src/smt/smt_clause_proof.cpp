/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    smt_clause_proof.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-15

Revision History:

--*/
#include "smt/smt_clause_proof.h"
#include "smt/smt_context.h"
#include "ast/ast_pp.h"

namespace smt {
    clause_proof::clause_proof(context& ctx): ctx(ctx), m(ctx.get_manager()) {}

    clause_proof::status clause_proof::kind2st(clause_kind k) {
        switch (k) {
        case CLS_AUX: 
            return status::hypothesis;
        case CLS_LEARNED:
        case CLS_AUX_LEMMA:
            return status::lemma;
        default:
            UNREACHABLE();
            return status::lemma;
        }
    }

    void clause_proof::add(clause& c) {
        update(c, kind2st(c.get_kind()));
    }

    void clause_proof::add(literal lit, clause_kind k) {
        if (!ctx.get_fparams().m_clause_proof) {
            return;
        }
        expr_ref_vector lits(m);
        lits.push_back(ctx.literal2expr(lit));
        m_trail.push_back(info(kind2st(k), lits));
    }

    void clause_proof::add(literal lit1, literal lit2, clause_kind k) {
        if (!ctx.get_fparams().m_clause_proof) {
            return;
        }
        expr_ref_vector lits(m);
        lits.push_back(ctx.literal2expr(lit1));
        lits.push_back(ctx.literal2expr(lit2));
        m_trail.push_back(info(kind2st(k), lits));
    }


    void clause_proof::del(clause& c) {
        update(c, status::deleted);
    }

    void clause_proof::update(clause& c, status st) {
        if (!ctx.get_fparams().m_clause_proof) {
            return;
        }
        expr_ref_vector lits(m);
        for (literal lit : c) {
            lits.push_back(ctx.literal2expr(lit));
        }
        m_trail.push_back(info(st, lits));
    }

    proof_ref clause_proof::proof() {
        if (!ctx.get_fparams().m_clause_proof) {
            return proof_ref(m);
        }
        proof_ref_vector ps(m);
        for (auto& info : m_trail) {
            expr_ref fact = mk_or(info.m_clause);
            switch (info.m_status) {
            case status::hypothesis:
                ps.push_back(m.mk_assumption_add(fact));
                break;
            case status::lemma:
                ps.push_back(m.mk_lemma_add(fact));
                break;
            case status::deleted:
                ps.push_back(m.mk_redundant_del(fact));
                break;
            }
        }
        return proof_ref(m.mk_clause_trail(ps.size(), ps.c_ptr()), m);
    }

};


