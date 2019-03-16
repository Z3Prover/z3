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
        if (ctx.get_fparams().m_clause_proof) {  
            justification* j = c.get_justification();
            proof* pr = nullptr; // j ? j->mk_proof(ctx.get_cr()) : nullptr;          
            update(c, kind2st(c.get_kind()), pr);
        }
    }

    void clause_proof::add_lemma(clause& c) {
        if (ctx.get_fparams().m_clause_proof) {            
            update(c, status::lemma, nullptr);
        }
    }

    void clause_proof::add(literal lit, clause_kind k, justification* j) {
        if (ctx.get_fparams().m_clause_proof) {
            expr_ref_vector lits(m);
            lits.push_back(ctx.literal2expr(lit));
            proof* pr = nullptr; // j ? j->mk_proof(ctx.get_cr()) : nullptr; 
            m_trail.push_back(info(kind2st(k), lits, pr));
        }
    }

    void clause_proof::add(literal lit1, literal lit2, clause_kind k, justification* j) {
        if (ctx.get_fparams().m_clause_proof) {
            expr_ref_vector lits(m);
            lits.push_back(ctx.literal2expr(lit1));
            lits.push_back(ctx.literal2expr(lit2));
            proof* pr = nullptr; // j ? j->mk_proof(ctx.get_cr()) : nullptr;          
            m_trail.push_back(info(kind2st(k), lits, pr));
        }
    }


    void clause_proof::del(clause& c) {
        update(c, status::deleted, nullptr);
    }

    void clause_proof::update(clause& c, status st, proof* p) {
        if (ctx.get_fparams().m_clause_proof) {
            expr_ref_vector lits(m);
            for (literal lit : c) {
                lits.push_back(ctx.literal2expr(lit));
            }
            m_trail.push_back(info(st, lits, p));
        }
    }

    proof_ref clause_proof::get_proof() {
        if (!ctx.get_fparams().m_clause_proof) {
            return proof_ref(m);
        }
        proof_ref_vector ps(m);
        for (auto& info : m_trail) {
            expr_ref fact = mk_or(info.m_clause);
            proof* pr = info.m_proof;
            switch (info.m_status) {
            case status::hypothesis:
                ps.push_back(m.mk_assumption_add(pr, fact)); 
                break;
            case status::lemma:
                ps.push_back(m.mk_lemma_add(pr, fact)); 
                break;
            case status::deleted:
                ps.push_back(m.mk_redundant_del(fact));
                break;
            }
        }
        return proof_ref(m.mk_clause_trail(ps.size(), ps.c_ptr()), m);
    }

};


