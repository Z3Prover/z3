/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    smt_clause_proof.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-15

Revision History:

--*/
#include "smt/smt_clause_proof.h"
#include "smt/smt_context.h"
#include "ast/ast_pp.h"

namespace smt {
    clause_proof::clause_proof(context& ctx): ctx(ctx), m(ctx.get_manager()), m_lits(m) {}

    clause_proof::status clause_proof::kind2st(clause_kind k) {
        switch (k) {
        case CLS_AUX: 
            return status::assumption;
        case CLS_TH_AXIOM:
            return status::th_assumption;
        case CLS_LEARNED:
            return status::lemma;
        case CLS_TH_LEMMA:
            return status::th_lemma;
        default:
            UNREACHABLE();
            return status::lemma;
        }
    }

    proof* clause_proof::justification2proof(justification* j) {
        return (m.proofs_enabled() && j) ? j->mk_proof(ctx.get_cr()) : nullptr;
    }

    void clause_proof::add(clause& c) {
        if (ctx.get_fparams().m_clause_proof) {  
            justification* j = c.get_justification();
            proof* pr = justification2proof(j);
            update(c, kind2st(c.get_kind()), pr);
        }
    }

    void clause_proof::add(unsigned n, literal const* lits, clause_kind k, justification* j) {
        if (ctx.get_fparams().m_clause_proof) {  
            proof* pr = justification2proof(j);
            m_lits.reset();
            for (unsigned i = 0; i < n; ++i) {
                literal lit = lits[i];
                m_lits.push_back(ctx.literal2expr(lit));
            }
            update(kind2st(k), m_lits, pr);
        }
    }


    void clause_proof::shrink(clause& c, unsigned new_size) {
        if (ctx.get_fparams().m_clause_proof) {            
            m_lits.reset();
            for (unsigned i = 0; i < new_size; ++i) {
                m_lits.push_back(ctx.literal2expr(c[i]));
            }
            update(status::lemma, m_lits, nullptr);
            for (unsigned i = new_size; i < c.get_num_literals(); ++i) {
                m_lits.push_back(ctx.literal2expr(c[i]));
            }
            update(status::deleted, m_lits, nullptr);
        }
    }

    void clause_proof::add(literal lit, clause_kind k, justification* j) {
        if (ctx.get_fparams().m_clause_proof) {
            m_lits.reset();
            m_lits.push_back(ctx.literal2expr(lit));
            proof* pr = justification2proof(j);
            update(kind2st(k), m_lits, pr);
        }
    }

    void clause_proof::add(literal lit1, literal lit2, clause_kind k, justification* j) {
        if (ctx.get_fparams().m_clause_proof) {
            m_lits.reset();
            m_lits.push_back(ctx.literal2expr(lit1));
            m_lits.push_back(ctx.literal2expr(lit2));
            proof* pr = justification2proof(j);
            m_trail.push_back(info(kind2st(k), m_lits, pr));
        }
    }


    void clause_proof::del(clause& c) {
        update(c, status::deleted, nullptr);
    }

    void clause_proof::update(status st, expr_ref_vector& v, proof* p) {
        TRACE("clause_proof", tout << st << " " << v << "\n";);
        IF_VERBOSE(3, verbose_stream() << st << " " << v << "\n");
        m_trail.push_back(info(st, v, p));
    }

    void clause_proof::update(clause& c, status st, proof* p) {
        if (ctx.get_fparams().m_clause_proof) {
            m_lits.reset();
            for (literal lit : c) {
                m_lits.push_back(ctx.literal2expr(lit));
            }
            update(st, m_lits, p);
        }
    }

    proof_ref clause_proof::get_proof() {
        TRACE("context", tout << "get-proof " << ctx.get_fparams().m_clause_proof << "\n";);
        if (!ctx.get_fparams().m_clause_proof) {
            return proof_ref(m);
        }
        proof_ref_vector ps(m);
        for (auto& info : m_trail) {
            expr_ref fact = mk_or(info.m_clause);
            proof* pr = info.m_proof;
            switch (info.m_status) {
            case status::assumption:
                ps.push_back(m.mk_assumption_add(pr, fact)); 
                break;
            case status::lemma:
                ps.push_back(m.mk_lemma_add(pr, fact)); 
                break;
            case status::th_assumption:
                ps.push_back(m.mk_th_assumption_add(pr, fact)); 
                break;
            case status::th_lemma:
                ps.push_back(m.mk_th_lemma_add(pr, fact)); 
                break;
            case status::deleted:
                ps.push_back(m.mk_redundant_del(fact));
                break;
            }
        }
        return proof_ref(m.mk_clause_trail(ps.size(), ps.c_ptr()), m);
    }

    std::ostream& operator<<(std::ostream& out, clause_proof::status st) {
        switch (st) {
        case clause_proof::status::assumption:
            return out << "asm";
        case clause_proof::status::th_assumption:
            return out << "th_asm";
        case clause_proof::status::lemma:
            return out << "lem";
        case clause_proof::status::th_lemma:
            return out << "th_lem";
        case clause_proof::status::deleted:
            return out << "del";
        default:
            return out << "unkn";
        }
    }

};


