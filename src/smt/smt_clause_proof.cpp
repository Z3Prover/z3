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
#include "ast/ast_ll_pp.h"
#include <iostream>

namespace smt {
    
    clause_proof::clause_proof(context& ctx):
        ctx(ctx), m(ctx.get_manager()), m_lits(m), m_pp(m),
        m_assumption(m), m_rup(m), m_del(m), m_smt(m) {
        
        auto proof_log = ctx.get_fparams().m_proof_log;
        m_has_log = proof_log.is_non_empty_string();
        m_enabled = ctx.get_fparams().m_clause_proof || m_has_log;        
    }

    void clause_proof::init_pp_out() {
        if (m_has_log && !m_pp_out) {
            static unsigned id = 0;
            auto proof_log = ctx.get_fparams().m_proof_log;
            std::string log_name = proof_log.str();
            if (id > 0)
                log_name = std::to_string(id) + log_name;
            ++id;
            m_pp_out = alloc(std::ofstream, log_name);
            if (!*m_pp_out)
                throw default_exception(std::string("Could not open file ") + proof_log.str());
        }
    }

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

    proof_ref clause_proof::justification2proof(status st, justification* j) {
        proof* r = nullptr;
        if (j)
            r = j->mk_proof(ctx.get_cr());
        if (r) 
            return proof_ref(r, m);
        if (!is_enabled())
            return proof_ref(m);
        switch (st) {
        case status::assumption:
            if (!m_assumption) 
                m_assumption = m.mk_const("assumption", m.mk_proof_sort());
            return m_assumption;
        case status::lemma:
            if (!m_rup)
                m_rup = m.mk_const("rup", m.mk_proof_sort());
            return m_rup;
        case status::th_lemma:
        case status::th_assumption:
            if (!m_smt)
                m_smt = m.mk_const("smt", m.mk_proof_sort());
            return m_smt;
        case status::deleted:
            if (!m_del)
                m_del = m.mk_const("del", m.mk_proof_sort());
            return m_del;
        }
        UNREACHABLE();
        return proof_ref(m);
    }

    void clause_proof::add(clause& c, literal_buffer const* simp_lits) {
        if (!is_enabled())
            return;
        justification* j = c.get_justification();
        auto st = kind2st(c.get_kind());
        auto pr = justification2proof(st, j);
        CTRACE("mk_clause", pr.get(), tout << mk_bounded_pp(pr, m, 4) << "\n";);
        update(c, st, pr, simp_lits);        
    }

    void clause_proof::add(unsigned n, literal const* lits, clause_kind k, justification* j) {
        if (!is_enabled())
            return;
        auto st = kind2st(k);
        auto pr = justification2proof(st, j);
        CTRACE("mk_clause", pr.get(), tout << mk_bounded_pp(pr, m, 4) << "\n";);
        m_lits.reset();
        for (unsigned i = 0; i < n; ++i) 
            m_lits.push_back(ctx.literal2expr(lits[i]));
        update(st, m_lits, pr);
    }


    void clause_proof::shrink(clause& c, unsigned new_size) {
        if (!is_enabled())
            return;
        m_lits.reset();
        for (unsigned i = 0; i < new_size; ++i) 
            m_lits.push_back(ctx.literal2expr(c[i]));
        auto p = justification2proof(status::lemma, nullptr);
        update(status::lemma, m_lits, p);
        for (unsigned i = new_size; i < c.get_num_literals(); ++i) 
            m_lits.push_back(ctx.literal2expr(c[i]));
        p = justification2proof(status::deleted, nullptr);
        update(status::deleted, m_lits, p);
    }

    void clause_proof::add(literal lit, clause_kind k, justification* j) {
        if (!is_enabled())
            return;
        m_lits.reset();
        m_lits.push_back(ctx.literal2expr(lit));
        auto st = kind2st(k);
        auto pr = justification2proof(st, j);
        update(st, m_lits, pr);
    }

    void clause_proof::add(literal lit1, literal lit2, clause_kind k, justification* j, literal_buffer const* simp_lits) {
        if (!is_enabled())
            return;
        m_lits.reset();
        m_lits.push_back(ctx.literal2expr(lit1));
        m_lits.push_back(ctx.literal2expr(lit2));
        if (simp_lits) 
            for (auto lit : *simp_lits)
                m_lits.push_back(ctx.literal2expr(~lit));
        auto st = kind2st(k);
        auto pr = justification2proof(st, j);
        update(st, m_lits, pr);
    }

    void clause_proof::propagate(literal lit, justification const& jst, literal_vector const& ante) {
        if (!is_enabled())
            return;
        m_lits.reset();
        for (literal l : ante)
            m_lits.push_back(ctx.literal2expr(~l));
        m_lits.push_back(ctx.literal2expr(lit));
        proof_ref pr(m.mk_app(symbol("smt"), 0, nullptr, m.mk_proof_sort()), m);
        update(clause_proof::status::th_lemma, m_lits, pr);
    }

    void clause_proof::del(clause& c) {
        update(c, status::deleted, justification2proof(status::deleted, nullptr), nullptr);
    }

    std::ostream& clause_proof::display_literals(std::ostream& out, expr_ref_vector const& v) {
        for (expr* e : v)
            if (m.is_not(e, e))                
                m_pp.display_expr_def(out << " (not ", e) << ")";
            else
                m_pp.display_expr_def(out << " ", e);
        return out;
    }

    std::ostream& clause_proof::display_hint(std::ostream& out, proof* p) {
        if (p)
            m_pp.display_expr_def(out << " ", p);
        return out;
    }

    void clause_proof::declare(std::ostream& out, expr* e) {
        m_pp.collect(e);
        m_pp.display_decls(out);
        m.is_not(e, e);
        m_pp.define_expr(out, e);
    }

    void clause_proof::update(status st, expr_ref_vector& v, proof* p) {
        TRACE("clause_proof", tout << m_trail.size() << " " << st << " " << v << "\n";);
        if (ctx.get_fparams().m_clause_proof)
            m_trail.push_back(info(st, v, p));
        if (m_on_clause_eh) 
            m_on_clause_eh(m_on_clause_ctx, p, 0, nullptr, v.size(), v.data());
        
        if (m_has_log) {
            init_pp_out();
            auto& out = *m_pp_out;
            for (auto* e : v)
                declare(out, e);
            switch (st) {
            case clause_proof::status::assumption:
                if (!p || p->get_decl()->get_name() == "assumption") {
                    display_literals(out << "(assume", v) << ")\n";
                    break;
                }
                Z3_fallthrough;
            case clause_proof::status::lemma:
            case clause_proof::status::th_lemma:
            case clause_proof::status::th_assumption:
                if (p)
                    declare(out, p);
                display_hint(display_literals(out << "(infer", v), p) << ")\n";
                break;
            case clause_proof::status::deleted:
                display_literals(out << "(del", v) << ")\n";
                break;
            default:
                UNREACHABLE();
            }
            out.flush();
        }
    }

    void clause_proof::update(clause& c, status st, proof* p, literal_buffer const* simp_lits) {
        if (!is_enabled())
            return;
        m_lits.reset();
        for (literal lit : c) 
            m_lits.push_back(ctx.literal2expr(lit));
        if (simp_lits) 
            for (auto lit : *simp_lits)
                m_lits.push_back(ctx.literal2expr(~lit));
        update(st, m_lits, p);        
    }

    proof_ref clause_proof::get_proof(bool inconsistent) {
        TRACE("context", tout << "get-proof " << ctx.get_fparams().m_clause_proof << "\n";);
        if (!ctx.get_fparams().m_clause_proof) 
            return proof_ref(m);
        expr_ref_vector ps(m);
        for (auto& info : m_trail) {
            expr_ref fact = mk_or(info.m_clause);
            proof* pr = info.m_proof;
            expr* args[2] = { pr, fact };
            unsigned num_args = 2, offset = 0;
            if (!pr) 
                offset = 1;
            switch (info.m_status) {
            case status::assumption:
                ps.push_back(m.mk_app(symbol("assumption"), num_args - offset, args + offset, m.mk_proof_sort()));
                break;
            case status::lemma:
                ps.push_back(m.mk_app(symbol("lemma"), num_args - offset, args + offset, m.mk_proof_sort()));
                break;
            case status::th_assumption:
                ps.push_back(m.mk_app(symbol("th-assumption"), num_args - offset, args + offset, m.mk_proof_sort()));
                break;
            case status::th_lemma:
                ps.push_back(m.mk_app(symbol("th-lemma"), num_args - offset, args + offset, m.mk_proof_sort()));
                break;
            case status::deleted:
                ps.push_back(m.mk_redundant_del(fact));
                break;
            }
        }
        if (inconsistent) 
            ps.push_back(m.mk_false());
        else 
            ps.push_back(m.mk_const("clause-trail-end", m.mk_bool_sort()));
        return proof_ref(m.mk_clause_trail(ps.size(), ps.data()), m);
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


