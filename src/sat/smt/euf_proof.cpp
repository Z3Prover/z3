/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_proof.cpp

Abstract:

    Proof logging facilities.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "sat/smt/euf_solver.h"
#include "ast/ast_util.h"
#include <iostream>

namespace euf {

    void solver::init_proof() {
        if (!m_proof_initialized) {
            get_drat().add_theory(get_id(), symbol("euf"));
            get_drat().add_theory(m.get_basic_family_id(), symbol("bool"));
        }
        if (!m_proof_out && s().get_config().m_drat && 
            (get_config().m_lemmas2console || s().get_config().m_smt_proof.is_non_empty_string())) {
            TRACE("euf", tout << "init-proof\n");
            m_proof_out = alloc(std::ofstream, s().get_config().m_smt_proof.str(), std::ios_base::out);
            if (get_config().m_lemmas2console) 
                get_drat().set_clause_eh(*this);
            if (s().get_config().m_smt_proof.is_non_empty_string()) 
                get_drat().set_clause_eh(*this);
        }
        m_proof_initialized = true;
    }

    /**
     * \brief logs antecedents to a proof trail.
     *
     * NB with theories, this is not a pure EUF justification,
     * It is true modulo EUF and previously logged certificates
     * so it isn't necessarily an axiom over EUF,
     * We will here leave it to the EUF checker to perform resolution steps.
     */
    void solver::log_antecedents(literal l, literal_vector const& r) {
        TRACE("euf", log_antecedents(tout, l, r););
        if (!use_drat())
            return;
        literal_vector lits;
        for (literal lit : r) 
            lits.push_back(~lit);
        if (l != sat::null_literal)
            lits.push_back(l);
        get_drat().add(lits, sat::status::th(true, get_id()));
    }

    void solver::log_antecedents(std::ostream& out, literal l, literal_vector const& r) {
        for (sat::literal l : r) {
            expr* n = m_bool_var2expr[l.var()];
            out << ~l << ": ";
            if (!l.sign()) out << "! ";
            out << mk_bounded_pp(n, m) << "\n";
            SASSERT(s().value(l) == l_true);
        }
        if (l != sat::null_literal) {
            out << l << ": ";
            if (l.sign()) out << "! ";
            expr* n = m_bool_var2expr[l.var()];
            out << mk_bounded_pp(n, m) << "\n";
        }
    }

    void solver::set_tmp_bool_var(bool_var b, expr* e) {
        m_bool_var2expr.setx(b, e, nullptr);
    }

    void solver::log_justification(literal l, th_explain const& jst) {
        literal_vector lits;
        expr_ref_vector eqs(m);
        unsigned nv = s().num_vars();
        auto add_lit = [&](enode_pair const& eq) {
            unsigned v = nv;
            ++nv;
            eqs.push_back(m.mk_eq(eq.first->get_expr(), eq.second->get_expr()));
            set_tmp_bool_var(v, eqs.back());
            return literal(v, false);
        };

        for (auto lit : euf::th_explain::lits(jst))
            lits.push_back(~lit);
        if (l != sat::null_literal)
            lits.push_back(l);
        for (auto eq : euf::th_explain::eqs(jst)) 
            lits.push_back(~add_lit(eq));
        if (jst.lit_consequent() != sat::null_literal && jst.lit_consequent() != l) 
            lits.push_back(jst.lit_consequent());
        if (jst.eq_consequent().first != nullptr) 
            lits.push_back(add_lit(jst.eq_consequent()));
        get_drat().add(lits, sat::status::th(m_is_redundant, jst.ext().get_id(), jst.get_pragma()));
        for (unsigned i = s().num_vars(); i < nv; ++i)
            set_tmp_bool_var(i, nullptr);
    }

    void solver::on_clause(unsigned n, literal const* lits, sat::status st) {
        TRACE("euf", tout << "on-clause " << n << "\n");
        on_lemma(n, lits, st);
        on_proof(n, lits, st);
    }

    void solver::on_proof(unsigned n, literal const* lits, sat::status st) {
        if (!m_proof_out)
            return;
        flet<bool> _display_all_decls(m_display_all_decls, true);
        std::ostream& out = *m_proof_out;
        if (!visit_clause(out, n, lits))
            return;
        if (st.is_asserted()) 
            display_redundant(out, n, lits, status2proof_hint(st));
        else if (st.is_deleted()) 
            display_deleted(out, n, lits);        
        else if (st.is_redundant()) 
            display_redundant(out, n, lits, status2proof_hint(st));
        else if (st.is_input()) 
            display_assume(out, n, lits);
        else 
            UNREACHABLE();
        out.flush();
    }
        
    void solver::on_lemma(unsigned n, literal const* lits, sat::status st) {
        if (!get_config().m_lemmas2console) 
            return;
        if (!st.is_redundant() && !st.is_asserted()) 
            return;
        
        std::ostream& out = std::cout;
        if (!visit_clause(out, n, lits))
            return;
        std::function<symbol(int)> ppth = [&](int th) {
            return m.get_family_name(th);
        };
        if (!st.is_sat())
            out << "; " << sat::status_pp(st, ppth) << "\n";

        display_assert(out, n, lits);
    }

    void solver::on_instantiation(unsigned n, sat::literal const* lits, unsigned k, euf::enode* const* bindings) {
        std::ostream& out = std::cout;
        for (unsigned i = 0; i < k; ++i)
            visit_expr(out, bindings[i]->get_expr());        
        VERIFY(visit_clause(out, n, lits));
        out << "(instantiate";
        display_literals(out, n, lits);
        for (unsigned i = 0; i < k; ++i) 
            display_expr(out << " :binding ", bindings[i]->get_expr());
        out << ")\n";
    }

    bool solver::visit_clause(std::ostream& out, unsigned n, literal const* lits) {
        for (unsigned i = 0; i < n; ++i) {
            expr* e = bool_var2expr(lits[i].var());
            if (!e)
                return false;
            visit_expr(out, e);
        }
        return true;
    }

    void solver::display_assert(std::ostream& out, unsigned n, literal const* lits) {
        display_literals(out << "(assert (or", n, lits) << "))\n";
    }
    
    void solver::display_assume(std::ostream& out, unsigned n, literal const* lits) {
        display_literals(out << "(assume", n, lits) << ")\n";        
    }

    void solver::display_redundant(std::ostream& out, unsigned n, literal const* lits, expr* proof_hint) {
        if (proof_hint)
            visit_expr(out, proof_hint);
        display_hint(display_literals(out << "(learn", n, lits), proof_hint) << ")\n";        
    }

    void solver::display_deleted(std::ostream& out, unsigned n, literal const* lits) {
        display_literals(out << "(del", n, lits) << ")\n";        
    }

    std::ostream& solver::display_hint(std::ostream& out, expr* proof_hint) {
        if (proof_hint)
            return display_expr(out << " ", proof_hint);
        else
            return out;
    }

    expr_ref solver::status2proof_hint(sat::status st) {
        if (st.is_sat()) 
            return expr_ref(m.mk_const("rup", m.mk_proof_sort()), m); // provable by reverse unit propagation
        auto* h = reinterpret_cast<euf::th_proof_hint const*>(st.get_hint());
        if (!h)
            return expr_ref(m);

        expr* e = h->get_hint(*this);
        if (e)
            return expr_ref(e, m);

        return expr_ref(m);        
    }

    std::ostream& solver::display_literals(std::ostream& out, unsigned n, literal const* lits) {
        for (unsigned i = 0; i < n; ++i) {
            expr* e = bool_var2expr(lits[i].var());
            if (lits[i].sign())
                display_expr(out << " (not ", e) << ")";
            else
                display_expr(out << " ", e);
        }
        return out;
    }

    void solver::visit_expr(std::ostream& out, expr* e) {
        m_clause_visitor.collect(e);
        if (m_display_all_decls)
            m_clause_visitor.display_decls(out);
        else
            m_clause_visitor.display_skolem_decls(out);
        m_clause_visitor.define_expr(out, e);
    }

    std::ostream& solver::display_expr(std::ostream& out, expr* e) {
        return m_clause_visitor.display_expr_def(out, e);
    }

}
