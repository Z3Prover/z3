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
        if (m_proof_initialized)
            return;

        if (m_on_clause && !s().get_config().m_drat_disable)
            s().set_drat(true);
        
        if (!s().get_config().m_drat)
            return;

        if (!get_config().m_lemmas2console &&
            !s().get_config().m_smt_proof_check &&
            !m_on_clause &&
            !m_config.m_proof_log.is_non_empty_string())
            return;
        
        if (m_config.m_proof_log.is_non_empty_string())
            m_proof_out = alloc(std::ofstream, m_config.m_proof_log.str(), std::ios_base::out);
        get_drat().set_clause_eh(*this);
        m_proof_initialized = true;        
    }

    enode_pair solver::get_justification_eq(size_t j) {
        auto* ext = sat::constraint_base::to_extension(j);
        SASSERT(ext != this);
        auto s = fid2solver(ext->get_id());
        return s->get_justification_eq(j);
    }

    /**
    * Log justifications.
    * is_euf - true if l is justified by congruence closure. In this case create a congruence closure proof.
    * explain_size - the relevant portion of premises for the congruence closure proof.
    * The EUF solver manages equality propagation. Each propagated equality is justified by a congruence closure.
    */
    void solver::log_justifications(literal l, unsigned explain_size, bool is_euf) {

        unsigned nv = s().num_vars();
        expr_ref_vector eqs(m);

        auto add_hint_literals = [&](unsigned sz) {
            eqs.reset();
            m_hint_lits.reset();
            nv = s().num_vars();
            for (unsigned i = 0; i < sz; ++i) {
                size_t* e = m_explain[i];
                if (is_literal(e))
                    m_hint_lits.push_back(get_literal(e));
                else {
                    SASSERT(is_justification(e));
                    auto [x, y] = get_justification_eq(get_justification(e));
                    eqs.push_back(m.mk_eq(x->get_expr(), y->get_expr()));
                    set_tmp_bool_var(nv, eqs.back());
                    m_hint_lits.push_back(literal(nv, false));
                    ++nv;
                }
            }
        };

        auto clear_hint_literals = [&]() {
            for (unsigned v = s().num_vars(); v < nv; ++v)
                set_tmp_bool_var(v, nullptr);
        };

        // log EUF justifications
        if (is_euf) {
            add_hint_literals(explain_size);
            auto* hint = mk_hint(m_euf, l);
            log_antecedents(l, m_hint_lits, hint);
            clear_hint_literals();
        }

        // explain equalities
        for (auto const& [a, b] : m_hint_eqs) {
            m_egraph.begin_explain();
            m_explain.reset();
            m_egraph.explain_eq<size_t>(m_explain, &m_explain_cc, a, b);
            m_egraph.end_explain();
            // Detect shortcut if equality is explained directly by a theory
            if (m_explain.size() == 1 && !is_literal(m_explain[0])) {
                auto const& [x, y] = th_explain::from_index(get_justification(m_explain[0])).eq_consequent();
                if (x == a && y == b)
                    continue;
            }
            add_hint_literals(m_explain.size());
            eqs.push_back(m.mk_eq(a->get_expr(), b->get_expr()));
            set_tmp_bool_var(nv, eqs.back());
            sat::literal eql = literal(nv, false);
            ++nv;
            auto* hint = mk_hint(m_euf, eql);
            log_antecedents(eql, m_hint_lits, hint);
            clear_hint_literals();
        }
    }

    void solver::log_antecedents(literal l, literal_vector const& r, th_proof_hint* hint) {
        SASSERT(hint && use_drat());
        TRACE("euf", log_antecedents(tout, l, r); tout << mk_pp(hint->get_hint(*this), m) << "\n");
        literal_vector lits;
        for (literal lit : r) 
            lits.push_back(~lit);
        if (l != sat::null_literal)
            lits.push_back(l);
        get_drat().add(lits, sat::status::th(true, get_id(), hint));
    }

    void solver::log_rup(literal l, literal_vector const& r) {
        literal_vector lits;
        for (literal lit : r)
            lits.push_back(~lit);
        if (l != sat::null_literal)
            lits.push_back(l);
        get_drat().add(lits, sat::status::redundant());
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

    eq_proof_hint* solver::mk_hint(symbol const& th, literal conseq) {
        if (!use_drat())
            return nullptr;
        push(value_trail(m_lit_tail));
        push(value_trail(m_cc_tail));
        push(restore_vector(m_proof_literals));
        if (conseq != sat::null_literal)
            m_proof_literals.push_back(~conseq);
        m_proof_literals.append(m_hint_lits);
        m_lit_head = m_lit_tail;
        m_cc_head  = m_cc_tail;
        m_lit_tail = m_proof_literals.size();
        m_cc_tail  = m_explain_cc.size();
        return new (get_region()) eq_proof_hint(th, m_lit_head, m_lit_tail, m_cc_head, m_cc_tail);
    }

    th_proof_hint* solver::mk_cc_proof_hint(sat::literal_vector const& ante, app* a, app* b) {
        if (!use_drat())
            return nullptr;
        SASSERT(a->get_decl() == b->get_decl());
        push(value_trail(m_lit_tail));
        push(value_trail(m_cc_tail));
        push(restore_vector(m_proof_literals));
        push(restore_vector(m_explain_cc));

        for (auto lit : ante)
            m_proof_literals.push_back(~lit);

        m_explain_cc.push_back({a, b, 0, false});
        
        m_lit_head = m_lit_tail;
        m_cc_head  = m_cc_tail;
        m_lit_tail = m_proof_literals.size();
        m_cc_tail  = m_explain_cc.size();
        return new (get_region()) eq_proof_hint(m_euf, m_lit_head, m_lit_tail, m_cc_head, m_cc_tail);        
    }

    th_proof_hint* solver::mk_tc_proof_hint(sat::literal const* clause) {
        if (!use_drat())
            return nullptr;
        push(value_trail(m_lit_tail));
        push(value_trail(m_cc_tail));
        push(restore_vector(m_proof_literals));

        for (unsigned i = 0; i < 3; ++i)
            m_proof_literals.push_back(~clause[i]);
        
        m_lit_head = m_lit_tail;
        m_cc_head  = m_cc_tail;
        m_lit_tail = m_proof_literals.size();
        m_cc_tail  = m_explain_cc.size();
        return new (get_region()) eq_proof_hint(m_euf, m_lit_head, m_lit_tail, m_cc_head, m_cc_tail);        
    }


    expr* eq_proof_hint::get_hint(euf::solver& s) const {
        ast_manager& m = s.get_manager();
        func_decl_ref cc(m), cc_comm(m);
        sort* proof = m.mk_proof_sort();
        expr_ref_vector& args = s.m_expr_args;
        args.reset();
        if (m_cc_head < m_cc_tail) {
            sort* sorts[1] = { m.mk_bool_sort() };
            cc_comm = m.mk_func_decl(symbol("comm"), 1, sorts, proof);
            cc = m.mk_func_decl(symbol("cc"), 1, sorts, proof);
        }
        auto cc_proof = [&](bool comm, expr* eq) {
            if (comm)
                return m.mk_app(cc_comm, eq);
            else
                return m.mk_app(cc, eq);
        };
        auto compare_ts = [](cc_justification_record const& a,
                             cc_justification_record const& b) {
            auto const& [_1, _2, ta, _3] = a;
            auto const& [_4, _5, tb, _6] = b;
            return ta < tb;
        };
        for (unsigned i = m_lit_head; i < m_lit_tail; ++i) 
            args.push_back(s.literal2expr(s.m_proof_literals[i]));
        
        std::sort(s.m_explain_cc.data() + m_cc_head, s.m_explain_cc.data() + m_cc_tail, compare_ts);
        for (unsigned i = m_cc_head; i < m_cc_tail; ++i) {
            auto const& [a, b, ts, comm] = s.m_explain_cc[i];
            args.push_back(cc_proof(comm, m.mk_eq(a, b)));
        }        
        return m.mk_app(th, args.size(), args.data(), proof);
    }

    smt_proof_hint* solver::mk_smt_clause(symbol const& n, unsigned nl, literal const* lits) {
        if (!use_drat())
            return nullptr;
        push(value_trail(m_lit_tail));
        push(restore_vector(m_proof_literals));

        for (unsigned i = 0; i < nl; ++i)
            m_proof_literals.push_back(~lits[i]);
            
        m_lit_head = m_lit_tail;
        m_eq_head = m_eq_tail;
        m_deq_head = m_deq_tail;
        m_lit_tail = m_proof_literals.size();
        m_eq_tail = m_proof_eqs.size();
        m_deq_tail = m_proof_deqs.size();

        return new (get_region()) smt_proof_hint(n, m_lit_head, m_lit_tail, m_eq_head, m_eq_tail, m_deq_head, m_deq_tail);
    }
    
    smt_proof_hint* solver::mk_smt_hint(symbol const& n, unsigned nl, literal const* lits, unsigned ne, expr_pair const* eqs, unsigned nd, expr_pair const* deqs) {
        if (!use_drat())
            return nullptr;
        push(value_trail(m_lit_tail));
        push(restore_vector(m_proof_literals));
        
        for (unsigned i = 0; i < nl; ++i)
            if (sat::null_literal != lits[i]) {
                if (!literal2expr(lits[i])) 
                    IF_VERBOSE(0, verbose_stream() << lits[i] << "\n"; display(verbose_stream()));
                
                SASSERT(literal2expr(lits[i]));
                m_proof_literals.push_back(lits[i]);
            }

        push(value_trail(m_eq_tail));
        push(restore_vector(m_proof_eqs));
        m_proof_eqs.append(ne, eqs);
        
        push(value_trail(m_deq_tail));
        push(restore_vector(m_proof_deqs));
        m_proof_deqs.append(nd, deqs);
        
        m_lit_head = m_lit_tail;
        m_eq_head  = m_eq_tail;
        m_deq_head = m_deq_tail;
        m_lit_tail = m_proof_literals.size();
        m_eq_tail  = m_proof_eqs.size();
        m_deq_tail = m_proof_deqs.size();
        
        return new (get_region()) smt_proof_hint(n, m_lit_head, m_lit_tail, m_eq_head, m_eq_tail, m_deq_head, m_deq_tail);
    }

    smt_proof_hint* solver::mk_smt_hint(symbol const& n, unsigned nl, literal const* lits, unsigned ne, enode_pair const* eqs) {
        if (!use_drat())
            return nullptr;
        m_expr_pairs.reset();
        for (unsigned i = 0; i < ne; ++i)
            m_expr_pairs.push_back({ eqs[i].first->get_expr(), eqs[i].second->get_expr() });
        return mk_smt_hint(n, nl, lits, ne, m_expr_pairs.data());
    }

    sat::status solver::mk_tseitin_status(sat::literal a, sat::literal b) {
        sat::literal lits[2] = { a, b };
        return mk_tseitin_status(2, lits);
    }

    sat::status solver::mk_tseitin_status(unsigned n, sat::literal const* lits) {
        th_proof_hint* ph = use_drat() ? mk_smt_hint(symbol("tseitin"), n, lits) : nullptr;
        return sat::status::th(false, m.get_basic_family_id(), ph);        
    }

    sat::status solver::mk_distinct_status(unsigned n, sat::literal const* lits) {
        th_proof_hint* ph = use_drat() ? mk_smt_hint(symbol("alldiff"), n, lits) : nullptr;
        return sat::status::th(false, m.get_basic_family_id(), ph);
    }
    
    expr* smt_proof_hint::get_hint(euf::solver& s) const {
        ast_manager& m = s.get_manager();
        sort* proof = m.mk_proof_sort();
        ptr_buffer<sort> sorts;
        expr_ref_vector args(m);
        
        for (unsigned i = m_lit_head; i < m_lit_tail; ++i) 
            args.push_back(s.literal2expr(s.m_proof_literals[i]));
        for (unsigned i = m_eq_head; i < m_eq_tail; ++i) {
            auto const& [a, b] = s.m_proof_eqs[i];
            args.push_back(m.mk_eq(a, b));
        }
        for (unsigned i = m_deq_head; i < m_deq_tail; ++i) {
            auto const& [a, b] = s.m_proof_deqs[i];
            args.push_back(m.mk_not(m.mk_eq(a, b)));
        }
        return m.mk_app(m_name, args.size(), args.data(), proof);
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
        get_drat().add(lits, sat::status::th(false, jst.ext().get_id(), jst.get_pragma()));
        for (unsigned i = s().num_vars(); i < nv; ++i)
            set_tmp_bool_var(i, nullptr);
    }

    void solver::on_clause(unsigned n, literal const* lits, sat::status st) {
        TRACE("euf_verbose", tout << "on-clause " << n << "\n");
        on_lemma(n, lits, st);
        on_proof(n, lits, st);
        on_check(n, lits, st);
        on_clause_eh(n, lits, st);
    }

    void solver::on_clause_eh(unsigned n, literal const* lits, sat::status st) {
        if (!m_on_clause)
            return;
        m_clause.reset();
        for (unsigned i = 0; i < n; ++i) 
            m_clause.push_back(literal2expr(lits[i]));
        auto hint = status2proof_hint(st);
        m_on_clause(m_on_clause_ctx, hint, 0, nullptr, m_clause.size(), m_clause.data());
    }

    void solver::on_proof(unsigned n, literal const* lits, sat::status st) {
        if (!m_proof_out)
            return;
        flet<bool> _display_all_decls(m_display_all_decls, true);
        std::ostream& out = *m_proof_out;
        if (!visit_clause(out, n, lits))
            return;
        if (st.is_asserted()) 
            display_inferred(out, n, lits, status2proof_hint(st));
        else if (st.is_deleted()) 
            display_deleted(out, n, lits);        
        else if (st.is_redundant()) 
            display_inferred(out, n, lits, status2proof_hint(st));
        else if (st.is_input()) 
            display_assume(out, n, lits);
        else 
            UNREACHABLE();
        out.flush();
    }

    void solver::on_check(unsigned n, literal const* lits, sat::status st) {
        if (!s().get_config().m_smt_proof_check)
            return;
        m_clause.reset();
        for (unsigned i = 0; i < n; ++i) 
            m_clause.push_back(literal2expr(lits[i]));
        auto hint = status2proof_hint(st);
        if (st.is_asserted() || st.is_redundant())
            m_smt_proof_checker.infer(m_clause, hint);
        else if (st.is_deleted())
            m_smt_proof_checker.del(m_clause);
        else if (st.is_input())
            m_smt_proof_checker.assume(m_clause);
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
        expr_ref k(m);
        for (unsigned i = 0; i < n; ++i) {
            expr* e = bool_var2expr(lits[i].var());
            if (!e) {
                k = m.mk_const(symbol(lits[i].var()), m.mk_bool_sort());
                e = k;
            }
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

    void solver::display_inferred(std::ostream& out, unsigned n, literal const* lits, expr* proof_hint) {
        expr_ref hint(proof_hint, m);
        if (!hint)
            hint = m.mk_const(m_smt, m.mk_proof_sort()); 
        visit_expr(out, hint);
        display_hint(display_literals(out << "(infer", n, lits), hint) << ")\n";        
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

    app_ref solver::status2proof_hint(sat::status st) {
        if (st.is_sat()) 
            return app_ref(m.mk_const("rup", m.mk_proof_sort()), m); // provable by reverse unit propagation
        auto* h = reinterpret_cast<euf::th_proof_hint const*>(st.get_hint());
        if (!h)
            return app_ref(m);

        expr* e = h->get_hint(*this);
        if (e)
            return app_ref(to_app(e), m);

        return app_ref(m);        
    }

    std::ostream& solver::display_literals(std::ostream& out, unsigned n, literal const* lits) {
        expr_ref k(m);
        for (unsigned i = 0; i < n; ++i) {
            expr* e = bool_var2expr(lits[i].var());
            if (!e) {
                k = m.mk_const(symbol(lits[i].var()), m.mk_bool_sort());
                e = k;
            }
            SASSERT(e);
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
