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

    void solver::init_drat() {
        if (!m_drat_initialized) {
            get_drat().add_theory(get_id(), symbol("euf"));
            get_drat().add_theory(m.get_basic_family_id(), symbol("bool"));
        }
        m_drat_initialized = true;
    }

    void solver::def_add_arg(unsigned arg) {
        auto* out = get_drat().out();
        if (out)
            (*out) << " " << arg;
    }

    void solver::def_end() {
        auto* out = get_drat().out();
        if (out)
            (*out) << " 0\n";
    }

    void solver::def_begin(char id, unsigned n, std::string const& name) {
        auto* out = get_drat().out();
        if (out)
            (*out) << id << " " << n << " " << name;
    }

    void solver::bool_def(bool_var v, unsigned n) {
        auto* out = get_drat().out();
        if (out)
            (*out) << "b " << v << " " << n << " 0\n";
    }


    void solver::drat_log_params(func_decl* f) {
        for (unsigned i = f->get_num_parameters(); i-- > 0; ) {
            auto const& p = f->get_parameter(i);
            if (!p.is_ast()) 
                continue;
            ast* a = p.get_ast();
            if (is_func_decl(a))
                drat_log_decl(to_func_decl(a));
        }
    }
    
    void solver::drat_log_expr1(expr* e) {
        if (is_app(e)) {
            app* a = to_app(e);
            drat_log_params(a->get_decl());
            drat_log_decl(a->get_decl());
            std::stringstream strm;
            strm << mk_ismt2_func(a->get_decl(), m);
            def_begin('e', e->get_id(), strm.str());
            for (expr* arg : *a)
                def_add_arg(arg->get_id());
            def_end();
        }
        else if (is_var(e)) {
            var* v = to_var(e);
            def_begin('v', v->get_id(), "" + mk_pp(e->get_sort(), m));
            def_add_arg(v->get_idx());
            def_end();
        }
        else if (is_quantifier(e)) {
            quantifier* q = to_quantifier(e);
            std::stringstream strm;           
            strm << "(" << (is_forall(q) ? "forall" : (is_exists(q) ? "exists" : "lambda"));
            for (unsigned i = 0; i < q->get_num_decls(); ++i) 
                strm << " (" << q->get_decl_name(i) << " " << mk_pp(q->get_decl_sort(i), m) << ")";            
            strm << ")";
            def_begin('q', q->get_id(), strm.str());
            def_add_arg(q->get_expr()->get_id());
            def_end();
        }
        else 
            UNREACHABLE();
        m_drat_asts.insert(e);
        push(insert_obj_trail<ast>(m_drat_asts, e));
    }

    void solver::drat_log_expr(expr* e) {
        if (m_drat_asts.contains(e))
            return;
        ptr_vector<expr>::scoped_stack _sc(m_drat_todo);
        m_drat_todo.push_back(e);
        while (!m_drat_todo.empty()) {
            e = m_drat_todo.back();
            unsigned sz = m_drat_todo.size();
            if (is_app(e)) 
                for (expr* arg : *to_app(e))
                    if (!m_drat_asts.contains(arg))
                        m_drat_todo.push_back(arg);
            if (is_quantifier(e)) {
                expr* arg = to_quantifier(e)->get_expr();
                if (!m_drat_asts.contains(arg))
                    m_drat_todo.push_back(arg);                
            }                
            if (m_drat_todo.size() != sz)
                continue;
            if (!m_drat_asts.contains(e))
                drat_log_expr1(e);
            m_drat_todo.pop_back();                   
        }
    }

    void solver::drat_bool_def(sat::bool_var v, expr* e) {
        if (!use_drat())
            return;
        drat_log_expr(e);
        bool_def(v, e->get_id());
    }


    void solver::drat_log_decl(func_decl* f) {
        if (f->get_family_id() != null_family_id) 
            return;
        if (m_drat_asts.contains(f))
            return;
        m_drat_asts.insert(f);
        push(insert_obj_trail< ast>(m_drat_asts, f));
        std::ostringstream strm;
        smt2_pp_environment_dbg env(m);
        ast_smt2_pp(strm, f, env);
        def_begin('f', f->get_small_id(), strm.str());
        def_end();
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

    void solver::log_justification(literal l, th_explain const& jst) {
        literal_vector lits;
        unsigned nv = s().num_vars();
        expr_ref_vector eqs(m);
        auto add_lit = [&](enode_pair const& eq) {
            ++nv;
            literal lit(nv, false);
            eqs.push_back(m.mk_eq(eq.first->get_expr(), eq.second->get_expr()));
            drat_eq_def(lit, eqs.back());            
            return lit;
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
    }

    void solver::drat_eq_def(literal lit, expr* eq) {
        expr *a = nullptr, *b = nullptr;
        VERIFY(m.is_eq(eq, a, b));
        drat_log_expr(a);
        drat_log_expr(b);
        def_begin('e', eq->get_id(), std::string("="));
        def_add_arg(a->get_id());
        def_add_arg(b->get_id());
        def_end();
        bool_def(lit.var(), eq->get_id());
    }

    void solver::on_clause(unsigned n, literal const* lits, sat::status st) {
        if (!get_config().m_lemmas2console) 
            return;
        if (!st.is_redundant() && !st.is_asserted()) 
            return;

        
        if (!visit_clause(n, lits))
            return;

        std::function<symbol(int)> ppth = [&](int th) {
            return m.get_family_name(th);
        };
        if (!st.is_sat())
            std::cout << "; " << sat::status_pp(st, ppth) << "\n";

        display_clause(n, lits);
    }


    bool solver::visit_clause(unsigned n, literal const* lits) {
        for (unsigned i = 0; i < n; ++i) {
            expr* e = bool_var2expr(lits[i].var());
            if (!e)
                return false;
            visit_expr(e);
        }
        return true;
    }

    void solver::display_clause(unsigned n, literal const* lits) {
        std::cout << "(assert (or";
        for (unsigned i = 0; i < n; ++i) {
            expr* e = bool_var2expr(lits[i].var());
            if (lits[i].sign())
                m_clause_visitor.display_expr_def(std::cout << " (not ", e) << ")";
            else
                m_clause_visitor.display_expr_def(std::cout << " ", e);
        }
        std::cout << "))\n";
    }

    void solver::visit_expr(expr* e) {
        m_clause_visitor.collect(e);
        m_clause_visitor.display_skolem_decls(std::cout);
        m_clause_visitor.define_expr(std::cout, e);
    }

    void solver::display_expr(expr* e) {
        m_clause_visitor.display_expr_def(std::cout, e);
    }

}
