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

namespace euf {

    void solver::init_drat() {
        if (!m_drat_initialized) {
            get_drat().add_theory(get_id(), symbol("euf"));
            get_drat().add_theory(m.get_basic_family_id(), symbol("bool"));
        }
        m_drat_initialized = true;
    }

    void solver::drat_log_expr1(expr* e) {
        if (is_app(e)) {
            app* a = to_app(e);
            drat_log_decl(a->get_decl());
            std::stringstream strm;
            strm << mk_ismt2_func(a->get_decl(), m);
            if (a->get_num_parameters() == 0)
                get_drat().def_begin('e', e->get_id(), strm.str());
            else {
                get_drat().def_begin('e', e->get_id(), strm.str());
            }
            for (expr* arg : *a)
                get_drat().def_add_arg(arg->get_id());
            get_drat().def_end();
            m_drat_asts.insert(e);
            push(insert_obj_trail<ast>(m_drat_asts, e));
        }
        else {
            IF_VERBOSE(0, verbose_stream() << "logging binders is TBD\n");
        }
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
            if (m_drat_todo.size() != sz)
                continue;
            drat_log_expr1(e);
            m_drat_todo.pop_back();                   
        }
    }

    void solver::drat_bool_def(sat::bool_var v, expr* e) {
        if (!use_drat())
            return;
        drat_log_expr(e);
        get_drat().bool_def(v, e->get_id());
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
        get_drat().def_begin('f', f->get_decl_id(), strm.str());
        get_drat().def_end();
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
        get_drat().add(lits, sat::status::th(m_is_redundant, jst.ext().get_id()));
    }

    void solver::drat_eq_def(literal lit, expr* eq) {
        expr *a = nullptr, *b = nullptr;
        VERIFY(m.is_eq(eq, a, b));
        get_drat().def_begin('e', eq->get_id(), std::string("="));
        get_drat().def_add_arg(a->get_id());
        get_drat().def_add_arg(b->get_id());
        get_drat().def_end();
        get_drat().bool_def(lit.var(), eq->get_id());
    }

}
