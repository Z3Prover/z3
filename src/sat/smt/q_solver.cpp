/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    a_solver.cpp

Abstract:

    Quantifier solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/
#pragma once

#include "ast/rewriter/var_subst.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"


namespace q {
    
    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, ctx.get_manager().get_family_id(name())),
        m_mbqi(ctx, *this)
    {}

    void solver::asserted(sat::literal l) {
        expr* e = bool_var2expr(l.var());
        SASSERT(is_forall(e) || is_exists(e));
        if (l.sign() == is_forall(e)) {
            // existential force
            add_clause(~l, skolemize(to_quantifier(e)));
        }
        else {
            // universal force
//          add_clause(~l, uskolemize(to_quantifier(e)));
            ctx.push_vec(m_universal, l);
        }
    }

    sat::check_result solver::check() {
        switch (m_mbqi()) {
        case l_true: return sat::check_result::CR_DONE;
        case l_false: return sat::check_result::CR_CONTINUE;
        case l_undef: return sat::check_result::CR_GIVEUP;            
        }
        return sat::check_result::CR_GIVEUP;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("quantifier inst", m_stats.m_num_inst);
    }

    euf::th_solver* solver::clone(sat::solver* s, euf::solver& ctx) {
        return alloc(solver, ctx);
    }

    bool solver::unit_propagate() {
        return false;
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        SASSERT(is_forall(n->get_expr()) || is_exists(n->get_expr()));
        auto v = euf::th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);        
        return v;
    }

    sat::literal solver::skolemize(quantifier* q) {
        sat::literal sk;
        if (m_skolems.find(q, sk))
            return sk;        
        expr_ref tmp(m);
        expr_ref_vector vars(m);
        unsigned sz = q->get_num_decls();
        vars.resize(sz, nullptr);
        for (unsigned i = 0; i < sz; ++i) {
            vars[i] = m.mk_fresh_const(q->get_decl_name(i), q->get_decl_sort(i));    
        }
        var_subst subst(m);
        expr_ref body = subst(q->get_expr(), vars.size(), vars.c_ptr());
        ctx.get_rewriter()(body);
        sk = b_internalize(body);
        if (is_forall(q))
            sk.neg();
        m_skolems.insert(q, sk);
        // TODO find a different way than rely on backtrack stack, e,g., save body/q in ref-counted stack
        ctx.push(insert_map<euf::solver, skolem_table, quantifier*>(m_skolems, q));
        return sk;
    }

    /*
    * Find initial values to instantiate quantifier with so to make it as hard as possible for solver
    * to find values to free variables. 
    */
    sat::literal solver::uskolemize(quantifier* q) {
        NOT_IMPLEMENTED_YET();
        return sat::null_literal;
    }

    void solver::init_search() {
        m_mbqi.init_search();
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) {
        SASSERT(is_forall(e) || is_exists(e));
        sat::bool_var v = ctx.get_si().add_bool_var(e);
        sat::literal lit = ctx.attach_lit(sat::literal(v, sign), e);
        mk_var(ctx.get_egraph().find(e));
        return lit;
    }
}
