/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    qe_mbi.cpp

Abstract:

    Model-based interpolation utilities

Author:

    Nikolaj Bjorner (nbjorner), Arie Gurfinkel 2018-6-8

Revision History:


Notes:

  Reduction into:
   T_EUF
   T_LIRA

  Other theories: DT, ARR reduced to EUF
  BV is EUF/Boolean.


--*/

#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/arith_decl_plugin.h"
#include "model/model_evaluator.h"
#include "solver/solver.h"
#include "qe/qe_mbi.h"
#include "qe/qe_term_graph.h"
#include "qe/qe_arith.h"
#include "qe/qe_arrays.h"


namespace qe {

    lbool mbi_plugin::check(expr_ref_vector& lits, model_ref& mdl) {
        while (true) {
            switch ((*this)(lits, mdl)) {
            case mbi_sat:
                return l_true;
            case mbi_unsat:
                return l_false;
            case mbi_undef:
                return l_undef;
            case mbi_augment:
                break;
            }
        }
    }

    bool mbi_plugin::is_shared(func_decl* f) {
        return f->get_family_id() != null_family_id || m_shared.contains(f);
    }

    bool mbi_plugin::is_shared(expr* e) {
        e = m_rep ? m_rep(e) : e;
        if (!is_app(e)) return false;
        unsigned id = e->get_id();
        m_is_shared.reserve(id + 1, l_undef);
        lbool r = m_is_shared[id];
        if (r != l_undef) return r == l_true;
        app* a = to_app(e);
        bool all_shared = is_shared(a->get_decl());
        for (expr* arg : *a) {
            if (!all_shared)
                break;
            if (!is_shared(arg)) 
                all_shared = false;
        }
        m_is_shared[id] = all_shared ? l_true : l_false;
        return all_shared;
    }


    // -------------------------------
    // prop_mbi

    prop_mbi_plugin::prop_mbi_plugin(solver* s): mbi_plugin(s->get_manager()), m_solver(s) {}

    // sketch of propositional

    mbi_result prop_mbi_plugin::operator()(expr_ref_vector& lits, model_ref& mdl)  {
        lbool r = m_solver->check_sat(lits);
        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            return mbi_unsat;
        case l_true:
            m_solver->get_model(mdl);
            lits.reset();
            for (unsigned i = 0, sz = mdl->get_num_constants(); i < sz; ++i) {
                func_decl* c = mdl->get_constant(i);
                if (is_shared(c)) {
                    if (m.is_true(mdl->get_const_interp(c))) {
                        lits.push_back(m.mk_const(c));
                    }
                    else if (m.is_false(mdl->get_const_interp(c))) {
                        lits.push_back(m.mk_not(m.mk_const(c)));
                    }
                }
            }
            return mbi_sat;
        default:
            return mbi_undef;
        }
    }

    void prop_mbi_plugin::block(expr_ref_vector const& lits) {
        m_solver->assert_expr(mk_not(mk_and(lits)));
    }

    // -------------------------------
    // uflia_mbi

    struct uflia_mbi::is_atom_proc {
        ast_manager&         m;
        expr_ref_vector&     m_atoms;
        obj_hashtable<expr>& m_atom_set;

        is_atom_proc(expr_ref_vector& atoms, obj_hashtable<expr>& atom_set): 
            m(atoms.m()), m_atoms(atoms), m_atom_set(atom_set) {}

        void operator()(app* a) {
            if (m_atom_set.contains(a)) {
                // continue
            }
            else if (m.is_eq(a)) {
                m_atoms.push_back(a);
                m_atom_set.insert(a);
            }
            else if (m.is_bool(a) && a->get_family_id() != m.get_basic_family_id()) {
                m_atoms.push_back(a);
                m_atom_set.insert(a);
            }
        }
        void operator()(expr*) {}
    };

    uflia_mbi::uflia_mbi(solver* s, solver* sNot):
        mbi_plugin(s->get_manager()),
        m_atoms(m),
        m_fmls(m),
        m_solver(s),
        m_dual_solver(sNot) {
        params_ref p;
        p.set_bool("core.minimize", true);
        m_solver->updt_params(p);
        m_dual_solver->updt_params(p);
        m_solver->get_assertions(m_fmls);
        collect_atoms(m_fmls);
    }

    void uflia_mbi::collect_atoms(expr_ref_vector const& fmls) {
        expr_fast_mark1 marks;
        is_atom_proc proc(m_atoms, m_atom_set);
        for (expr* e : fmls) {
            quick_for_each_expr(proc, marks, e);
        }
    }

    bool uflia_mbi::get_literals(model_ref& mdl, expr_ref_vector& lits) {
        lits.reset();
        for (expr* e : m_atoms) {
            if (mdl->is_true(e)) {
                lits.push_back(e);
            }
            else if (mdl->is_false(e)) {
                lits.push_back(m.mk_not(e));
            }
        }
        TRACE("qe", tout << "atoms from model: " << lits << "\n";);
        solver_ref dual = m_dual_solver->translate(m, m_dual_solver->get_params());
        dual->assert_expr(mk_not(mk_and(m_fmls)));
        lbool r = dual->check_sat(lits);
        TRACE("qe", dual->display(tout << "dual result " << r << "\n"););
        if (l_false == r) {
            // use the dual solver to find a 'small' implicant
            lits.reset();
            dual->get_unsat_core(lits);
            return true;
        }
        else {
            return false;
        }
    }


    /** 
     * \brief A subterm is an arithmetic variable if:
     *  1. it is not shared.
     *  2. it occurs under an arithmetic operation.
     *  3. it is not an arithmetic expression.
     * 
     *  The result is ordered using deepest term first.
     */
    app_ref_vector uflia_mbi::get_arith_vars(expr_ref_vector& lits) {
        app_ref_vector avars(m); 
        svector<bool> seen;
        arith_util a(m);
        for (expr* e : subterms(lits)) {
            if ((m.is_eq(e) && a.is_int_real(to_app(e)->get_arg(0))) || a.is_arith_expr(e)) {
                for (expr* arg : *to_app(e)) {
                    unsigned id = arg->get_id();
                    seen.reserve(id + 1, false);
                    if (is_app(arg) && !m.is_eq(arg) && !a.is_arith_expr(arg) && !is_shared(arg) && !seen[id]) {
                        seen[id] = true;
                        avars.push_back(to_app(arg));
                    }
                }
            }
        }
        order_avars(avars);
        TRACE("qe", tout << "vars: " << avars << "\n";);
        return avars;
    }

    vector<def> uflia_mbi::arith_project(model_ref& mdl, app_ref_vector& avars, expr_ref_vector& lits) {
        arith_project_plugin ap(m);
        ap.set_check_purified(false);
        return ap.project(*mdl.get(), avars, lits);
    }

    mbi_result uflia_mbi::operator()(expr_ref_vector& lits, model_ref& mdl) {
        lbool r = m_solver->check_sat(lits);

        switch (r) {
        case l_false:
            lits.reset();
            m_solver->get_unsat_core(lits);
            TRACE("qe", tout << "unsat core: " << lits << "\n";);
            // optionally minimize core using superposition.
            return mbi_unsat;
        case l_true: 
            m_solver->get_model(mdl);
            if (!get_literals(mdl, lits)) {
                return mbi_undef;
            }
            project(mdl, lits);
            return mbi_sat;
        default:
            // TBD: if not running solver to completion, then:
            // 1. extract unit literals from m_solver.
            // 2. run a cc over the units
            // 3. extract equalities or other assignments over the congruence classes
            // 4. ensure that at least some progress is made over original lits.
            return mbi_undef;
        }
    }

    /**
       \brief main projection routine
    */
    void uflia_mbi::project(model_ref& mdl, expr_ref_vector& lits) {
        TRACE("qe", 
              tout << lits << "\n" << *mdl << "\n";
              tout << m_solver->get_assertions() << "\n";);

        add_dcert(mdl, lits);
        auto avars = get_arith_vars(lits);
        auto defs = arith_project(mdl, avars, lits);
        substitute(defs, lits);
        project_euf(mdl, lits);
    }

    /**
       \brief add difference certificates to formula.
       
       First version just uses an Ackerman reduction.

       It should be replaced by DCert.
    */
    void uflia_mbi::add_dcert(model_ref& mdl, expr_ref_vector& lits) {        
        term_graph tg(m);
        func_decl_ref_vector shared(m_shared_trail);
        tg.set_vars(shared, false);
        tg.add_lits(lits);
        lits.append(tg.get_ackerman_disequalities());
        TRACE("qe", tout << "project: " << lits << "\n";);                
    }

    /**
     * \brief substitute solution to arithmetical variables into lits
     */
    void uflia_mbi::substitute(vector<def> const& defs, expr_ref_vector& lits) {
        for (auto const& def : defs) {
            expr_safe_replace rep(m);
            rep.insert(def.var, def.term);
            rep(lits);
        }
        TRACE("qe", tout << "substitute: " << lits << "\n";);
        IF_VERBOSE(1, verbose_stream() << lits << "\n");
    }

    /**
     * \brief project private symbols.
     */
    void uflia_mbi::project_euf(model_ref& mdl, expr_ref_vector& lits) {
        term_graph tg(m);
        func_decl_ref_vector shared(m_shared_trail);
        tg.set_vars(shared, false);
        tg.add_lits(lits);
        lits.reset();
        lits.append(tg.project(*mdl.get()));
        TRACE("qe", tout << "project: " << lits << "\n";);                
    }

    /**
     * \brief Order arithmetical variables:
     * sort arithmetical terms, such that deepest terms are first.
     */
    void uflia_mbi::order_avars(app_ref_vector& avars) {

        // sort avars based on depth
        std::function<bool(app*, app*)> compare_depth = 
            [](app* x, app* y) {
                return 
                    (x->get_depth() > y->get_depth()) || 
                    (x->get_depth() == y->get_depth() && x->get_id() > y->get_id());
        };
        std::sort(avars.c_ptr(), avars.c_ptr() + avars.size(), compare_depth);
        TRACE("qe", tout << "avars:" << avars << "\n";);
    }

    void uflia_mbi::block(expr_ref_vector const& lits) {
        // want to rely only on atoms from original literals: collect_atoms(lits);
        expr_ref conj(mk_not(mk_and(lits)), m);
        TRACE("qe", tout << "block " << lits << "\n";);
        m_solver->assert_expr(conj);
    }


    /** --------------------------------------------------------------
     * ping-pong interpolation of Gurfinkel & Vizel
     * compute a binary interpolant.
     */
    lbool interpolator::pingpong(mbi_plugin& a, mbi_plugin& b, expr_ref& itp) {
        model_ref mdl;
        expr_ref_vector lits(m);
        bool turn = true;
        vector<expr_ref_vector> itps, blocks;
        itps.push_back(expr_ref_vector(m));
        itps.push_back(expr_ref_vector(m));
        blocks.push_back(expr_ref_vector(m));
        blocks.push_back(expr_ref_vector(m));
        mbi_result last_res = mbi_undef;
        bool_rewriter rw(m);
        while (true) {
            auto* t1 = turn ? &a : &b;
            auto* t2 = turn ? &b : &a;
            mbi_result next_res = (*t1)(lits, mdl);
            switch (next_res) {
            case mbi_sat:
                if (last_res == mbi_sat) {
                    itp = nullptr;
                    return l_true;
                }
                TRACE("mbi", tout << "new lits " << lits << "\n";);
                break; // continue
            case mbi_unsat: {
                if (lits.empty()) {
                    // TBD, either a => itp and itp => !b
                    // or          b => itp and itp => !a
                    itp = mk_and(itps[!turn]);
                    return l_false;
                }
                t2->block(lits);
                expr_ref lemma(mk_not(mk_and(lits)));
                TRACE("mbi", tout << lemma << "\n";);
                blocks[turn].push_back(lemma);
                itp = m.mk_implies(mk_and(blocks[!turn]), lemma);
                // TBD: compute closure over variables not in vars
                itps[turn].push_back(itp);
                lits.reset();  // or find a prefix of lits?
                break;
            }
            case mbi_augment:
                break;
            case mbi_undef:
                return l_undef;
            }
            turn = !turn;
            last_res = next_res;
        }
    }

    /**
     * One-sided pogo creates clausal interpolants.
     * It creates a set of consequences of b that are inconsistent with a.
     */
    lbool interpolator::pogo(mbi_plugin& a, mbi_plugin& b, expr_ref& itp) {
        expr_ref_vector lits(m), itps(m);
        while (true) {
            model_ref mdl;
            lits.reset();
            switch (a.check(lits, mdl)) {
            case l_true:
                switch (b.check(lits, mdl)) {
                case l_true:
                    return l_true;
                case l_false:
                    a.block(lits);
                    itps.push_back(mk_not(mk_and(lits)));
                    break;
                case l_undef:
                    return l_undef;
                }
                break;
            case l_false:
                itp = mk_and(itps);
                return l_false;
            case l_undef:
                return l_undef;
            }
        }
    }

};
