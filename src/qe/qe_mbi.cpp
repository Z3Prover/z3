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
                if (m_shared.contains(c)) {
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
    // euf_arith_mbi

    struct euf_arith_mbi_plugin::is_atom_proc {
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

    struct euf_arith_mbi_plugin::is_arith_var_proc {
        ast_manager&    m;
        app_ref_vector& m_avars;
        app_ref_vector& m_proxies;
        arith_util      m_arith;
        obj_hashtable<expr> m_seen;
        is_arith_var_proc(app_ref_vector& avars, app_ref_vector& proxies):
            m(avars.m()), m_avars(avars), m_proxies(proxies), m_arith(m) {
        }
        void operator()(app* a) {
            if (is_arith_op(a) || a->get_family_id() == m.get_basic_family_id()) {
                return;
            }

            if (m_arith.is_int_real(a)) {
                m_avars.push_back(a);
                if (!m_seen.contains(a)) {
                    m_proxies.push_back(a);
                    m_seen.insert(a);
                }
            }
            for (expr* arg : *a) {
                if (is_app(arg) && !m_seen.contains(arg) && m_arith.is_int_real(arg)) {
                    m_proxies.push_back(to_app(arg));
                    m_seen.insert(arg);
                }
            }
        }
        bool is_arith_op(app* a) {
            return a->get_family_id() == m_arith.get_family_id();
        }
        void operator()(expr*) {}
    };

    void euf_arith_mbi_plugin::filter_private_arith(app_ref_vector& avars) {
        arith_util a(m);
        unsigned j = 0;
        obj_hashtable<func_decl> shared;
        for (func_decl* f : m_shared) shared.insert(f);
        for (unsigned i = 0; i < avars.size(); ++i) {
            app* v = avars.get(i);
            if (!shared.contains(v->get_decl()) && 
                v->get_family_id() != a.get_family_id()) {
                avars[j++] = v;
            }
        }
        avars.shrink(j);
    }

    euf_arith_mbi_plugin::euf_arith_mbi_plugin(solver* s, solver* sNot):
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

    void euf_arith_mbi_plugin::collect_atoms(expr_ref_vector const& fmls) {
        expr_fast_mark1 marks;
        is_atom_proc proc(m_atoms, m_atom_set);
        for (expr* e : fmls) {
            quick_for_each_expr(proc, marks, e);
        }
    }

    bool euf_arith_mbi_plugin::get_literals(model_ref& mdl, expr_ref_vector& lits) {
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
     * \brief extract arithmetical variables and arithmetical terms in shared positions.
     */
    app_ref_vector euf_arith_mbi_plugin::get_arith_vars(model_ref& mdl, expr_ref_vector& lits, app_ref_vector& proxies) {
        app_ref_vector avars(m); 
        is_arith_var_proc _proc(avars, proxies);
        for_each_expr(_proc, lits);
        return avars;
    }

    mbi_result euf_arith_mbi_plugin::operator()(expr_ref_vector& lits, model_ref& mdl) {
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

    void euf_arith_mbi_plugin::project(model_ref& mdl, expr_ref_vector& lits) {
        TRACE("qe", tout << lits << "\n" << *mdl << "\n";);
        TRACE("qe", tout << m_solver->get_assertions() << "\n";);

        // 0. saturation
        array_project_plugin arp(m);
        arp.saturate(*mdl, m_shared, lits);

        // . arithmetical variables - atomic and in purified positions
        app_ref_vector proxies(m);
        app_ref_vector avars = get_arith_vars(mdl, lits, proxies);
        TRACE("qe", tout << "vars: " << avars << "\nproxies: " << proxies << "\nlits: " << lits << "\n";);

        // . project private non-arithmetical variables from lits
        project_euf(mdl, lits, avars);

        // . Minimzie span between smallest and largest proxy variable.
        minimize_span(mdl, avars, proxies);

        // . Order arithmetical variables and purified positions
        order_avars(mdl, lits, avars, proxies);
        TRACE("qe", tout << "ordered: " << lits << "\n";);

        // . Perform arithmetical projection
        arith_project_plugin ap(m);
        ap.set_check_purified(false);
        auto defs = ap.project(*mdl.get(), avars, lits);
        TRACE("qe", tout << "aproject: " << lits << "\n";);

        // . Substitute solution into lits
        substitute(defs, lits);
        TRACE("qe", tout << "substitute: " << lits << "\n";);
        IF_VERBOSE(1, verbose_stream() << lits << "\n");
    }

    /**
     * \brief substitute solution to arithmetical variables into lits
     */
    void euf_arith_mbi_plugin::substitute(vector<def> const& defs, expr_ref_vector& lits) {
        for (auto const& def : defs) {
            expr_safe_replace rep(m);
            rep.insert(def.var, def.term);
            rep(lits);
        }
    }

    /**
     * \brief project private symbols.
     * - project with respect to shared symbols only.
     *   retains equalities that are independent of arithmetic
     * - project with respect to shared + arithmetic basic terms
     *   retains predicates that are projected by arithmetic 
     */
    void euf_arith_mbi_plugin::project_euf(model_ref& mdl, expr_ref_vector& lits, app_ref_vector& avars) {
        term_graph tg1(m), tg2(m);
        func_decl_ref_vector shared(m_shared);
        tg1.set_vars(shared, false);
        for (app* a : avars) shared.push_back(a->get_decl());
        tg2.set_vars(shared, false);
        tg1.add_lits(lits);
        tg2.add_lits(lits);
        lits.reset();
        lits.append(tg1.project(*mdl.get()));
        lits.append(tg2.project(*mdl.get()));
        TRACE("qe", tout << "project: " << lits << "\n";);                
    }

    vector<std::pair<rational, app*>> euf_arith_mbi_plugin::sort_proxies(model_ref& mdl, app_ref_vector const& proxies) {
        arith_util a(m);
        model_evaluator mev(*mdl.get());
        vector<std::pair<rational, app*>> vals;
        for (app* v : proxies) {
            rational val;
            expr_ref tmp = mev(v);
            VERIFY(a.is_numeral(tmp, val));
            vals.push_back(std::make_pair(val, v));
        }
        struct compare_first {
            bool operator()(std::pair<rational, app*> const& x,
                          std::pair<rational, app*> const& y) const {
                return x.first < y.first;
            }
        };
        // add offset ordering between proxies
        compare_first cmp;
        std::sort(vals.begin(), vals.end(), cmp);
        return vals;
    }

    void euf_arith_mbi_plugin::minimize_span(model_ref& mdl, app_ref_vector& avars, app_ref_vector const& proxies) {
#if 0
        arith_util a(m);
        opt::context opt(m);        
        expr_ref_vector fmls(m);
        m_solver->get_assertions(fmls);
        for (expr* l : fmls) opt.add_hard_constraint(l);
        vector<std::pair<rational, app*>> vals = sort_proxies(mdl, proxies);
        app_ref t(m);
        for (unsigned i = 1; i < vals.size(); ++i) {
            rational offset = vals[i].first - vals[i-1].first;
            expr* t1 = vals[i-1].second;
            expr* t2 = vals[i].second;
            if (offset.is_zero()) {
                t = m.mk_eq(t1, t2);
            }
            else {
                SASSERT(offset.is_pos());
                t = a.mk_lt(t1, t2);
            }
            opt.add_hard_constraint(t);
        }
        t = a.mk_sub(vals[0].second, vals.back().second);
        opt.add_objective(t, true);
        expr_ref_vector asms(m);
        VERIFY(l_true == opt.optimize(asms));
        opt.get_model(mdl);
        model_evaluator mev(*mdl.get());
        std::cout << mev(t) << "\n";
#endif
    }

    /**
     * \brief Order arithmetical variables:
     * 1. add literals that order the proxies according to the model.
     * 2. sort arithmetical terms, such that deepest terms are first.
     */
    void euf_arith_mbi_plugin::order_avars(model_ref& mdl, expr_ref_vector& lits, app_ref_vector& avars, app_ref_vector const& proxies) {
        arith_util a(m);
        model_evaluator mev(*mdl.get());
        vector<std::pair<rational, app*>> vals = sort_proxies(mdl, proxies);
        for (unsigned i = 1; i < vals.size(); ++i) {
            rational offset = vals[i].first - vals[i-1].first;
            expr* t1 = vals[i-1].second;
            expr* t2 = vals[i].second;
            if (offset.is_zero()) {
                lits.push_back(m.mk_eq(t1, t2));
            }
            else {
                expr_ref t(a.mk_add(t1, a.mk_numeral(offset, true)), m);
                lits.push_back(a.mk_le(t, t2));
            }
        }

        // filter out only private variables
        filter_private_arith(avars);

        // sort avars based on depth
        struct compare_depth {
            bool operator()(app* x, app* y) const {
                return 
                    (x->get_depth() > y->get_depth()) || 
                    (x->get_depth() == y->get_depth() && x->get_id() > y->get_id());
            }
        };
        compare_depth cmpd;
        std::sort(avars.c_ptr(), avars.c_ptr() + avars.size(), cmpd);
        TRACE("qe", tout << lits << "\navars:" << avars << "\n" << *mdl << "\n";);
    }

    void euf_arith_mbi_plugin::block(expr_ref_vector const& lits) {
        // want to rely only on atoms from original literals: collect_atoms(lits);
        expr_ref conj(mk_not(mk_and(lits)), m);
        //m_fmls.push_back(conj);
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

    lbool interpolator::vurtego(mbi_plugin& a, mbi_plugin& b, expr_ref& itp, model_ref &mdl) {
        /**
           Assumptions on mbi_plugin()
           Let local be assertions local to the plugin
           Let blocked be clauses added by blocked, kept separately from local
           mbi_plugin::check(lits, mdl, bool force_model):
              if lits.empty()  and mdl == nullptr then
                  if is_sat(local & blocked) then
                      return l_true, mbp of local, mdl of local & blocked
                  else
                      return l_false
              else if !lits.empty() then
                  if is_sat(local & mdl & blocked)
                      return l_true, lits, extension of mdl to local
                  else if is_sat(local & lits & blocked)
                      if (force_model) then
                        return l_false, core of model, nullptr
                      else
                        return l_true, mbp of local, mdl of local & blocked
                  else if !is_sat(local & lits) then
                      return l_false, mbp of local, nullptr
                  else if is_sat(local & lits) && !is_sat(local & lits & blocked)
                      MISSING CASE
                      MUST PRODUCE AN IMPLICANT OF LOCAL that is inconsistent with lits & blocked
                      in this case !is_sat(local & lits & mdl) and is_sat(mdl, blocked)
                          let mdl_blocked be lits of blocked that are true in mdl
                          return l_false, core of lits & mdl_blocked, nullptr

           mbi_plugin::block(phi): add phi to blocked

           probably should use the operator() instead of check.
           mbi_augment -- means consistent with lits but not with the mdl
           mbi_sat -- means consistent with lits and mdl

         */
        expr_ref_vector lits(m), itps(m);
        while (true) {
            // when lits.empty(), this picks an A-implicant consistent with B
            // when !lits.empty(), checks whether mdl of shared vocab extends to A
            bool force_model = !lits.empty();
            switch (a.check_ag(lits, mdl, force_model)) {
            case l_true:
                if (force_model)
                    // mdl is a model for a && b
                    return l_true;
                switch (b.check_ag(lits, mdl, false)) {
                case l_true:
                    /* can return true if know that b did not change
                       the model. For now, cycle back to A.  */
                    SASSERT(!lits.empty());
                    SASSERT(mdl);
                    break;
                case l_false:
                    // Force a different A-implicant
                    a.block(lits);
                    lits.reset();
                    mdl.reset();
                    break;
                case l_undef:
                    return l_undef;
                }
            case l_false:
                if (lits.empty()) {
                    // no more A-implicants, terminate
                    itp = mk_and(itps);
                    return l_false;
                }
                // force B to pick a different model or a different implicant
                b.block(lits);
                itps.push_back(mk_not(mk_and(lits)));
                lits.reset();
                mdl.reset();
                break;
            case l_undef:
                return l_undef;
            }
        }
    }

};
