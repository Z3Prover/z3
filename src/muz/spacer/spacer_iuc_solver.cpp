/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_iuc_solver.cpp

Abstract:

   A solver that produces interpolated unsat cores (IUCs)

Author:

    Arie Gurfinkel

Notes:

--*/
#include"muz/spacer/spacer_iuc_solver.h"
#include"ast/ast.h"
#include"muz/spacer/spacer_util.h"
#include"ast/proofs/proof_utils.h"
#include"muz/spacer/spacer_farkas_learner.h"
#include"ast/rewriter/expr_replacer.h"
#include"muz/spacer/spacer_unsat_core_learner.h"
#include"muz/spacer/spacer_unsat_core_plugin.h"
#include "muz/spacer/spacer_iuc_proof.h"

namespace spacer {
void iuc_solver::push ()
{
    m_defs.push_back (def_manager (*this));
    m_solver.push ();
}

void iuc_solver::pop (unsigned n)
{
    m_solver.pop (n);
    unsigned lvl = m_defs.size ();
    SASSERT (n <= lvl);
    unsigned new_lvl = lvl-n;
    while (m_defs.size() > new_lvl) {
        m_num_proxies -= m_defs.back ().m_defs.size ();
        m_defs.pop_back ();
    }
}

app* iuc_solver::fresh_proxy ()
{
    if (m_num_proxies == m_proxies.size()) {
        std::stringstream name;
        name << "spacer_proxy!" << m_proxies.size ();
        app_ref res(m);
        res = m.mk_const (symbol (name.str ().c_str ()),
                          m.mk_bool_sort ());
        m_proxies.push_back (res);

        // -- add the new proxy to proxy eliminator
        proof_ref pr(m);
        pr = m.mk_asserted (m.mk_true ());
        m_elim_proxies_sub.insert (res, m.mk_true (), pr);

    }
    return m_proxies.get (m_num_proxies++);
}

app* iuc_solver::mk_proxy (expr *v)
{
    {
        expr *e = v;
        m.is_not (v, e);
        if (is_uninterp_const(e)) { return to_app(v); }
    }

    def_manager &def = m_defs.size () > 0 ? m_defs.back () : m_base_defs;
    return def.mk_proxy (v);
}

bool iuc_solver::mk_proxies (expr_ref_vector &v, unsigned from)
{
    bool dirty = false;
    for (unsigned i = from, sz = v.size(); i < sz; ++i) {
        app *p = mk_proxy (v.get (i));
        dirty |= (v.get (i) != p);
        v[i] = p;
    }
    return dirty;
}

void iuc_solver::push_bg (expr *e)
{
    if (m_assumptions.size () > m_first_assumption)
    { m_assumptions.shrink(m_first_assumption); }
    m_assumptions.push_back (e);
    m_first_assumption = m_assumptions.size ();
}

void iuc_solver::pop_bg (unsigned n)
{
    if (n == 0) { return; }

    if (m_assumptions.size () > m_first_assumption)
    { m_assumptions.shrink(m_first_assumption); }
    m_first_assumption = m_first_assumption > n ? m_first_assumption - n : 0;
    m_assumptions.shrink (m_first_assumption);
}

unsigned iuc_solver::get_num_bg () {return m_first_assumption;}

lbool iuc_solver::check_sat (unsigned num_assumptions, expr * const *assumptions)
{
    // -- remove any old assumptions
    if (m_assumptions.size () > m_first_assumption)
    { m_assumptions.shrink(m_first_assumption); }

    // -- replace theory literals in background assumptions with proxies
    mk_proxies (m_assumptions);
    // -- in case mk_proxies added new literals, they are all background
    m_first_assumption = m_assumptions.size ();

    m_assumptions.append (num_assumptions, assumptions);
    m_is_proxied = mk_proxies (m_assumptions, m_first_assumption);

    lbool res;
    res = m_solver.check_sat (m_assumptions.size (), m_assumptions.c_ptr ());
    set_status (res);
    return res;
}


app* iuc_solver::def_manager::mk_proxy (expr *v)
{
    app* r;
    if (m_expr2proxy.find(v, r)) { return r; }

    ast_manager &m = m_parent.m;
    app_ref proxy(m);
    app_ref def(m);
    proxy = m_parent.fresh_proxy ();
    def = m.mk_or (m.mk_not (proxy), v);
    m_defs.push_back (def);
    m_expr2proxy.insert (v, proxy);
    m_proxy2def.insert (proxy, def);

    m_parent.assert_expr (def.get ());
    return proxy;
}

bool iuc_solver::def_manager::is_proxy (app *k, app_ref &def)
{
    app *r = nullptr;
    bool found = m_proxy2def.find (k, r);
    def = r;
    return found;
}

void iuc_solver::def_manager::reset ()
{
    m_expr2proxy.reset ();
    m_proxy2def.reset ();
    m_defs.reset ();
}

bool iuc_solver::def_manager::is_proxy_def (expr *v)
{
    // XXX This might not be the most robust way to check
    return m_defs.contains (v);
}

bool iuc_solver::is_proxy(expr *e, app_ref &def)
{
    if (!is_uninterp_const(e)) { return false; }

    app *a = to_app (e);

    for (int i = m_defs.size (); i > 0; --i)
        if (m_defs[i-1].is_proxy (a, def))
        { return true; }

    if (m_base_defs.is_proxy (a, def))
    { return true; }

    return false;
}

void iuc_solver::collect_statistics (statistics &st) const
{
    m_solver.collect_statistics (st);
    st.update ("time.iuc_solver.iuc_core", m_iuc_watch.get_seconds ());
}

void iuc_solver::reset_statistics ()
{
    m_iuc_watch.reset ();
}

void iuc_solver::get_unsat_core (ptr_vector<expr> &core)
{
    m_solver.get_unsat_core (core);
    undo_proxies_in_core (core);
}
void iuc_solver::undo_proxies_in_core (ptr_vector<expr> &r)
{
    app_ref e(m);
    expr_fast_mark1 bg;
    for (unsigned i = 0; i < m_first_assumption; ++i)
    { bg.mark(m_assumptions.get(i)); }

    // expand proxies
    unsigned j = 0;
    for (unsigned i = 0, sz = r.size(); i < sz; ++i) {
        // skip background assumptions
        if (bg.is_marked(r[i])) { continue; }

        // -- undo proxies, but only if they were introduced in check_sat
        if (m_is_proxied && is_proxy(r[i], e)) {
            SASSERT (m.is_or (e));
            r[j] = e->get_arg (1);
        } else if (i != j) { r[j] = r[i]; }
        j++;
    }
    r.shrink (j);
}

void iuc_solver::undo_proxies (expr_ref_vector &r)
{
    app_ref e(m);
    // expand proxies
    for (unsigned i = 0, sz = r.size (); i < sz; ++i)
        if (is_proxy(r.get(i), e)) {
            SASSERT (m.is_or (e));
            r[i] = e->get_arg (1);
        }
}

void iuc_solver::get_unsat_core (expr_ref_vector &_core)
{
    ptr_vector<expr> core;
    get_unsat_core (core);
    _core.append (core.size (), core.c_ptr ());
}

void iuc_solver::elim_proxies (expr_ref_vector &v)
{
    expr_ref f = mk_and (v);
    scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer (m);
    rep->set_substitution (&m_elim_proxies_sub);
    (*rep) (f);
    v.reset ();
    flatten_and (f, v);
}

void iuc_solver::get_iuc(expr_ref_vector &core)
{
    scoped_watch _t_ (m_iuc_watch);

    typedef obj_hashtable<expr> expr_set;
    expr_set core_lits;
    for (unsigned i = m_first_assumption, sz = m_assumptions.size(); i < sz; ++i) {
        expr *a = m_assumptions.get (i);
        app_ref def(m);
        if (is_proxy(a, def)) { core_lits.insert(def.get()); }
        core_lits.insert (a);
    }

    if (m_iuc == 0) {
        // ORIGINAL PDR CODE
        // AG: deprecated
        proof_ref pr(m);
        pr = get_proof ();

        farkas_learner learner_old;
        learner_old.set_split_literals(m_split_literals);

        learner_old.get_lemmas (pr, core_lits, core);
        elim_proxies (core);
        simplify_bounds (core); // XXX potentially redundant
    }
    else {
        // NEW IUC
        proof_ref res(get_proof(), m);

        // -- old hypothesis reducer while the new one is broken
        if (m_old_hyp_reducer) {
            // AG: deprecated
            // pre-process proof in order to get a proof which is
            // better suited for unsat-core-extraction
            if (m_print_farkas_stats) {
                iuc_proof iuc_before(m, res.get(), core_lits);
                verbose_stream() << "\nOld reduce_hypotheses. Before:";
                iuc_before.dump_farkas_stats();
            }

            proof_utils::reduce_hypotheses(res);
            proof_utils::permute_unit_resolution(res);

            if (m_print_farkas_stats) {
                iuc_proof iuc_after(m, res.get(), core_lits);
                verbose_stream() << "Old reduce_hypothesis. After:";
                iuc_after.dump_farkas_stats();
            }
        }
        // -- new hypothesis reducer
        else
        {
            // pre-process proof for better iuc extraction
            if (m_print_farkas_stats) {
                iuc_proof iuc_before(m, res.get(), core_lits);
                verbose_stream() << "\n New hypothesis_reducer. Before:";
                iuc_before.dump_farkas_stats();
            }

            theory_axiom_reducer ta_reducer(m);
            proof_ref pr1(ta_reducer.reduce (res.get()), m);

            hypothesis_reducer hyp_reducer(m);
            proof_ref pr2(hyp_reducer.reduce(pr1), m);

            res = pr2;

            if (m_print_farkas_stats) {
                iuc_proof iuc_after(m, res.get(), core_lits);
                verbose_stream() << "New hypothesis_reducer. After:";
                iuc_after.dump_farkas_stats();
            }
        }

        iuc_proof iuc_pf(m, res, core_lits);

        unsat_core_learner learner(m, iuc_pf);

        // -- register iuc plugins
        if (m_iuc_arith == 0 || m_iuc_arith == 1) {
            unsat_core_plugin_farkas_lemma* plugin =
                alloc(unsat_core_plugin_farkas_lemma,
                      learner, m_split_literals,
                      (m_iuc_arith == 1) /* use constants from A */);
            learner.register_plugin(plugin);
        }
        else if (m_iuc_arith == 2) {
            SASSERT(false && "Broken");
            unsat_core_plugin_farkas_lemma_optimized* plugin =
                alloc(unsat_core_plugin_farkas_lemma_optimized, learner, m);
            learner.register_plugin(plugin);
        }
        else if(m_iuc_arith == 3) {
            unsat_core_plugin_farkas_lemma_bounded* plugin =
                alloc(unsat_core_plugin_farkas_lemma_bounded, learner, m);
            learner.register_plugin(plugin);
        }
        else {
            UNREACHABLE();
        }

        if (m_iuc == 1) {
            // -- iuc based on the lowest cut in the proof
            unsat_core_plugin_lemma* plugin =
                alloc(unsat_core_plugin_lemma, learner);
            learner.register_plugin(plugin);
        }
        else if (m_iuc == 2) {
            // -- iuc based on the smallest cut in the proof
            unsat_core_plugin_min_cut* plugin =
                alloc(unsat_core_plugin_min_cut, learner, m);
            learner.register_plugin(plugin);
        }
        else {
            UNREACHABLE();
        }

        // compute interpolating unsat core
        learner.compute_unsat_core(core);

        elim_proxies (core);
        // AG: this should be taken care of by minimizing the iuc cut
        simplify_bounds (core);
    }

    IF_VERBOSE(2,
               verbose_stream () << "IUC Core:\n"
               << mk_and(core) << "\n";);
}

void iuc_solver::refresh ()
{
    // only refresh in non-pushed state
    SASSERT (m_defs.size () == 0);
    expr_ref_vector assertions (m);
    for (unsigned i = 0, e = m_solver.get_num_assertions(); i < e; ++i) {
        expr* a = m_solver.get_assertion (i);
        if (!m_base_defs.is_proxy_def(a)) { assertions.push_back(a); }

    }
    m_base_defs.reset ();
    NOT_IMPLEMENTED_YET ();
    // solver interface does not have a reset method. need to introduce it somewhere.
    // m_solver.reset ();
    for (unsigned i = 0, e = assertions.size (); i < e; ++i)
    { m_solver.assert_expr(assertions.get(i)); }
}

}
