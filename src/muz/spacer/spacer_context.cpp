/**
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_context.cpp

Abstract:

    SPACER predicate transformers and search context.

Author:

    Arie Gurfinkel
    Anvesh Komuravelli

    Based on muz/pdr/pdr_context.cpp by Nikolaj Bjorner (nbjorner)

Notes:

--*/


#include <sstream>
#include <iomanip>

#include "muz/base/dl_util.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "util/util.h"
#include "muz/spacer/spacer_prop_solver.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "ast/for_each_expr.h"
#include "muz/base/dl_rule_set.h"
#include "smt/tactic/unit_subsumption_tactic.h"
#include "model/model_smt2_pp.h"
#include "muz/transforms/dl_mk_rule_inliner.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/proofs/proof_checker.h"
#include "smt/smt_value_sort.h"
#include "ast/scoped_proof.h"
#include "muz/spacer/spacer_qe_project.h"
#include "tactic/core/blast_term_ite_tactic.h"

#include "util/timeit.h"
#include "util/luby.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/expr_abstract.h"

namespace spacer {

// ----------------
// pred_tansformer

pred_transformer::pred_transformer(context& ctx, manager& pm, func_decl* head):
    pm(pm), m(pm.get_manager()),
    ctx(ctx), m_head(head, m),
    m_sig(m), m_solver(pm, ctx.get_params(), head->get_name()),
    m_reach_ctx (pm.mk_fresh3 ()),
    m_pobs(*this),
    m_frames(*this),
    m_reach_facts(), m_rf_init_sz(0),
    m_transition(m), m_initial_state(m), m_extend_lit(m),
    m_all_init(false),
    m_reach_case_vars(m)
{
    init_sig ();
    app_ref v(m);
    std::stringstream name;
    name << m_head->get_name () << "_ext0";
    v = m.mk_const (symbol(name.str().c_str()), m.mk_bool_sort());
    m_extend_lit = m.mk_not (m.mk_const (pm.get_n_pred (v->get_decl ())));
}

pred_transformer::~pred_transformer()
{
    rule2inst::iterator it2 = m_rule2inst.begin(), end2 = m_rule2inst.end();
    for (; it2 != end2; ++it2) {
        dealloc(it2->m_value);
    }
    rule2expr::iterator it3 = m_rule2transition.begin(), end3 = m_rule2transition.end();
    for (; it3 != end3; ++it3) {
        m.dec_ref(it3->m_value);
    }
}

std::ostream& pred_transformer::display(std::ostream& out) const
{
    if (!rules().empty()) { out << "rules\n"; }
    datalog::rule_manager& rm = ctx.get_datalog_context().get_rule_manager();
    for (unsigned i = 0; i < rules().size(); ++i) {
        rm.display_smt2(*rules()[i], out) << "\n";
    }
    out << "transition\n" << mk_pp(transition(), m) << "\n";
    return out;
}

void pred_transformer::collect_statistics(statistics& st) const
{
    m_solver.collect_statistics(st);
    st.update("SPACER num propagations", m_stats.m_num_propagations);
    st.update("SPACER num properties", m_frames.lemma_size ());
    st.update("SPACER num invariants", m_stats.m_num_invariants);

    st.update ("time.spacer.init_rules.pt.init", m_initialize_watch.get_seconds ());
    st.update ("time.spacer.solve.pt.must_reachable",
               m_must_reachable_watch.get_seconds ());
}

void pred_transformer::reset_statistics()
{
    m_solver.reset_statistics();
    //m_reachable.reset_statistics();
    m_stats.reset();
    m_initialize_watch.reset ();
    m_must_reachable_watch.reset ();
}

void pred_transformer::init_sig()
{
    for (unsigned i = 0; i < m_head->get_arity(); ++i) {
        sort * arg_sort = m_head->get_domain(i);
        std::stringstream name_stm;
        name_stm << m_head->get_name() << '_' << i;
        func_decl_ref stm(m);
        stm = m.mk_func_decl(symbol(name_stm.str().c_str()), 0, (sort*const*)nullptr, arg_sort);
        m_sig.push_back(pm.get_o_pred(stm, 0));
    }
}

void pred_transformer::ensure_level(unsigned level)
{
    if (is_infty_level(level)) { return; }

    while (m_frames.size() <= level) {
        m_frames.add_frame ();
        m_solver.add_level ();
    }
}

bool pred_transformer::is_must_reachable(expr* state, model_ref* model)
{
    scoped_watch _t_(m_must_reachable_watch);
    SASSERT (state);
    // XXX This seems to mis-handle the case when state is
    // reachable using the init rule of the current transformer
    if (m_reach_facts.empty()) { return false; }

    m_reach_ctx->push ();
    m_reach_ctx->assert_expr (state);
    m_reach_ctx->assert_expr (m.mk_not (m_reach_case_vars.back ()));
    lbool res = m_reach_ctx->check_sat (0, nullptr);
    if (model) { m_reach_ctx->get_model(*model); }
    m_reach_ctx->pop (1);
    return (res == l_true);
}




reach_fact* pred_transformer::get_used_reach_fact (model_evaluator_util& mev,
                                                   bool all)
{
    expr_ref v (m);

    for (unsigned i = all ? 0 : m_rf_init_sz, sz = m_reach_case_vars.size ();
         i < sz; i++) {
        VERIFY (mev.eval (m_reach_case_vars.get (i), v, false));
        if (m.is_false (v)) {
            return m_reach_facts.get (i);
        }
    }

    UNREACHABLE ();
    return nullptr;
}

reach_fact *pred_transformer::get_used_origin_reach_fact (model_evaluator_util& mev,
                                                          unsigned oidx)
{
    expr_ref b(m), v(m);
    reach_fact *res = nullptr;

    for (unsigned i = 0, sz = m_reach_case_vars.size (); i < sz; i++) {
        pm.formula_n2o (m_reach_case_vars.get (i), v, oidx);
        VERIFY(mev.eval (v, b, false));

        if (m.is_false (b)) {
            res = m_reach_facts.get (i);
            break;
        }
    }
    SASSERT (res);
    return res;
}

datalog::rule const* pred_transformer::find_rule(model &model,
                                                 bool& is_concrete,
                                                 vector<bool>& reach_pred_used,
                                                 unsigned& num_reuse_reach)
{
    typedef obj_map<expr, datalog::rule const*> tag2rule;
    TRACE ("spacer_verbose",
           datalog::rule_manager& rm = ctx.get_datalog_context().get_rule_manager();
           tag2rule::iterator it = m_tag2rule.begin();
           tag2rule::iterator end = m_tag2rule.end();
           for (; it != end; ++it) {
               expr* pred = it->m_key;
               tout << mk_pp(pred, m) << ":\n";
               if (it->m_value) { rm.display_smt2(*(it->m_value), tout) << "\n"; }
           }
        );

    // find a rule whose tag is true in the model;
    // prefer a rule where the model intersects with reach facts of all predecessors;
    // also find how many predecessors' reach facts are true in the model
    expr_ref vl(m);
    datalog::rule const* r = ((datalog::rule*)nullptr);
    tag2rule::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
    for (; it != end; ++it) {
        expr* tag = it->m_key;
        if (model.eval(to_app(tag)->get_decl(), vl) && m.is_true(vl)) {
            r = it->m_value;
            is_concrete = true;
            num_reuse_reach = 0;
            reach_pred_used.reset ();
            unsigned tail_sz = r->get_uninterpreted_tail_size ();
            for (unsigned i = 0; i < tail_sz; i++) {
                bool used = false;
                func_decl* d = r->get_tail(i)->get_decl();
                pred_transformer const& pt = ctx.get_pred_transformer (d);
                if (!pt.has_reach_facts()) { is_concrete = false; }
                else {
                    expr_ref v(m);
                    pm.formula_n2o (pt.get_last_reach_case_var (), v, i);
                    model.eval (to_app (v.get ())->get_decl (), vl);
                    used = m.is_false (vl);
                    is_concrete = is_concrete && used;
                }

                reach_pred_used.push_back (used);
                if (used) { num_reuse_reach++; }
            }
            if (is_concrete) { break; }
        }
    }
    // SASSERT (r);
    // reached by a reachability fact
    if (!r) { is_concrete = true; }
    return r;
}

void pred_transformer::find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& preds) const
{
    preds.reset();
    unsigned tail_sz = r.get_uninterpreted_tail_size();
    for (unsigned ti = 0; ti < tail_sz; ti++) {
        preds.push_back(r.get_tail(ti)->get_decl());
    }
}

void pred_transformer::find_predecessors(vector<std::pair<func_decl*, unsigned> >& preds) const
{
    preds.reset();
    obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
    for (; it != end; it++) {
        datalog::rule const& r = *it->m_value;
        unsigned tail_sz = r.get_uninterpreted_tail_size();
        for (unsigned ti = 0; ti < tail_sz; ti++) {
            preds.push_back(std::make_pair (r.get_tail(ti)->get_decl(), ti));
        }
    }
}


void pred_transformer::remove_predecessors(expr_ref_vector& literals)
{
    // remove tags
    for (unsigned i = 0; i < literals.size(); ) {
        expr* l = literals[i].get();
        m.is_not(l, l);
        if (m_tag2rule.contains(l)) {
            literals[i] = literals.back();
            literals.pop_back();
        } else {
            ++i;
        }
    }
}

void pred_transformer::simplify_formulas()
{
    m_frames.simplify_formulas ();
}


expr_ref pred_transformer::get_formulas(unsigned level, bool add_axioms)
{
    expr_ref_vector res(m);
    if (add_axioms) {
        res.push_back(pm.get_background());
        res.push_back((level == 0)?initial_state():transition());
    }
    m_frames.get_frame_geq_lemmas (level, res);
    return pm.mk_and(res);
}

bool pred_transformer::propagate_to_next_level (unsigned src_level)
{return m_frames.propagate_to_next_level (src_level);}


/// \brief adds a lema to the solver and to child solvers
void pred_transformer::add_lemma_core(lemma* lemma)
{
    unsigned lvl = lemma->level();
    expr* l = lemma->get_expr();
    SASSERT(!lemma->is_ground() || is_clause(m, l));
    SASSERT(!is_quantifier(l) || is_clause(m, to_quantifier(l)->get_expr()));

    TRACE("spacer", tout << "add-lemma-core: " << pp_level (lvl)
          << " " << head ()->get_name ()
          << " " << mk_pp (l, m) << "\n";);

    TRACE("core_array_eq", tout << "add-lemma-core: " << pp_level (lvl)
          << " " << head ()->get_name ()
          << " " << mk_pp (l, m) << "\n";);

    STRACE ("spacer.expand-add",
            tout << "add-lemma: " << pp_level (lvl) << " "
            << head ()->get_name () << " "
            << mk_epp (l, m) << "\n\n";);


    if (is_infty_level(lvl)) { m_stats.m_num_invariants++; }

    if (lemma->is_ground()) {
        if (is_infty_level(lvl)) { m_solver.assert_expr(l); }
        else {
            ensure_level (lvl);
            m_solver.assert_expr (l, lvl);
        }
    }

    for (unsigned i = 0, sz = m_use.size (); i < sz; ++i)
    { m_use [i]->add_lemma_from_child(*this, lemma, next_level(lvl)); }
}

bool pred_transformer::add_lemma (expr *e, unsigned lvl) {
    lemma_ref lem = alloc(lemma, m, e, lvl);
    return m_frames.add_lemma(lem.get());
}

void pred_transformer::add_lemma_from_child (pred_transformer& child,
                                             lemma* lemma, unsigned lvl)
{
    ensure_level(lvl);
    expr_ref_vector fmls(m);
    mk_assumptions(child.head(), lemma->get_expr(), fmls);

    for (unsigned i = 0; i < fmls.size(); ++i) {
        expr_ref_vector inst(m);
        expr* a = to_app(fmls.get(i))->get_arg(0);
        expr* l = to_app(fmls.get(i))->get_arg(1);
        if (get_context().use_instantiate())
        { lemma->mk_insts(inst, l); }
        for (unsigned j=0; j < inst.size(); j++) {
            inst.set(j, m.mk_implies(a, inst.get(j)));
        }
        if (lemma->is_ground() || get_context().use_qlemmas())
        { inst.push_back(fmls.get(i)); }
        SASSERT (!inst.empty ());
        for (unsigned j = 0; j < inst.size(); ++j) {
            TRACE("spacer_detail", tout << "child property: "
                  << mk_pp(inst.get (j), m) << "\n";);
            if (is_infty_level(lvl))
            { m_solver.assert_expr(inst.get(j)); }
            else
            { m_solver.assert_expr(inst.get(j), lvl); }
        }
    }

}

expr* pred_transformer::mk_fresh_reach_case_var ()
{
    std::stringstream name;
    func_decl_ref decl(m);

    name << head ()->get_name () << "#reach_case_" << m_reach_case_vars.size ();
    decl = m.mk_func_decl (symbol (name.str ().c_str ()), 0,
                           (sort*const*)nullptr, m.mk_bool_sort ());
    m_reach_case_vars.push_back (m.mk_const (pm.get_n_pred (decl)));
    return m_reach_case_vars.back ();
}

expr* pred_transformer::get_reach_case_var (unsigned idx) const
{return m_reach_case_vars.get (idx);}


void pred_transformer::add_reach_fact (reach_fact *fact)
{
    timeit _timer (is_trace_enabled("spacer_timeit"),
                   "spacer::pred_transformer::add_reach_fact",
                   verbose_stream ());

    TRACE ("spacer",
           tout << "add_reach_fact: " << head()->get_name() << " "
           << (fact->is_init () ? "INIT " : "")
           << mk_pp(fact->get (), m) << "\n";);

    // -- avoid duplicates
    if (fact == nullptr || get_reach_fact(fact->get())) { return; }

    // all initial facts are grouped together
    SASSERT (!fact->is_init () || m_reach_facts.empty () ||
             m_reach_facts.back ()->is_init ());

    m_reach_facts.push_back (fact);
    if (fact->is_init()) { m_rf_init_sz++; }


    // update m_reach_ctx
    expr_ref last_var (m);
    expr_ref new_var (m);
    expr_ref fml (m);

    if (!m_reach_case_vars.empty()) { last_var = m_reach_case_vars.back(); }
    if (fact->is_init () || !ctx.get_params ().spacer_reach_as_init ())
    { new_var = mk_fresh_reach_case_var(); }
    else {
        new_var = extend_initial (fact->get ())->get_arg (0);
        m_reach_case_vars.push_back (new_var);
    }

    SASSERT (m_reach_facts.size () == m_reach_case_vars.size ());

    if (last_var)
    { fml = m.mk_or(m.mk_not(last_var), fact->get(), new_var); }
    else
    { fml = m.mk_or(fact->get(), new_var); }

    m_reach_ctx->assert_expr (fml);
    TRACE ("spacer",
           tout << "updating reach ctx: " << mk_pp(fml, m) << "\n";);

    lemma lem(m, fml, infty_level());
    // update users; reach facts are independent of levels
    for (unsigned i = 0; i < m_use.size(); ++i) {
        m_use[i]->add_lemma_from_child (*this, &lem, infty_level ());
    }
}

expr_ref pred_transformer::get_reachable()
{
    expr_ref res(m);
    res = m.mk_false();

    if (!m_reach_facts.empty()) {
        expr_substitution sub(m);
        expr_ref c(m), v(m);
        for (unsigned i = 0, sz = sig_size(); i < sz; ++i) {
            c = m.mk_const(pm.o2n(sig(i), 0));
            v = m.mk_var(i, sig(i)->get_range());
            sub.insert(c, v);
        }
        scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
        rep->set_substitution(&sub);

        expr_ref_vector args(m);
        for (unsigned i = 0, sz = m_reach_facts.size (); i < sz; ++i) {
            reach_fact *f;
            f = m_reach_facts.get(i);
            expr_ref r(m);
            r = f->get();
            const ptr_vector<app> &aux = f->aux_vars();
            if (!aux.empty()) {
                // -- existentially quantify auxiliary variables
                r = mk_exists (m, aux.size(), aux.c_ptr(), r);
                // XXX not sure how this interacts with variable renaming later on.
                // XXX For now, simply dissallow existentially quantified auxiliaries
                NOT_IMPLEMENTED_YET();
            }
            (*rep)(r);

            args.push_back (r);
        }
        res = mk_or(args);
    }
    return res;
}

expr* pred_transformer::get_last_reach_case_var () const
{
    return m_reach_case_vars.empty () ? nullptr : m_reach_case_vars.back ();
}

expr_ref pred_transformer::get_cover_delta(func_decl* p_orig, int level)
{
    expr_ref result(m.mk_true(), m), v(m), c(m);

    expr_ref_vector lemmas (m);
    m_frames.get_frame_lemmas (level == -1 ? infty_level() : level, lemmas);
    if (!lemmas.empty()) { result = pm.mk_and(lemmas); }

    // replace local constants by bound variables.
    expr_substitution sub(m);
    for (unsigned i = 0; i < sig_size(); ++i) {
        c = m.mk_const(pm.o2n(sig(i), 0));
        v = m.mk_var(i, sig(i)->get_range());
        sub.insert(c, v);
    }
    scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
    rep->set_substitution(&sub);
    (*rep)(result);

    // adjust result according to model converter.
    unsigned arity = m_head->get_arity();
    model_ref md = alloc(model, m);
    if (arity == 0) {
        md->register_decl(m_head, result);
    } else {
        func_interp* fi = alloc(func_interp, m, arity);
        fi->set_else(result);
        md->register_decl(m_head, fi);
    }
    model_converter_ref mc = ctx.get_model_converter();
    apply(mc, md);
    if (p_orig->get_arity() == 0) {
        result = md->get_const_interp(p_orig);
    } else {
        result = md->get_func_interp(p_orig)->get_interp();
    }
    return result;
}

/**
 * get an origin summary used by this transformer in the given model
 * level is the level at which may summaries are obtained
 * oidx is the origin index of this predicate in the model
 * must indicates whether a must or a may summary is requested
 *
 * returns an implicant of the summary
 */
expr_ref pred_transformer::get_origin_summary (model_evaluator_util &mev,
                                               unsigned level,
                                               unsigned oidx,
                                               bool must,
                                               const ptr_vector<app> **aux)
{
    expr_ref_vector summary (m);
    expr_ref v(m);

    if (!must) { // use may summary
        summary.push_back (get_formulas (level, false));
        // -- no auxiliary variables in lemmas
        *aux = nullptr;
    } else { // find must summary to use
        reach_fact *f = get_used_origin_reach_fact (mev, oidx);
        summary.push_back (f->get ());
        *aux = &f->aux_vars ();
    }

    SASSERT (!summary.empty ());

    // -- convert to origin
    for (unsigned i = 0; i < summary.size(); ++i) {
        pm.formula_n2o (summary.get (i), v, oidx);
        summary[i] = v;
    }

    // -- pick an implicant
    expr_ref_vector literals (m);
    compute_implicant_literals (mev, summary, literals);

    return get_manager ().mk_and (literals);
}


void pred_transformer::add_cover(unsigned level, expr* property)
{
    // replace bound variables by local constants.
    expr_ref result(property, m), v(m), c(m);
    expr_substitution sub(m);
    for (unsigned i = 0; i < sig_size(); ++i) {
        c = m.mk_const(pm.o2n(sig(i), 0));
        v = m.mk_var(i, sig(i)->get_range());
        sub.insert(v, c);
    }
    scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
    rep->set_substitution(&sub);
    (*rep)(result);
    TRACE("spacer", tout << "cover:\n" << mk_pp(result, m) << "\n";);

    // add the property.
    expr_ref_vector lemmas(m);
    flatten_and(result, lemmas);
    for (unsigned i = 0, sz = lemmas.size(); i < sz; ++i) {
        add_lemma(lemmas.get(i), level);
    }
}

void pred_transformer::propagate_to_infinity (unsigned level)
{m_frames.propagate_to_infinity (level);}



/// \brief Returns true if the obligation is already blocked by current lemmas
bool pred_transformer::is_blocked (pob &n, unsigned &uses_level)
{
    ensure_level (n.level ());
    prop_solver::scoped_level _sl (m_solver, n.level ());
    m_solver.set_core (nullptr);
    m_solver.set_model (nullptr);

    expr_ref_vector post(m), aux(m);
    post.push_back (n.post ());
    lbool res = m_solver.check_assumptions (post, aux, 0, nullptr, 0);
    if (res == l_false) { uses_level = m_solver.uses_level(); }
    return res == l_false;
}

bool pred_transformer::is_qblocked (pob &n)
{
    // XXX Trivial implementation to get us started
    smt::kernel solver (m, get_manager ().fparams2());
    expr_ref_vector frame_lemmas(m);
    m_frames.get_frame_geq_lemmas (n.level (), frame_lemmas);

    // assert all lemmas
    for (unsigned i = 0, sz = frame_lemmas.size (); i < sz; ++i)
    { solver.assert_expr(frame_lemmas.get(i)); }
    // assert cti
    solver.assert_expr (n.post ());
    lbool res = solver.check ();

    return res == l_false;
}

//
// check if predicate transformer has a satisfiable predecessor state.
// returns either a satisfiable predecessor state or
// return a property that blocks state and is implied by the
// predicate transformer (or some unfolding of it).
//
lbool pred_transformer::is_reachable(pob& n, expr_ref_vector* core,
                                     model_ref* model, unsigned& uses_level,
                                     bool& is_concrete, datalog::rule const*& r,
                                     vector<bool>& reach_pred_used,
                                     unsigned& num_reuse_reach)
{
    TRACE("spacer",
          tout << "is-reachable: " << head()->get_name() << " level: "
          << n.level() << " depth: " << n.depth () << "\n";
          tout << mk_pp(n.post(), m) << "\n";);
    timeit _timer (is_trace_enabled("spacer_timeit"),
                   "spacer::pred_transformer::is_reachable",
                   verbose_stream ());

    ensure_level(n.level());

    // prepare the solver
    prop_solver::scoped_level _sl(m_solver, n.level());
    prop_solver::scoped_subset_core _sc (m_solver, !n.use_farkas_generalizer ());
    m_solver.set_core(core);
    m_solver.set_model(model);

    expr_ref_vector post (m), reach_assumps (m);
    post.push_back (n.post ());

    // populate reach_assumps

    // XXX eager_reach_check must always be
    // XXX enabled. Otherwise, we can get into an infinite loop in
    // XXX which a model is consistent with a must-summary, but the
    // XXX appropriate assumption is not set correctly by the model.
    // XXX Original code handled reachability-events differently.
    if (/* ctx.get_params ().eager_reach_check () && */
        n.level () > 0 && !m_all_init) {
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin (),
            end = m_tag2rule.end ();
        for (; it != end; ++it) {
            datalog::rule const* r = it->m_value;
            if (!r) { continue; }
            find_predecessors(*r, m_predicates);
            if (m_predicates.empty()) { continue; }
            for (unsigned i = 0; i < m_predicates.size(); i++) {
                const pred_transformer &pt =
                    ctx.get_pred_transformer (m_predicates [i]);
                if (pt.has_reach_facts()) {
                    expr_ref a(m);
                    pm.formula_n2o (pt.get_last_reach_case_var (), a, i);
                    reach_assumps.push_back (m.mk_not (a));
                } else if (ctx.get_params().spacer_init_reach_facts()) {
                    reach_assumps.push_back (m.mk_not (it->m_key));
                    break;
                }
            }
        }
    }

    TRACE ("spacer",
           if (!reach_assumps.empty ()) {
               tout << "reach assumptions\n";
               for (unsigned i = 0; i < reach_assumps.size (); i++) {
                   tout << mk_pp (reach_assumps.get (i), m) << "\n";
               }
           }
        );

    // check local reachability;
    // result is either sat (with some reach assumps) or
    // unsat (even with no reach assumps)
    expr *bg = m_extend_lit.get ();
    lbool is_sat = m_solver.check_assumptions (post, reach_assumps, 1, &bg, 0);

    TRACE ("spacer",
           if (!reach_assumps.empty ()) {
               tout << "reach assumptions used\n";
               for (unsigned i = 0; i < reach_assumps.size (); i++) {
                   tout << mk_pp (reach_assumps.get (i), m) << "\n";
               }
           }
        );

    if (is_sat == l_true || is_sat == l_undef) {
        if (core) { core->reset(); }
        if (model) {
            r = find_rule (**model, is_concrete, reach_pred_used, num_reuse_reach);
            TRACE ("spacer", tout << "reachable "
                   << "is_concrete " << is_concrete << " rused: ";
                   for (unsigned i = 0, sz = reach_pred_used.size (); i < sz; ++i)
                       tout << reach_pred_used [i];
                   tout << "\n";);
        }

        return is_sat;
    }
    if (is_sat == l_false) {
        SASSERT (reach_assumps.empty ());
        TRACE ("spacer", tout << "unreachable with lemmas\n";
               if (core) {
                   tout << "Core:\n";
                   for (unsigned i = 0; i < core->size (); i++) {
                       tout << mk_pp (core->get(i), m) << "\n";
                   }
               }
            );
        uses_level = m_solver.uses_level();
        return l_false;
    }
    UNREACHABLE();
    return l_undef;
}

bool pred_transformer::is_invariant(unsigned level, expr* lemma,
                                    unsigned& solver_level, expr_ref_vector* core)
{
    expr_ref_vector conj(m), aux(m);
    expr_ref glemma(m);

    if (false && is_quantifier(lemma)) {
        SASSERT(is_forall(lemma));
        app_ref_vector tmp(m);
        ground_expr(to_quantifier(lemma)->get_expr (), glemma, tmp);
        lemma = glemma.get();
    }

    conj.push_back(mk_not(m, lemma));
    flatten_and (conj);

    prop_solver::scoped_level _sl(m_solver, level);
    prop_solver::scoped_subset_core _sc (m_solver, true);
    m_solver.set_core(core);
    m_solver.set_model(nullptr);
    expr * bg = m_extend_lit.get ();
    lbool r = m_solver.check_assumptions (conj, aux, 1, &bg, 1);
    if (r == l_false) {
        solver_level = m_solver.uses_level ();
        CTRACE ("spacer", level < m_solver.uses_level (),
                tout << "Checking at level " << level
                << " but only using " << m_solver.uses_level () << "\n";);
        SASSERT (level <= solver_level);
    }
    return r == l_false;
}

bool pred_transformer::check_inductive(unsigned level, expr_ref_vector& state,
                                       unsigned& uses_level)
{
    manager& pm = get_manager();
    expr_ref_vector conj(m), core(m);
    expr_ref states(m);
    states = m.mk_not(pm.mk_and(state));
    mk_assumptions(head(), states, conj);
    prop_solver::scoped_level _sl(m_solver, level);
    prop_solver::scoped_subset_core _sc (m_solver, true);
    m_solver.set_core(&core);
    m_solver.set_model (nullptr);
    expr_ref_vector aux (m);
    conj.push_back (m_extend_lit);
    lbool res = m_solver.check_assumptions (state, aux, conj.size (), conj.c_ptr (), 1);
    if (res == l_false) {
        state.reset();
        state.append(core);
        uses_level = m_solver.uses_level();
    }
    TRACE ("core_array_eq",
           tout << "check_inductive: "
           << "states: " << mk_pp (states, m)
           << " is: " << res << "\n"
           << "with transition: " << mk_pp (m_transition, m) << "\n";);
    return res == l_false;
}

void pred_transformer::mk_assumptions(func_decl* head, expr* fml,
                                      expr_ref_vector& result)
{
    expr_ref tmp1(m), tmp2(m);
    expr_substitution sub (m);
    proof_ref pr (m.mk_asserted (m.mk_true ()), m);
    obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(),
        end = m_tag2rule.end();
    for (; it != end; ++it) {
        expr* tag = it->m_key;
        datalog::rule const* r = it->m_value;
        if (!r) { continue; }
        find_predecessors(*r, m_predicates);
        for (unsigned i = 0; i < m_predicates.size(); i++) {
            func_decl* d = m_predicates[i];
            if (d == head) {
                tmp1 = m.mk_implies(tag, fml);
                pm.formula_n2o(tmp1, tmp2, i);
                result.push_back(tmp2);
            }
        }
    }
}

void pred_transformer::initialize(decl2rel const& pts)
{
    m_initial_state = m.mk_false();
    m_transition = m.mk_true();
    init_rules(pts, m_initial_state, m_transition);
    th_rewriter rw(m);
    rw(m_transition);
    rw(m_initial_state);

    m_solver.assert_expr (m_transition);
    m_solver.assert_expr (m_initial_state, 0);
    TRACE("spacer",
          tout << "Initial state: " << mk_pp(m_initial_state, m) << "\n";
          tout << "Transition:    " << mk_pp(m_transition,  m) << "\n";);
    SASSERT(is_app(m_initial_state));
    //m_reachable.add_init(to_app(m_initial_state));


}

void pred_transformer::init_reach_facts ()
{
    expr_ref_vector v(m);
    reach_fact_ref fact;

    rule2expr::iterator it = m_rule2tag.begin (), end = m_rule2tag.end ();
    for (; it != end; ++it) {
        const datalog::rule* r = it->m_key;
        if (r->get_uninterpreted_tail_size() == 0) {
            fact = alloc (reach_fact, m, *r, m_rule2transition.find (r),
                          get_aux_vars (*r), true);
            add_reach_fact (fact.get ());
        }
    }
}

void pred_transformer::init_rules(decl2rel const& pts, expr_ref& init, expr_ref& transition)
{
    expr_ref_vector transitions(m);
    ptr_vector<datalog::rule const> tr_rules;
    datalog::rule const* rule;
    expr_ref_vector disj(m), init_conds (m);
    app_ref pred(m);
    vector<bool> is_init;
    for (unsigned i = 0; i < rules().size(); ++i) {
        init_rule(pts, *rules()[i], is_init, tr_rules, transitions);
    }
    SASSERT (is_init.size () == transitions.size ());
    switch(transitions.size()) {
    case 0:
        transition = m.mk_false();
        break;
    case 1: {
        std::stringstream name;
        // create a dummy tag.
        name << head()->get_name() << "_dummy";
        pred = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());
        rule = tr_rules[0];
        m_tag2rule.insert(pred, rule);
        m_rule2tag.insert(rule, pred.get());
        transitions [0] = m.mk_implies (pred, transitions.get (0));
        transitions.push_back (m.mk_or (pred, m_extend_lit->get_arg (0)));
        if (!is_init [0]) { init_conds.push_back(m.mk_not(pred)); }

        transition = pm.mk_and(transitions);
        break;
    }
    default:
        disj.push_back (m_extend_lit->get_arg (0));
        for (unsigned i = 0; i < transitions.size(); ++i) {
            std::stringstream name;
            name << head()->get_name() << "_tr" << i;
            pred = m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort());
            rule = tr_rules[i];
            m_tag2rule.insert(pred, rule);
            m_rule2tag.insert(rule, pred);
            disj.push_back(pred);
            transitions[i] = m.mk_implies(pred, transitions[i].get());
            // update init conds
            if (!is_init[i]) {
                init_conds.push_back (m.mk_not (pred));
            }
        }
        transitions.push_back(m.mk_or(disj.size(), disj.c_ptr()));
        transition = pm.mk_and(transitions);
        break;
    }
    // mk init condition
    init = pm.mk_and (init_conds);
    if (init_conds.empty ()) { // no rule has uninterpreted tail
        m_all_init = true;
    }
}

void pred_transformer::init_rule(
    decl2rel const&      pts,
    datalog::rule const& rule,
    vector<bool>&     is_init,
    ptr_vector<datalog::rule const>& rules,
    expr_ref_vector&     transitions)
{
    scoped_watch _t_(m_initialize_watch);

    // Predicates that are variable representatives. Other predicates at
    // positions the variables occur are made equivalent with these.
    expr_ref_vector conj(m);
    app_ref_vector& var_reprs = *(alloc(app_ref_vector, m));
    ptr_vector<app> aux_vars;

    unsigned ut_size = rule.get_uninterpreted_tail_size();
    unsigned t_size  = rule.get_tail_size();
    SASSERT(ut_size <= t_size);
    init_atom(pts, rule.get_head(), var_reprs, conj, UINT_MAX);
    for (unsigned i = 0; i < ut_size; ++i) {
        if (rule.is_neg_tail(i)) {
            throw default_exception("SPACER does not support negated predicates in rule tails");
        }
        init_atom(pts, rule.get_tail(i), var_reprs, conj, i);
    }
    // -- substitute free variables
    expr_ref fml(m);
    {
        expr_ref_vector tail(m);
        for (unsigned i = ut_size; i < t_size; ++i)
        { tail.push_back(rule.get_tail(i)); }
        fml = mk_and (tail);

        ground_free_vars (fml, var_reprs, aux_vars, ut_size == 0);
        SASSERT(check_filled(var_reprs));

        expr_ref tmp(m);
        var_subst (m, false)(fml,
                             var_reprs.size (), (expr*const*)var_reprs.c_ptr(), tmp);
        flatten_and (tmp, conj);
        fml = mk_and(conj);
        conj.reset ();
    }

    th_rewriter rw(m);
    rw(fml);
    if (ctx.get_params().spacer_blast_term_ite()) {
        blast_term_ite (fml);
        rw(fml);
    }
    TRACE("spacer", tout << mk_pp(fml, m) << "\n";);

    // allow quantifiers in init rule
    SASSERT(ut_size == 0 || is_ground(fml));
    if (m.is_false(fml)) {
        // no-op.
    } else {
        is_init.push_back (ut_size == 0);
        transitions.push_back(fml);
        m.inc_ref(fml);
        m_rule2transition.insert(&rule, fml.get());
        rules.push_back(&rule);
    }
    m_rule2inst.insert(&rule,&var_reprs);
    m_rule2vars.insert(&rule, aux_vars);
    TRACE("spacer",
          tout << rule.get_decl()->get_name() << "\n";
          for (unsigned i = 0; i < var_reprs.size(); ++i) {
              tout << mk_pp(var_reprs[i].get(), m) << " ";
          }
          tout << "\n";);
}

bool pred_transformer::check_filled(app_ref_vector const& v) const
{
    for (unsigned i = 0; i < v.size(); ++i) {
        if (!v[i]) { return false; }
    }
    return true;
}

// create constants for free variables in tail.
void pred_transformer::ground_free_vars(expr* e, app_ref_vector& vars,
                                        ptr_vector<app>& aux_vars, bool is_init)
{
    expr_free_vars fv;
    fv(e);

    while (vars.size() < fv.size()) {
        vars.push_back(nullptr);
    }
    for (unsigned i = 0; i < fv.size(); ++i) {
        if (fv[i] && !vars[i].get()) {
            vars[i] = m.mk_fresh_const("aux", fv[i]);
            vars[i] = m.mk_const (pm.get_n_pred (vars.get (i)->get_decl ()));
            aux_vars.push_back(vars[i].get());
        }
    }

}

// create names for variables used in relations.
void pred_transformer::init_atom(
    decl2rel const& pts,
    app * atom,
    app_ref_vector& var_reprs,
    expr_ref_vector& conj,
    unsigned tail_idx
    )
{
    unsigned arity = atom->get_num_args();
    func_decl* head = atom->get_decl();
    pred_transformer& pt = *pts.find(head);
    for (unsigned i = 0; i < arity; i++) {
        app_ref rep(m);

        if (tail_idx == UINT_MAX) {
            rep = m.mk_const(pm.o2n(pt.sig(i), 0));
        } else {
            rep = m.mk_const(pm.o2o(pt.sig(i), 0, tail_idx));
        }

        expr * arg = atom->get_arg(i);
        if (is_var(arg)) {
            var * v = to_var(arg);
            unsigned var_idx = v->get_idx();
            if (var_idx >= var_reprs.size()) {
                var_reprs.resize(var_idx+1);
            }
            expr * repr = var_reprs[var_idx].get();
            if (repr) {
                conj.push_back(m.mk_eq(rep, repr));
            } else {
                var_reprs[var_idx] = rep;
            }
        } else {
            SASSERT(is_app(arg));
            conj.push_back(m.mk_eq(rep, arg));
        }
    }
}

void pred_transformer::add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r)
{
    r.push_back(pm.get_background());
    r.push_back((lvl == 0)?initial_state():transition());
    for (unsigned i = 0; i < rules().size(); ++i) {
        add_premises(pts, lvl, *rules()[i], r);
    }
}

void pred_transformer::add_premises(decl2rel const& pts, unsigned lvl, datalog::rule& rule, expr_ref_vector& r)
{
    find_predecessors(rule, m_predicates);
    for (unsigned i = 0; i < m_predicates.size(); ++i) {
        expr_ref tmp(m);
        func_decl* head = m_predicates[i];
        pred_transformer& pt = *pts.find(head);
        expr_ref inv = pt.get_formulas(lvl, false);
        if (!m.is_true(inv)) {
            pm.formula_n2o(inv, tmp, i, true);
            r.push_back(tmp);
        }
    }
}

void pred_transformer::inherit_properties(pred_transformer& other)
{
    m_frames.inherit_frames (other.m_frames);
}


lemma::lemma (ast_manager &manager, expr * body, unsigned lvl) :
    m_ref_count(0), m(manager),
    m_body(body, m), m_cube(m),
    m_bindings(m), m_lvl(lvl),
    m_pob(nullptr), m_new_pob(false) {
    SASSERT(m_body);
    normalize(m_body, m_body);
}

lemma::lemma(pob_ref const &p) :
    m_ref_count(0), m(p->get_ast_manager()),
    m_body(m), m_cube(m),
    m_bindings(m), m_lvl(p->level()),
    m_pob(p), m_new_pob(m_pob) {SASSERT(m_pob);}

lemma::lemma(pob_ref const &p, expr_ref_vector &cube, unsigned lvl) :
    m_ref_count(0),
    m(p->get_ast_manager()),
    m_body(m), m_cube(m),
    m_bindings(m), m_lvl(p->level()),
    m_pob(p), m_new_pob(m_pob)
{
    update_cube(p, cube);
    set_level(lvl);
}

void lemma::mk_expr_core() {
    if (m_body) return;

    if (m_pob) {
        mk_cube_core();

        // make a clause by negating the cube
        m_body = ::push_not(::mk_and(m_cube));
        normalize(m_body, m_body);

        if (!m_pob->is_ground() && has_zk_const(m_body)) {
            app_ref_vector zks(m);
            m_pob->get_skolems(zks);
            zks.reverse();
            expr_abstract(m, 0,
                          zks.size(), (expr* const*)zks.c_ptr(), m_body,
                          m_body);
            ptr_buffer<sort> sorts;
            svector<symbol> names;
            for (unsigned i=0, sz=zks.size(); i < sz; ++i) {
                sorts.push_back(get_sort(zks.get(i)));
                names.push_back(zks.get(i)->get_decl()->get_name());
            }
            m_body = m.mk_quantifier(true, zks.size(),
                                     sorts.c_ptr(),
                                     names.c_ptr(),
                                     m_body, 0, symbol(m_body->get_id()));
            if (m_new_pob) {
                add_binding(m_pob->get_binding());
            }
        }
        m_new_pob = false;
        return;
    }
    else if (!m_cube.empty()) {
        m_body = ::push_not(::mk_and(m_cube));
        normalize(m_body, m_body);
        return;
    }
    else {
        UNREACHABLE();
    }
    SASSERT(m_body);
}
void lemma::mk_cube_core() {
    if (!m_cube.empty()) {return;}
    expr_ref cube(m);
    if (m_pob || m_body) {
        if(m_pob) {
            cube = m_pob->post();
        }
        else if (m_body) {
            // no quantifiers for now
            SASSERT(!is_quantifier(m_body));
            cube = m_body;
            cube = ::push_not(cube);
        }
        flatten_and(cube, m_cube);
        if (m_cube.empty()) {
            m_cube.push_back(m.mk_true());
        }
        else {
            std::sort(m_cube.c_ptr(), m_cube.c_ptr() + m_cube.size(), ast_lt_proc());
        }
    }
    else {
        UNREACHABLE();
    }
}
bool lemma::is_false() {
    // a lemma is false if
    // 1. it is defined by a cube, and the cube contains a single literal 'true'
    // 2. it is defined by a body, and the body is a single literal false
    // 3. it is defined by a pob, and the pob post is false
    if (m_cube.size() == 1) {return m.is_true(m_cube.get(0));}
    else if (m_body) {return m.is_false(m_body);}
    else if (m_pob) {return m.is_true(m_pob->post());}

    return false;
}
expr* lemma::get_expr() {
    mk_expr_core();
    return m_body;
}
expr_ref_vector const &lemma::get_cube() {
    mk_cube_core();
    return m_cube;
}

void lemma::update_cube (pob_ref const &p, expr_ref_vector &cube) {
    SASSERT(m_pob);
    SASSERT(m_pob.get() == p.get());
    m_cube.reset();
    m_body.reset();
    m_cube.append(cube);
    if (m_cube.empty()) {m_cube.push_back(m.mk_true());}
}

void lemma::mk_insts(expr_ref_vector &out, expr* e)
{
    expr *lem = e == nullptr ? get_expr() : e;
    if (!is_quantifier (lem) || m_bindings.empty()) {return;}

    expr *body = to_quantifier(lem)->get_expr();
    unsigned num_decls = to_quantifier(lem)->get_num_decls();
    expr_ref inst(m);
    var_subst vs(m, false);
    for (unsigned i = 0,
             sz = m_bindings.size() / num_decls,
             off = 0;
         i < sz;
         ++i, off += num_decls) {
        inst.reset();
        vs.reset();
        vs(body, num_decls, (expr**) m_bindings.c_ptr() + off, inst);
        out.push_back(inst);
    }
}

bool pred_transformer::frames::add_lemma(lemma *lem)
{
    TRACE("spacer", tout << "add-lemma: " << pp_level(lem->level()) << " "
          << m_pt.head()->get_name() << " "
          << mk_pp(lem->get_expr(), m_pt.get_ast_manager()) << "\n";);

    for (unsigned i = 0, sz = m_lemmas.size(); i < sz; ++i) {
        if (m_lemmas [i]->get_expr() == lem->get_expr()) {
            // extend bindings if needed
            if (!lem->get_bindings().empty()) {
                m_lemmas [i]->add_binding(lem->get_bindings());
            }
            // if the lemma is at a higher level, skip it
            // XXX if there are new bindings, we need to assert new instances
            if (m_lemmas [i]->level() >= lem->level()) {
                TRACE("spacer", tout << "Already at a higher level: "
                      << pp_level(m_lemmas [i]->level()) << "\n";);
                return false;
            }

            // update level of the existing lemma
            m_lemmas [i]->set_level(lem->level());
            // assert lemma in the solver
            m_pt.add_lemma_core(m_lemmas[i]);
            // move the lemma to its new place to maintain sortedness
            for (unsigned j = i; (j + 1) < sz && m_lt(m_lemmas [j + 1], m_lemmas[j]); ++j) {
                m_lemmas.swap (j, j+1);
            }

            return true;
        }
    }

    // did not find, create new lemma
    m_lemmas.push_back(lem);
    m_sorted = false;
    m_pt.add_lemma_core(lem);
    return true;
}


void pred_transformer::frames::propagate_to_infinity (unsigned level)
{
    for (unsigned i = 0, sz = m_lemmas.size (); i < sz; ++i)
        if (m_lemmas[i]->level() >= level && !is_infty_level(m_lemmas [i]->level())) {
            m_lemmas [i]->set_level (infty_level ());
            m_pt.add_lemma_core (m_lemmas [i]);
            m_sorted = false;
        }
}

void pred_transformer::frames::sort ()
{
    if (m_sorted) { return; }

    m_sorted = true;
    std::sort(m_lemmas.c_ptr(), m_lemmas.c_ptr() + m_lemmas.size (), m_lt);
}

bool pred_transformer::frames::propagate_to_next_level (unsigned level)
{
    sort ();
    bool all = true;


    if (m_lemmas.empty()) { return all; }

    unsigned tgt_level = next_level (level);
    m_pt.ensure_level (tgt_level);

    for (unsigned i = 0, sz = m_lemmas.size(); i < sz && m_lemmas [i]->level() <= level;) {
        if (m_lemmas [i]->level () < level)
        {++i; continue;}


        unsigned solver_level;
        expr * curr = m_lemmas [i]->get_expr ();
        if (m_pt.is_invariant(tgt_level, curr, solver_level)) {
            m_lemmas [i]->set_level (solver_level);
            m_pt.add_lemma_core (m_lemmas [i]);

            // percolate the lemma up to its new place
            for (unsigned j = i; (j+1) < sz && m_lt (m_lemmas[j+1], m_lemmas[j]); ++j) {
                m_lemmas.swap(j, j + 1);
            }
        } else {
            all = false;
            ++i;
        }
    }

    return all;
}

void pred_transformer::frames::simplify_formulas ()
{
    // number of subsumed lemmas
    unsigned num_sumbsumed = 0;

    // ensure that the lemmas are sorted
    sort();
    ast_manager &m = m_pt.get_ast_manager ();

    tactic_ref simplifier = mk_unit_subsumption_tactic (m);
    lemma_ref_vector new_lemmas;

    unsigned lemmas_size = m_lemmas.size ();
    goal_ref g (alloc (goal, m, false, false, false));

    unsigned j = 0;
    // for every frame + infinity frame
    for (unsigned i = 0; i <= m_size; ++i) {
        g->reset_all ();
        // normalize level
        unsigned level = i < m_size ? i : infty_level ();

        goal_ref_buffer result;

        // simplify lemmas of the current level
        // XXX lemmas of higher levels can be assumed in background
        // XXX decide what to do with non-ground lemmas!
        unsigned begin = j;
        for (; j < lemmas_size && m_lemmas[j]->level() <= level; ++j) {
            if (m_lemmas[j]->level() == level) {
                g->assert_expr(m_lemmas[j]->get_expr());
            }
        }
        unsigned end = j;

        unsigned sz = end - begin;
        // no lemmas at current level, move to next level
        if (sz <= 0) {continue;}

        // exactly one lemma at current level, nothing to
        // simplify. move to next level
        if (sz == 1) {
            new_lemmas.push_back(m_lemmas[begin]);
            continue;
        }

        // more than one lemma at current level. simplify.
        (*simplifier)(g, result);
        SASSERT(result.size () == 1);
        goal *r = result[0];

        // no simplification happened, copy all the lemmas
        if (r->size () == sz) {
            for (unsigned n = begin; n < end; ++n) {
                new_lemmas.push_back (m_lemmas[n]);
            }
        }
        // something got simplified, find out which lemmas remain
        else {
            num_sumbsumed += (sz - r->size());
            // For every expression in the result, copy corresponding
            // lemma into new_lemmas
            // XXX linear search. optimize if needed.
            for (unsigned k = 0; k < r->size(); ++k) {
                bool found = false;
                for (unsigned n = begin; n < end; ++n) {
                    if (m_lemmas[n]->get_expr() == r->form(k)) {
                        new_lemmas.push_back(m_lemmas[n]);
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    verbose_stream() << "Failed to find a lemma for: "
                                     << mk_pp(r->form(k), m) << "\n";
                    verbose_stream() << "Available lemmas are: ";
                    for (unsigned n = begin; n < end; ++n) {
                        verbose_stream() << n << ": "
                                         << mk_pp(m_lemmas[n]->get_expr(), m)
                                         << "\n";
                    }
                }
                ENSURE(found);
                SASSERT(found);
            }
        }
    }

    SASSERT(new_lemmas.size() + num_sumbsumed == m_lemmas.size());
    ENSURE(new_lemmas.size() + num_sumbsumed == m_lemmas.size());
    if (new_lemmas.size() < m_lemmas.size()) {
        m_lemmas.reset();
        m_lemmas.append(new_lemmas);
        m_sorted = false;
        sort();
    }
}

pob* pred_transformer::pobs::mk_pob(pob *parent,
                                    unsigned level, unsigned depth,
                                    expr *post, app_ref_vector const &b) {

    if (!m_pt.ctx.get_params().spacer_reuse_pobs()) {
        pob* n = alloc(pob, parent, m_pt, level, depth);
        n->set_post(post, b);
        return n;
    }

    // create a new pob and set its post to normalize it
    pob p(parent, m_pt, level, depth, false);
    p.set_post(post, b);

    if (m_pobs.contains(p.post())) {
        auto &buf = m_pobs[p.post()];
        for (unsigned i = 0, sz = buf.size(); i < sz; ++i) {
            pob *f = buf.get(i);
            if (f->parent() == parent) {
                f->inherit(p);
                return f;
            }
        }
    }

    pob* n = alloc(pob, parent, m_pt, level, depth);
    n->set_post(post, b);
    m_pinned.push_back(n);

    if (m_pobs.contains(n->post())) {
        m_pobs[n->post()].push_back(n);
    }
    else {
        pob_buffer buf;
        buf.push_back(n);
        m_pobs.insert(n->post(), buf);
    }
    return n;
}

app* pred_transformer::extend_initial (expr *e)
{
    // create fresh extend literal
    app_ref v(m);
    std::stringstream name;
    name << m_head->get_name() << "_ext";
    v = m.mk_fresh_const (name.str ().c_str (),
                          m.mk_bool_sort ());
    v = m.mk_const (pm.get_n_pred (v->get_decl ()));

    expr_ref ic(m);

    // -- extend the initial condition
    ic = m.mk_or (m_extend_lit, e, v);
    m_solver.assert_expr (ic);

    // -- remember the new extend literal
    m_extend_lit = m.mk_not (v);

    return m_extend_lit;
}


// ----------------
// derivation

derivation::derivation (pob& parent, datalog::rule const& rule,
                        expr *trans, app_ref_vector const &evars) :
    m_parent (parent),
    m_rule (rule),
    m_premises (),
    m_active (0),
    m_trans (trans, m_parent.get_ast_manager ()),
    m_evars (evars) {}

derivation::premise::premise (pred_transformer &pt, unsigned oidx,
                              expr *summary, bool must,
                              const ptr_vector<app> *aux_vars) :
    m_pt (pt), m_oidx (oidx),
    m_summary (summary, pt.get_ast_manager ()), m_must (must),
    m_ovars (pt.get_ast_manager ())
{

    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();

    unsigned sig_sz = m_pt.head ()->get_arity ();
    for (unsigned i = 0; i < sig_sz; ++i)
    { m_ovars.push_back(m.mk_const(sm.o2o(pt.sig(i), 0, m_oidx))); }

    if (aux_vars)
        for (unsigned i = 0, sz = aux_vars->size (); i < sz; ++i)
        { m_ovars.push_back(m.mk_const(sm.n2o(aux_vars->get(i)->get_decl(), m_oidx))); }
}

derivation::premise::premise (const derivation::premise &p) :
    m_pt (p.m_pt), m_oidx (p.m_oidx), m_summary (p.m_summary), m_must (p.m_must),
    m_ovars (p.m_ovars) {}

/// \brief Updated the summary.
/// The new summary is over n-variables.
void derivation::premise::set_summary (expr * summary, bool must,
                                       const ptr_vector<app> *aux_vars)
{
    ast_manager &m = m_pt.get_ast_manager ();
    manager &sm = m_pt.get_manager ();
    unsigned sig_sz = m_pt.head ()->get_arity ();

    m_must = must;
    sm.formula_n2o (summary, m_summary, m_oidx);

    m_ovars.reset ();
    for (unsigned i = 0; i < sig_sz; ++i)
    { m_ovars.push_back(m.mk_const(sm.o2o(m_pt.sig(i), 0, m_oidx))); }

    if (aux_vars)
        for (unsigned i = 0, sz = aux_vars->size (); i < sz; ++i)
            m_ovars.push_back (m.mk_const (sm.n2o (aux_vars->get (i)->get_decl (),
                                                   m_oidx)));
}


void derivation::add_premise (pred_transformer &pt,
                              unsigned oidx,
                              expr* summary,
                              bool must,
                              const ptr_vector<app> *aux_vars)
{m_premises.push_back (premise (pt, oidx, summary, must, aux_vars));}



pob *derivation::create_first_child (model_evaluator_util &mev)
{
    if (m_premises.empty()) { return nullptr; }
    m_active = 0;
    return create_next_child(mev);
}

pob *derivation::create_next_child (model_evaluator_util &mev)
{
    timeit _timer (is_trace_enabled("spacer_timeit"),
                   "spacer::derivation::create_next_child",
                   verbose_stream ());

    ast_manager &m = get_ast_manager ();
    expr_ref_vector summaries (m);
    app_ref_vector vars (m);

    bool use_native_mbp = get_context ().use_native_mbp ();
    bool ground = get_context ().use_ground_cti ();
    // -- find first may premise
    while (m_active < m_premises.size() && m_premises[m_active].is_must()) {
        summaries.push_back (m_premises[m_active].get_summary ());
        vars.append (m_premises[m_active].get_ovars ());
        ++m_active;
    }
    if (m_active >= m_premises.size()) { return nullptr; }

    // -- update m_trans with the pre-image of m_trans over the must summaries
    summaries.push_back (m_trans);
    m_trans = get_manager ().mk_and (summaries);
    summaries.reset ();

    if (!vars.empty()) {
        timeit _timer1 (is_trace_enabled("spacer_timeit"),
                        "create_next_child::qproject1",
                        verbose_stream ());
        qe_project (m, vars, m_trans, mev.get_model (), true, use_native_mbp, !ground);
        //qe::reduce_array_selects (*mev.get_model (), m_trans);
        // remember variables that need to be existentially quantified
        m_evars.append (vars);
    }

    if (!mev.is_true (m_premises[m_active].get_summary())) {
        IF_VERBOSE(1, verbose_stream() << "Summary unexpectendly not true\n";);
        return nullptr;
    }


    // create the post condition by compute post-image over summaries
    // that precede currently active premise
    vars.reset ();
    for (unsigned i = m_active + 1; i < m_premises.size(); ++i) {
        summaries.push_back (m_premises [i].get_summary ());
        vars.append (m_premises [i].get_ovars ());
    }
    summaries.push_back (m_trans);

    expr_ref post(m);
    post = get_manager ().mk_and (summaries);
    summaries.reset ();
    if (!vars.empty()) {
        timeit _timer2 (is_trace_enabled("spacer_timeit"),
                        "create_next_child::qproject2",
                        verbose_stream ());
        qe_project (m, vars, post, mev.get_model (), true, use_native_mbp, !ground);
        //qe::reduce_array_selects (*mev.get_model (), post);

        // remember variables that need to be existentially quantified
        m_evars.append (vars);
    }

    get_manager ().formula_o2n (post.get (), post,
                                m_premises [m_active].get_oidx (), m_evars.empty());


    /* The level and depth are taken from the parent, not the sibling.
       The reasoning is that the sibling has not been checked before,
       and lower level is a better starting point. */
    pob *n = m_premises[m_active].pt().mk_pob(&m_parent,
                                              prev_level (m_parent.level ()),
                                              m_parent.depth (), post, m_evars);

    IF_VERBOSE (1, verbose_stream ()
                << "\n\tcreate_child: " << n->pt ().head ()->get_name ()
                << " (" << n->level () << ", " << n->depth () << ") "
                << (n->use_farkas_generalizer () ? "FAR " : "SUB ")
                << n->post ()->get_id ();
                verbose_stream().flush (););
    return n;
}

pob *derivation::create_next_child ()
{
    if (m_active + 1 >= m_premises.size()) { return nullptr; }

    bool use_native_mbp = get_context ().use_native_mbp ();
    bool ground = get_context ().use_ground_cti ();

    // update the summary of the active node to some must summary

    // construct a new model consistent with the must summary of m_active premise
    pred_transformer &pt = m_premises[m_active].pt ();
    model_ref model;

    ast_manager &m = get_ast_manager ();
    manager &pm = get_manager ();

    expr_ref_vector summaries (m);

    for (unsigned i = m_active + 1; i < m_premises.size (); ++i)
    { summaries.push_back(m_premises [i].get_summary()); }

    // -- orient transition relation towards m_active premise
    expr_ref active_trans (m);
    pm.formula_o2n (m_trans, active_trans,
                    m_premises[m_active].get_oidx (), false);
    summaries.push_back (active_trans);

    // if not true, bail out, the must summary of m_active is not strong enough
    // this is possible if m_post was weakened for some reason
    if (!pt.is_must_reachable(pm.mk_and(summaries), &model)) { return nullptr; }

    model_evaluator_util mev (m);
    mev.set_model (*model);
    // find must summary used

    reach_fact *rf = pt.get_used_reach_fact (mev, true);

    // get an implicant of the summary
    expr_ref_vector u(m), lits (m);
    u.push_back (rf->get ());
    compute_implicant_literals (mev, u, lits);
    expr_ref v(m);
    v = pm.mk_and (lits);

    // XXX The summary is not used by anyone after this point
    m_premises[m_active].set_summary (v, true, &(rf->aux_vars ()));


    /** HACK: needs a rewrite
     * compute post over the new must summary this must be done here
     * because the must summary is currently described over new
     * variables. However, we store it over old-variables, but we do
     * not update the model. So we must get rid of all of the
     * new-variables at this point.
     */
    {
        pred_transformer &pt = m_premises[m_active].pt ();
        app_ref_vector vars (m);

        summaries.reset ();
        summaries.push_back (v);
        summaries.push_back (active_trans);
        m_trans = pm.mk_and (summaries);

        // variables to eliminate
        vars.append (rf->aux_vars ().size (), rf->aux_vars ().c_ptr ());
        for (unsigned i = 0, sz = pt.head ()->get_arity (); i < sz; ++i)
        { vars.push_back(m.mk_const(pm.o2n(pt.sig(i), 0))); }

        if (!vars.empty ()) {
            qe_project (m, vars, m_trans, mev.get_model (), true, use_native_mbp,
                        !ground);
            // keep track of implicitly quantified variables
            m_evars.append (vars);
        }
    }

    m_active++;

    return create_next_child (mev);
}

pob::pob (pob* parent, pred_transformer& pt,
          unsigned level, unsigned depth, bool add_to_parent):
    m_ref_count (0),
    m_parent (parent), m_pt (pt),
    m_post (m_pt.get_ast_manager ()),
    m_binding(m_pt.get_ast_manager()),
    m_new_post (m_pt.get_ast_manager ()),
    m_level (level), m_depth (depth),
    m_open (true), m_use_farkas (true), m_weakness(0) {
    if(add_to_parent && m_parent) {
        m_parent->add_child(*this);
    }
}


void pob::set_post(expr* post) {
    app_ref_vector b(get_ast_manager());
    set_post(post, b);
}

void pob::set_post(expr* post, app_ref_vector const &b) {
    normalize(post, m_post,
              m_pt.get_context().get_params().spacer_simplify_pob(),
              m_pt.get_context().get_params().spacer_use_eqclass());

    m_binding.reset();
    if (b.empty()) return;

    m_binding.append(b);

    std::sort (m_binding.c_ptr(), m_binding.c_ptr() + m_binding.size(), ast_lt_proc());

    // skolemize implicit existential quantifier
    ast_manager &m = get_ast_manager();
    app_ref_vector pinned(m);

    expr_safe_replace sub(m);
    for (unsigned i = 0, sz = m_binding.size(); i < sz; ++i) {
        expr* e;

        e = m_binding.get(i);
        pinned.push_back (mk_zk_const (m, i, get_sort(e)));
        sub.insert (e, pinned.back());
    }
    sub(m_post);
}

void pob::inherit(pob const &p) {
    SASSERT(m_parent == p.m_parent);
    SASSERT(&m_pt == &p.m_pt);
    SASSERT(m_post == p.m_post);
    SASSERT(!m_new_post);

    m_binding.reset();
    m_binding.append(p.m_binding);

    m_level = p.m_level;
    m_depth = p.m_depth;
    m_open = p.m_open;
    m_use_farkas = p.m_use_farkas;
    m_weakness = p.m_weakness;

    m_derivation = nullptr;
}

void pob::clean () {
    if(m_new_post) {
        m_post = m_new_post;
        m_new_post.reset();
    }
}

void pob::close () {
    if(!m_open) { return; }

    reset ();
    m_open = false;
    for (unsigned i = 0, sz = m_kids.size (); i < sz; ++i)
    { m_kids [i]->close(); }
}

void pob::get_skolems(app_ref_vector &v) {
    for (unsigned i = 0, sz = m_binding.size(); i < sz; ++i) {
        expr* e;

        e = m_binding.get(i);
        v.push_back (mk_zk_const (get_ast_manager(), i, get_sort(e)));
    }
}



// ----------------
// pob_queue

pob* pob_queue::top ()
{
    /// nothing in the queue
    if (m_obligations.empty()) { return nullptr; }
    /// top queue element is above max level
    if (m_obligations.top()->level() > m_max_level) { return nullptr; }
    /// top queue element is at the max level, but at a higher than base depth
    if (m_obligations.top ()->level () == m_max_level &&
        m_obligations.top()->depth() > m_min_depth) { return nullptr; }

    /// there is something good in the queue
    return m_obligations.top ().get ();
}

void pob_queue::set_root(pob& root)
{
    m_root = &root;
    m_max_level = root.level ();
    m_min_depth = root.depth ();
    reset();
}

pob_queue::~pob_queue() {}

void pob_queue::reset()
{
    while (!m_obligations.empty()) { m_obligations.pop(); }
    if (m_root) { m_obligations.push(m_root); }
}

// ----------------
// context

context::context(fixedpoint_params const&     params,
                 ast_manager&          m) :
    m_params(params),
    m(m),
    m_context(nullptr),
    m_pm(params.pdr_max_num_contexts(), m),
    m_query_pred(m),
    m_query(nullptr),
    m_pob_queue(),
    m_last_result(l_undef),
    m_inductive_lvl(0),
    m_expanded_lvl(0),
    m_use_native_mbp(params.spacer_native_mbp ()),
    m_ground_cti (params.spacer_ground_cti ()),
    m_instantiate (params.spacer_instantiate ()),
    m_use_qlemmas (params.spacer_qlemmas ()),
    m_weak_abs(params.spacer_weak_abs()),
    m_use_restarts(params.spacer_restarts()),
    m_restart_initial_threshold(params.spacer_restart_initial_threshold())
{}

context::~context()
{
    reset_lemma_generalizers();
    reset();
}

void context::reset()
{
    TRACE("spacer", tout << "\n";);
    m_pob_queue.reset();
    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (; it != end; ++it) {
        dealloc(it->m_value);
    }
    m_rels.reset();
    m_query = nullptr;
    m_last_result = l_undef;
    m_inductive_lvl = 0;
}

void context::init_rules(datalog::rule_set& rules, decl2rel& rels)
{
    scoped_watch _t_(m_init_rules_watch);
    m_context = &rules.get_context();
    // Allocate collection of predicate transformers
    datalog::rule_set::decl2rules::iterator dit = rules.begin_grouped_rules(), dend = rules.end_grouped_rules();
    decl2rel::obj_map_entry* e;
    for (; dit != dend; ++dit) {
        func_decl* pred = dit->m_key;
        TRACE("spacer", tout << mk_pp(pred, m) << "\n";);
        SASSERT(!rels.contains(pred));
        e = rels.insert_if_not_there2(pred, alloc(pred_transformer, *this,
                                                  get_manager(), pred));
        datalog::rule_vector const& pred_rules = *dit->m_value;
        for (unsigned i = 0; i < pred_rules.size(); ++i) {
            e->get_data().m_value->add_rule(pred_rules[i]);
        }
    }
    datalog::rule_set::iterator rit = rules.begin(), rend = rules.end();
    for (; rit != rend; ++rit) {
        datalog::rule* r = *rit;
        pred_transformer* pt;
        unsigned utz = r->get_uninterpreted_tail_size();
        for (unsigned i = 0; i < utz; ++i) {
            func_decl* pred = r->get_decl(i);
            if (!rels.find(pred, pt)) {
                pt = alloc(pred_transformer, *this, get_manager(), pred);
                rels.insert(pred, pt);
            }
        }
    }
    // Initialize use list dependencies
    decl2rel::iterator it = rels.begin(), end = rels.end();
    for (; it != end; ++it) {
        func_decl* pred = it->m_key;
        pred_transformer* pt = it->m_value, *pt_user;
        obj_hashtable<func_decl> const& deps = rules.get_dependencies().get_deps(pred);
        obj_hashtable<func_decl>::iterator itf = deps.begin(), endf = deps.end();
        for (; itf != endf; ++itf) {
            TRACE("spacer", tout << mk_pp(pred, m) << " " << mk_pp(*itf, m) << "\n";);
            pt_user = rels.find(*itf);
            pt_user->add_use(pt);
        }
    }

    // Initialize the predicate transformers.
    it = rels.begin(), end = rels.end();
    for (; it != end; ++it) {
        pred_transformer& rel = *it->m_value;
        rel.initialize(rels);
        TRACE("spacer", rel.display(tout); );
    }

    // initialize reach facts
    it = rels.begin (), end = rels.end ();
    for (; it != end; ++it)
    { it->m_value->init_reach_facts(); }
}

void context::update_rules(datalog::rule_set& rules)
{
    decl2rel rels;
    init_lemma_generalizers(rules);
    init_rules(rules, rels);
    decl2rel::iterator it = rels.begin(), end = rels.end();
    for (; it != end; ++it) {
        pred_transformer* pt = nullptr;
        if (m_rels.find(it->m_key, pt)) {
            it->m_value->inherit_properties(*pt);
        }
    }
    reset();
    it = rels.begin(), end = rels.end();
    for (; it != end; ++it) {
        m_rels.insert(it->m_key, it->m_value);
    }
}

unsigned context::get_num_levels(func_decl* p)
{
    pred_transformer* pt = nullptr;
    if (m_rels.find(p, pt)) {
        return pt->get_num_levels();
    } else {
        IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
        return 0;
    }
}

expr_ref context::get_cover_delta(int level, func_decl* p_orig, func_decl* p)
{
    pred_transformer* pt = nullptr;
    if (m_rels.find(p, pt)) {
        return pt->get_cover_delta(p_orig, level);
    } else {
        IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
        return expr_ref(m.mk_true(), m);
    }
}

void context::add_cover(int level, func_decl* p, expr* property)
{
    pred_transformer* pt = nullptr;
    if (!m_rels.find(p, pt)) {
        pt = alloc(pred_transformer, *this, get_manager(), p);
        m_rels.insert(p, pt);
        IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
    }
    unsigned lvl = (level == -1)?infty_level():((unsigned)level);
    pt->add_cover(lvl, property);
}

void context::add_invariant (func_decl *p, expr *property)
{add_cover (infty_level(), p, property);}

expr_ref context::get_reachable(func_decl *p)
{
    pred_transformer* pt = nullptr;
    if (!m_rels.find(p, pt))
    { return expr_ref(m.mk_false(), m); }
    return pt->get_reachable();
}

bool context::validate()
{
    if (!m_params.pdr_validate_result()) { return true; }

    std::stringstream msg;

    switch(m_last_result) {
    case l_true: {
        expr_ref cex(m);
        cex = get_ground_sat_answer();
        if (!cex.get()) {
            IF_VERBOSE(0, verbose_stream() << "Cex validation failed\n";);
            throw default_exception("Cex validation failed\n");
            return false;
        }
        break;
    }
    case l_false: {
        expr_ref_vector refs(m);
        expr_ref tmp(m);
        model_ref model;
        model_converter_ref mc;
        vector<relation_info> rs;
        get_level_property(m_inductive_lvl, refs, rs);
        inductive_property ex(m, mc, rs);
        ex.to_model(model);
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        var_subst vs(m, false);
        for (; it != end; ++it) {
            ptr_vector<datalog::rule> const& rules = it->m_value->rules();
            TRACE ("spacer", tout << "PT: " << it->m_value->head ()->get_name ().str ()
                   << "\n";);
            for (unsigned i = 0; i < rules.size(); ++i) {
                datalog::rule& r = *rules[i];

                TRACE ("spacer",
                       get_datalog_context ().
                       get_rule_manager ().
                       display_smt2(r, tout) << "\n";);

                model->eval(r.get_head(), tmp);
                expr_ref_vector fmls(m);
                fmls.push_back(m.mk_not(tmp));
                unsigned utsz = r.get_uninterpreted_tail_size();
                unsigned tsz  = r.get_tail_size();
                for (unsigned j = 0; j < utsz; ++j) {
                    model->eval(r.get_tail(j), tmp);
                    fmls.push_back(tmp);
                }
                for (unsigned j = utsz; j < tsz; ++j) {
                    fmls.push_back(r.get_tail(j));
                }
                tmp = m.mk_and(fmls.size(), fmls.c_ptr());
                svector<symbol> names;
                expr_free_vars fv;
                fv (tmp);
                fv.set_default_sort (m.mk_bool_sort ());

                for (unsigned i = 0; i < fv.size(); ++i) {
                    names.push_back(symbol(fv.size () - i - 1));
                }
                if (!fv.empty()) {
                    fv.reverse ();
                    tmp = m.mk_exists(fv.size(), fv.c_ptr(), names.c_ptr(), tmp);
                }
                smt::kernel solver(m, m_pm.fparams2());
                solver.assert_expr(tmp);
                lbool res = solver.check();
                if (res != l_false) {
                    msg << "rule validation failed when checking: "
                        << mk_pp(tmp, m);
                    IF_VERBOSE(0, verbose_stream() << msg.str() << "\n";);
                    throw default_exception(msg.str());
                    return false;
                }
            }
        }
        TRACE ("spacer", tout << "Validation Succeeded\n";);
        break;
    }
    default:
        break;
    }
    return true;
}


void context::reset_lemma_generalizers()
{
    std::for_each(m_lemma_generalizers.begin(), m_lemma_generalizers.end(),
                  delete_proc<lemma_generalizer>());
    m_lemma_generalizers.reset();
}

void context::init_lemma_generalizers(datalog::rule_set& rules)
{
    reset_lemma_generalizers();
    m.toggle_proof_mode(PGM_ENABLED);
    smt_params &fparams = m_pm.fparams ();
    if (!m_params.spacer_eq_prop ()) {
        fparams.m_arith_bound_prop = BP_NONE;
        fparams.m_arith_auto_config_simplex = true;
        fparams.m_arith_propagate_eqs = false;
        fparams.m_arith_eager_eq_axioms = false;
    }
    fparams.m_random_seed = m_params.spacer_random_seed ();

    fparams.m_dump_benchmarks = m_params.spacer_vs_dump_benchmarks();
    fparams.m_dump_min_time = m_params.spacer_vs_dump_min_time();
    fparams.m_dump_recheck = m_params.spacer_vs_recheck();

    fparams.m_mbqi = m_params.spacer_mbqi();

    if (get_params().spacer_use_eqclass()) {
        m_lemma_generalizers.push_back (alloc(lemma_eq_generalizer, *this));
    }

    // -- AG: commented out because it is causing performance issues at the moment
    //m_lemma_generalizers.push_back (alloc (unsat_core_generalizer, *this));

    if (m_params.pdr_use_inductive_generalizer()) {
        m_lemma_generalizers.push_back(alloc(lemma_bool_inductive_generalizer, *this, 0));
    }

    if (m_params.spacer_use_array_eq_generalizer()) {
        m_lemma_generalizers.push_back(alloc(lemma_array_eq_generalizer, *this));
    }

    if (get_params().spacer_lemma_sanity_check()) {
        m_lemma_generalizers.push_back(alloc(lemma_sanity_checker, *this));
    }

}

void context::get_level_property(unsigned lvl, expr_ref_vector& res,
                                 vector<relation_info>& rs) const
{
    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (; it != end; ++it) {
        pred_transformer* r = it->m_value;
        if (r->head() == m_query_pred) {
            continue;
        }
        expr_ref conj = r->get_formulas(lvl, false);
        m_pm.formula_n2o(0, false, conj);
        res.push_back(conj);
        ptr_vector<func_decl> sig(r->head()->get_arity(), r->sig());
        rs.push_back(relation_info(m, r->head(), sig, conj));
    }
}

void context::simplify_formulas()
{
    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (; it != end; ++it) {
        pred_transformer* r = it->m_value;
        r->simplify_formulas();
    }
}

lbool context::solve(unsigned from_lvl)
{
    m_last_result = l_undef;
    try {
        m_last_result = solve_core (from_lvl);
        if (m_last_result == l_false) {
            simplify_formulas();
            m_last_result = l_false;
            IF_VERBOSE(1, {
                    expr_ref_vector refs(m);
                    vector<relation_info> rs;
                    get_level_property(m_inductive_lvl, refs, rs);
                    model_converter_ref mc;
                    inductive_property ex(m, mc, rs);
                    verbose_stream() << ex.to_string();
                });

            // upgrade invariants that are known to be inductive.
            // decl2rel::iterator it = m_rels.begin (), end = m_rels.end ();
            // for (; m_inductive_lvl > 0 && it != end; ++it) {
            //   if (it->m_value->head() != m_query_pred) {
            //     it->m_value->propagate_to_infinity (m_inductive_lvl);
            //   }
            // }
        }
        VERIFY (validate ());
    } catch (unknown_exception)
    {}

    if (m_last_result == l_true) {
        m_stats.m_cex_depth = get_cex_depth ();
    }

    if (m_params.print_statistics ()) {
        statistics st;
        collect_statistics (st);
        st.display_smt2 (verbose_stream ());
    }

    return m_last_result;
}


void context::checkpoint()
{
    if (m.canceled ()) {
        throw default_exception("spacer canceled");
    }
}

unsigned context::get_cex_depth()
{
    if (m_last_result != l_true) {
        IF_VERBOSE(1,
                   verbose_stream ()
                   << "Trace unavailable when result is false\n";);
        return 0;
    }

    // treat the following as queues: read from left to right and insert at right
    ptr_vector<func_decl> preds;
    ptr_vector<pred_transformer> pts;
    reach_fact_ref_vector facts;

    // temporary
    reach_fact* fact;
    datalog::rule const* r;
    pred_transformer* pt;

    // get and discard query rule
    fact = m_query->get_last_reach_fact ();
    r = &fact->get_rule ();

    unsigned cex_depth = 0;

    // initialize queues
    // assume that the query is only on a single predicate
    // (i.e. disallow fancy queries for now)
    facts.append (fact->get_justifications ());
    if (facts.size() != 1) {
        // XXX AG: Escape if an assertion is about to fail
        IF_VERBOSE(1,
                   verbose_stream () <<
                   "Warning: counterexample is trivial or non-existent\n";);
        return cex_depth;
    }
    SASSERT (facts.size () == 1);
    m_query->find_predecessors (*r, preds);
    SASSERT (preds.size () == 1);
    pts.push_back (&(get_pred_transformer (preds[0])));

    pts.push_back (NULL); // cex depth marker

    // bfs traversal of the query derivation tree
    for (unsigned curr = 0; curr < pts.size (); curr++) {
        // get current pt and fact
        pt = pts.get (curr);
        // check for depth marker
        if (pt == nullptr) {
            ++cex_depth;
            // insert new marker if there are pts at higher depth
            if (curr + 1 < pts.size()) { pts.push_back(NULL); }
            continue;
        }
        fact = facts.get (curr - cex_depth); // discount the number of markers
        // get rule justifying the derivation of fact at pt
        r = &fact->get_rule ();
        TRACE ("spacer",
               tout << "next rule: " << r->name ().str () << "\n";
            );
        // add child facts and pts
        facts.append (fact->get_justifications ());
        pt->find_predecessors (*r, preds);
        for (unsigned j = 0; j < preds.size (); j++) {
            pts.push_back (&(get_pred_transformer (preds[j])));
        }
    }

    return cex_depth;
}

/**
   \brief retrieve answer.
*/

void context::get_rules_along_trace(datalog::rule_ref_vector& rules)
{
    if (m_last_result != l_true) {
        IF_VERBOSE(1,
                   verbose_stream ()
                   << "Trace unavailable when result is false\n";);
        return;
    }

    // treat the following as queues: read from left to right and insert at right
    ptr_vector<func_decl> preds;
    ptr_vector<pred_transformer> pts;
    reach_fact_ref_vector facts;

    // temporary
    reach_fact* fact;
    datalog::rule const* r;
    pred_transformer* pt;

    // get query rule
    fact = m_query->get_last_reach_fact ();
    r = &fact->get_rule ();
    rules.push_back (const_cast<datalog::rule *> (r));
    TRACE ("spacer",
           tout << "Initial rule: " << r->name().str() << "\n";
        );

    // initialize queues
    // assume that the query is only on a single predicate
    // (i.e. disallow fancy queries for now)
    facts.append (fact->get_justifications ());
    if (facts.size() != 1) {
        // XXX AG: Escape if an assertion is about to fail
        IF_VERBOSE(1,
                   verbose_stream () <<
                   "Warning: counterexample is trivial or non-existent\n";);
        return;
    }
    SASSERT (facts.size () == 1);
    m_query->find_predecessors (*r, preds);
    SASSERT (preds.size () == 1);
    pts.push_back (&(get_pred_transformer (preds[0])));

    // populate rules according to a preorder traversal of the query derivation tree
    for (unsigned curr = 0; curr < pts.size (); curr++) {
        // get current pt and fact
        pt = pts.get (curr);
        fact = facts.get (curr);
        // get rule justifying the derivation of fact at pt
        r = &fact->get_rule ();
        rules.push_back (const_cast<datalog::rule *> (r));
        TRACE ("spacer",
               tout << "next rule: " << r->name ().str () << "\n";
            );
        // add child facts and pts
        facts.append (fact->get_justifications ());
        pt->find_predecessors (*r, preds);
        for (unsigned j = 0; j < preds.size (); j++) {
            pts.push_back (&(get_pred_transformer (preds[j])));
        }
    }
}

model_ref context::get_model()
{
    model_ref model;
    expr_ref_vector refs(m);
    vector<relation_info> rs;
    get_level_property(m_inductive_lvl, refs, rs);
    inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
    ex.to_model (model);
    return model;
}

proof_ref context::get_proof() const
{
    return proof_ref (m);
}

expr_ref context::get_answer()
{
    switch(m_last_result) {
    case l_true:
        return mk_sat_answer();
    case l_false:
        return mk_unsat_answer();
    default:
        return expr_ref(m.mk_true(), m);
    }
}

/**
   \brief Retrieve satisfying assignment with explanation.
*/
expr_ref context::mk_sat_answer() {return get_ground_sat_answer();}


expr_ref context::mk_unsat_answer() const
{
    expr_ref_vector refs(m);
    vector<relation_info> rs;
    get_level_property(m_inductive_lvl, refs, rs);
    inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
    return ex.to_expr();
}

expr_ref context::get_ground_sat_answer()
{
    if (m_last_result != l_true) {
        verbose_stream () << "Sat answer unavailable when result is false\n";
        return expr_ref (m);
    }

    // treat the following as queues: read from left to right and insert at the right
    reach_fact_ref_vector reach_facts;
    ptr_vector<func_decl> preds;
    ptr_vector<pred_transformer> pts;
    expr_ref_vector cex (m), // pre-order list of ground instances of predicates
        cex_facts (m); // equalities for the ground cex using signature constants

    // temporary
    reach_fact *reach_fact;
    pred_transformer* pt;
    expr_ref cex_fact (m);
    datalog::rule const* r;

    // get and discard query rule
    reach_fact = m_query->get_last_reach_fact ();
    r = &reach_fact->get_rule ();

    // initialize queues
    reach_facts.append (reach_fact->get_justifications ());
    if (reach_facts.size() != 1) {
        // XXX Escape if an assertion is about to fail
        IF_VERBOSE(1,
                   verbose_stream () <<
                   "Warning: counterexample is trivial or non-existent\n";);
        return expr_ref(m.mk_true(), m);
    }
    m_query->find_predecessors (*r, preds);
    SASSERT (preds.size () == 1);
    pts.push_back (&(get_pred_transformer (preds[0])));
    cex_facts.push_back (m.mk_true ());

    // XXX a hack to avoid assertion when query predicate is not nullary
    if (preds[0]->get_arity () == 0)
    { cex.push_back(m.mk_const(preds[0])); }

    // smt context to obtain local cexes
    scoped_ptr<smt::kernel> cex_ctx = alloc (smt::kernel, m, m_pm.fparams2 ());
    model_evaluator_util mev (m);

    // preorder traversal of the query derivation tree
    for (unsigned curr = 0; curr < pts.size (); curr++) {
        // pick next pt, fact, and cex_fact
        pt = pts.get (curr);
        reach_fact = reach_facts[curr];

        cex_fact = cex_facts.get (curr);

        ptr_vector<pred_transformer> child_pts;

        // get justifying rule and child facts for the derivation of reach_fact at pt
        r = &reach_fact->get_rule ();
        const reach_fact_ref_vector &child_reach_facts =
            reach_fact->get_justifications ();
        // get child pts
        preds.reset();
        pt->find_predecessors(*r, preds);
        for (unsigned j = 0; j < preds.size (); j++) {
            child_pts.push_back (&(get_pred_transformer (preds[j])));
        }
        // update the queues
        reach_facts.append (child_reach_facts);
        pts.append (child_pts);

        // update cex and cex_facts by making a local sat check:
        // check consistency of reach facts of children, rule body, and cex_fact
        cex_ctx->push ();
        cex_ctx->assert_expr (cex_fact);
        unsigned u_tail_sz = r->get_uninterpreted_tail_size ();
        SASSERT (child_reach_facts.size () == u_tail_sz);
        for (unsigned i = 0; i < u_tail_sz; i++) {
            expr_ref ofml (m);
            child_pts.get (i)->get_manager ().formula_n2o
                (child_reach_facts[i]->get (), ofml, i);
            cex_ctx->assert_expr (ofml);
        }
        cex_ctx->assert_expr (pt->transition ());
        cex_ctx->assert_expr (pt->rule2tag (r));
        lbool res = cex_ctx->check ();
        CTRACE("cex", res == l_false,
               tout << "Cex fact: " << mk_pp(cex_fact, m) << "\n";
               for (unsigned i = 0; i < u_tail_sz; i++)
                   tout << "Pre" << i << " "
                        << mk_pp(child_reach_facts[i]->get(), m) << "\n";
               tout << "Rule: ";
               get_datalog_context().get_rule_manager().display_smt2(*r, tout) << "\n";
            );
        VERIFY (res == l_true);
        model_ref local_mdl;
        cex_ctx->get_model (local_mdl);
        cex_ctx->pop (1);

        model_evaluator_util mev (m);
        mev.set_model (*local_mdl);
        for (unsigned i = 0; i < child_pts.size (); i++) {
            pred_transformer& ch_pt = *(child_pts.get (i));
            unsigned sig_size = ch_pt.sig_size ();
            expr_ref_vector ground_fact_conjs (m);
            expr_ref_vector ground_arg_vals (m);
            for (unsigned j = 0; j < sig_size; j++) {
                expr_ref sig_arg (m), sig_val (m);
                sig_arg = m.mk_const (ch_pt.get_manager ().o2o (ch_pt.sig (j), 0, i));
                VERIFY(mev.eval (sig_arg, sig_val, true));
                ground_fact_conjs.push_back (m.mk_eq (sig_arg, sig_val));
                ground_arg_vals.push_back (sig_val);
            }
            if (ground_fact_conjs.size () > 0) {
                expr_ref ground_fact (m);
                ground_fact = m.mk_and (ground_fact_conjs.size (), ground_fact_conjs.c_ptr ());
                ch_pt.get_manager ().formula_o2n (ground_fact, ground_fact, i);
                cex_facts.push_back (ground_fact);
            } else {
                cex_facts.push_back (m.mk_true ());
            }
            cex.push_back (m.mk_app (ch_pt.head (), sig_size, ground_arg_vals.c_ptr ()));
        }
    }

    TRACE ("spacer",
           tout << "ground cex\n";
           for (unsigned i = 0; i < cex.size (); i++) {
               tout << mk_pp (cex.get (i), m) << "\n";
           }
        );

    return expr_ref (m.mk_and (cex.size (), cex.c_ptr ()), m);
}

///this is where everything starts
lbool context::solve_core (unsigned from_lvl)
{
    scoped_watch _w_(m_solve_watch);
    //if there is no query predicate, abort
    if (!m_rels.find(m_query_pred, m_query)) { return l_false; }

    unsigned lvl = from_lvl;

    pob *root = m_query->mk_pob(nullptr,from_lvl,0,m.mk_true());
    m_pob_queue.set_root (*root);

    unsigned max_level = get_params ().spacer_max_level ();

    for (unsigned i = 0; i < max_level; ++i) {
        checkpoint();
        m_expanded_lvl = infty_level ();
        m_stats.m_max_query_lvl = lvl;

        if (check_reachability()) { return l_true; }

        if (lvl > 0 && !get_params ().spacer_skip_propagate ())
            if (propagate(m_expanded_lvl, lvl, UINT_MAX)) { return l_false; }

        m_pob_queue.inc_level ();
        lvl = m_pob_queue.max_level ();
        m_stats.m_max_depth = std::max(m_stats.m_max_depth, lvl);
        IF_VERBOSE(1,verbose_stream() << "Entering level "<< lvl << "\n";);

        STRACE("spacer.expand-add", tout << "\n* LEVEL " << lvl << "\n";);

        IF_VERBOSE(1,
                   if (m_params.print_statistics ()) {
                       statistics st;
                       collect_statistics (st);
                   };
            );
    }
    // communicate failure to datalog::context
    if (m_context) { m_context->set_status(datalog::BOUNDED); }
    return l_undef;
}


//
bool context::check_reachability ()
{
    scoped_watch _w_(m_reach_watch);

    timeit _timer (get_verbosity_level () >= 1,
                   "spacer::context::check_reachability",
                   verbose_stream ());

    pob_ref last_reachable;

    if (get_params().spacer_reset_obligation_queue()) { m_pob_queue.reset(); }

    unsigned initial_size = m_stats.m_num_lemmas;
    unsigned threshold = m_restart_initial_threshold;
    unsigned luby_idx = 1;

    while (m_pob_queue.top()) {
        pob_ref node;
        checkpoint ();

        while (last_reachable) {
            checkpoint ();
            node = last_reachable;
            last_reachable = nullptr;
            if (m_pob_queue.is_root(*node)) { return true; }
            if (is_reachable (*node->parent())) {
                last_reachable = node->parent ();
                SASSERT(last_reachable->is_closed());
                last_reachable->close ();
            } else if (!node->parent()->is_closed()) {
                /* bump node->parent */
                node->parent ()->bump_weakness();
            }
        }

        SASSERT (m_pob_queue.top ());
        // -- remove all closed nodes and updated all dirty nodes
        // -- this is necessary because there is no easy way to
        // -- remove nodes from the priority queue.
        while (m_pob_queue.top ()->is_closed () ||
               m_pob_queue.top()->is_dirty()) {
            pob_ref n = m_pob_queue.top ();
            m_pob_queue.pop ();
            if (n->is_closed()) {
                IF_VERBOSE (1,
                            verbose_stream () << "Deleting closed node: "
                            << n->pt ().head ()->get_name ()
                            << "(" << n->level () << ", " << n->depth () << ")"
                            << " " << n->post ()->get_id () << "\n";);
                if (m_pob_queue.is_root(*n)) { return true; }
                SASSERT (m_pob_queue.top ());
            } else if (n->is_dirty()) {
                n->clean ();
                // -- the node n might not be at the top after it is cleaned
                m_pob_queue.push (*n);
            } else
            { UNREACHABLE(); }
        }

        SASSERT (m_pob_queue.top ());

        if (m_use_restarts && m_stats.m_num_lemmas - initial_size > threshold) {
            luby_idx++;
            m_stats.m_num_restarts++;
            threshold =
                static_cast<unsigned>(get_luby(luby_idx)) * m_restart_initial_threshold;
            IF_VERBOSE (1, verbose_stream ()
                        << "(restarting :lemmas " << m_stats.m_num_lemmas
                        << " :restart_threshold " << threshold
                        << ")\n";);
            // -- clear obligation queue up to the root
            while (!m_pob_queue.is_root(*m_pob_queue.top())) { m_pob_queue.pop(); }
            initial_size = m_stats.m_num_lemmas;
        }

        node = m_pob_queue.top ();
        SASSERT (node->level () <= m_pob_queue.max_level ());
        switch (expand_node(*node)) {
        case l_true:
            SASSERT (m_pob_queue.top () == node.get ());
            m_pob_queue.pop ();
            last_reachable = node;
            last_reachable->close ();
            if (m_pob_queue.is_root(*node)) { return true; }
            break;
        case l_false:
            SASSERT (m_pob_queue.top () == node.get ());
            m_pob_queue.pop ();

            if (node->is_dirty()) { node->clean(); }

            node->inc_level ();
            if (get_params ().pdr_flexible_trace () &&
                (node->level () >= m_pob_queue.max_level () ||
                 m_pob_queue.max_level () - node->level ()
                 <= get_params ().pdr_flexible_trace_depth ()))
            { m_pob_queue.push(*node); }

            if (m_pob_queue.is_root(*node)) { return false; }
            break;
        case l_undef:
            // SASSERT (m_pob_queue.top () != node.get ());
            break;
        }
    }

    UNREACHABLE();
    return false;
}

/// check whether node n is concretely reachable
bool context::is_reachable(pob &n)
{
    scoped_watch _w_(m_is_reach_watch);
    // XXX hold a reference for n during this call.
    // XXX Should convert is_reachable() to accept pob_ref as argument
    pob_ref nref(&n);

    TRACE ("spacer",
           tout << "is-reachable: " << n.pt().head()->get_name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
           << mk_pp(n.post(), m) << "\n";);

    stopwatch watch;
    IF_VERBOSE (1, verbose_stream () << "is-reachable: " << n.pt ().head ()->get_name ()
                << " (" << n.level () << ", "
                << (n.depth () - m_pob_queue.min_depth ()) << ") "
                << (n.use_farkas_generalizer () ? "FAR " : "SUB ")
                << n.post ()->get_id ();
                verbose_stream().flush ();
                watch.start (););

    // used in case n is unreachable
    unsigned uses_level = infty_level ();
    model_ref model;

    // used in case n is reachable
    bool is_concrete;
    const datalog::rule * r = nullptr;
    // denotes which predecessor's (along r) reach facts are used
    vector<bool> reach_pred_used;
    unsigned num_reuse_reach = 0;

    unsigned saved = n.level ();
    n.m_level = infty_level ();
    lbool res = n.pt().is_reachable(n, nullptr, &model,
                                    uses_level, is_concrete, r,
                                    reach_pred_used, num_reuse_reach);
    n.m_level = saved;

    if (res != l_true || !is_concrete) {
        IF_VERBOSE(1, verbose_stream () << " F "
                   << std::fixed << std::setprecision(2)
                   << watch.get_seconds () << "\n";);
        return false;
    }
    SASSERT(res == l_true);
    SASSERT(is_concrete);

    model_evaluator_util mev (m);
    mev.set_model(*model);
    // -- update must summary
    if (r && r->get_uninterpreted_tail_size () > 0) {
        reach_fact_ref rf = mk_reach_fact (n, mev, *r);
        n.pt ().add_reach_fact (rf.get ());
    }

    // if n has a derivation, create a new child and report l_undef
    // otherwise if n has no derivation or no new children, report l_true
    pob *next = nullptr;
    scoped_ptr<derivation> deriv;
    if (n.has_derivation()) {deriv = n.detach_derivation();}

    // -- close n, it is reachable
    // -- don't worry about removing n from the obligation queue
    n.close ();

    if (deriv) {
        next = deriv->create_next_child ();
        if (next) {
            SASSERT(!next->is_closed());
            // move derivation over to the next obligation
            next->set_derivation(deriv.detach());

            // remove the current node from the queue if it is at the top
            if (m_pob_queue.top() == &n) { m_pob_queue.pop(); }

            m_pob_queue.push(*next);
        }
    }

    // either deriv was a nullptr or it was moved into next
    SASSERT(!next || !deriv);


    IF_VERBOSE(1, verbose_stream () << (next ? " X " : " T ")
               << std::fixed << std::setprecision(2)
               << watch.get_seconds () << "\n";);

    // recurse on the new proof obligation
    return next ? is_reachable(*next) : true;
}

//this processes a goal and creates sub-goal
lbool context::expand_node(pob& n)
{
    TRACE ("spacer",
           tout << "expand-node: " << n.pt().head()->get_name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
           << mk_pp(n.post(), m) << "\n";);

    STRACE ("spacer.expand-add",
            tout << "expand-node: " << n.pt().head()->get_name()
            << " level: " << n.level()
            << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
            << mk_epp(n.post(), m) << "\n\n";);

    TRACE ("core_array_eq",
           tout << "expand-node: " << n.pt().head()->get_name()
           << " level: " << n.level()
           << " depth: " << (n.depth () - m_pob_queue.min_depth ()) << "\n"
           << mk_pp(n.post(), m) << "\n";);

    stopwatch watch;
    IF_VERBOSE (1, verbose_stream () << "expand: " << n.pt ().head ()->get_name ()
                << " (" << n.level () << ", "
                << (n.depth () - m_pob_queue.min_depth ()) << ") "
                << (n.use_farkas_generalizer () ? "FAR " : "SUB ")
                << " w(" << n.weakness() << ") "
                << n.post ()->get_id ();
                verbose_stream().flush ();
                watch.start (););

    // used in case n is unreachable
    unsigned uses_level = infty_level ();
    expr_ref_vector cube(m);
    model_ref model;

    // used in case n is reachable
    bool is_concrete;
    const datalog::rule * r = nullptr;
    // denotes which predecessor's (along r) reach facts are used
    vector<bool> reach_pred_used;
    unsigned num_reuse_reach = 0;


    if (get_params().pdr_flexible_trace() && n.pt().is_blocked(n, uses_level)) {
        // if (!m_pob_queue.is_root (n)) n.close ();
        IF_VERBOSE (1, verbose_stream () << " K "
                    << std::fixed << std::setprecision(2)
                    << watch.get_seconds () << "\n";);

        return l_false;
    }

    smt_params &fparams = m_pm.fparams();
    flet<bool> _arith_ignore_int_(fparams.m_arith_ignore_int,
                                  m_weak_abs && n.weakness() < 1);
    flet<bool> _array_weak_(fparams.m_array_weak,
                            m_weak_abs && n.weakness() < 2);

    lbool res = n.pt ().is_reachable (n, &cube, &model, uses_level, is_concrete, r,
                                      reach_pred_used, num_reuse_reach);
    checkpoint ();
    IF_VERBOSE (1, verbose_stream () << "." << std::flush;);
    switch (res) {
        //reachable but don't know if this is purely using UA
    case l_true: {
        // update stats
        m_stats.m_num_reuse_reach += num_reuse_reach;

        model_evaluator_util mev (m);
        mev.set_model (*model);
        // must-reachable
        if (is_concrete) {
            // -- update must summary
            if (r && r->get_uninterpreted_tail_size() > 0) {
                reach_fact_ref rf = mk_reach_fact (n, mev, *r);
                checkpoint ();
                n.pt ().add_reach_fact (rf.get ());
                checkpoint ();
            }

            // if n has a derivation, create a new child and report l_undef
            // otherwise if n has no derivation or no new children, report l_true
            pob *next = nullptr;
            scoped_ptr<derivation> deriv;
            if (n.has_derivation()) {deriv = n.detach_derivation();}

            // -- close n, it is reachable
            // -- don't worry about removing n from the obligation queue
            n.close ();

            if (deriv) {
                next = deriv->create_next_child ();
                checkpoint ();
                if (next) {
                    // move derivation over to the next obligation
                    next->set_derivation (deriv.detach());

                    // remove the current node from the queue if it is at the top
                    if (m_pob_queue.top() == &n) { m_pob_queue.pop(); }

                    m_pob_queue.push (*next);
                }
            }


            IF_VERBOSE(1, verbose_stream () << (next ? " X " : " T ")
                       << std::fixed << std::setprecision(2)
                       << watch.get_seconds () << "\n";);
            return next ? l_undef : l_true;
        }

        // create a child of n
        VERIFY(create_children (n, *r, mev, reach_pred_used));
        IF_VERBOSE(1, verbose_stream () << " U "
                   << std::fixed << std::setprecision(2)
                   << watch.get_seconds () << "\n";);
        return l_undef;

    }
        // n is unreachable, create new summary facts
    case l_false: {
        timeit _timer (is_trace_enabled("spacer_timeit"),
                       "spacer::expand_node::false",
                       verbose_stream ());

        // -- only update expanded level when new lemmas are generated at it.
        if (n.level() < m_expanded_lvl) { m_expanded_lvl = n.level(); }

        TRACE("spacer", tout << "cube:\n";
              for (unsigned j = 0; j < cube.size(); ++j)
                  tout << mk_pp(cube[j].get(), m) << "\n";);


        pob_ref nref(&n);
        // -- create lemma from a pob and last unsat core
        lemma_ref lemma = alloc(class lemma, pob_ref(&n), cube, uses_level);

        // -- run all lemma generalizers
        for (unsigned i = 0;
             // -- only generalize if lemma was constructed using farkas
             n.use_farkas_generalizer () && !lemma->is_false() &&
                 i < m_lemma_generalizers.size(); ++i) {
            checkpoint ();
            (*m_lemma_generalizers[i])(lemma);
        }

        TRACE("spacer", tout << "invariant state: "
              << (is_infty_level(lemma->level())?"(inductive)":"")
              <<  mk_pp(lemma->get_expr(), m) << "\n";);

        bool v = n.pt().add_lemma (lemma.get());
        if (v) { m_stats.m_num_lemmas++; }

        // Optionally update the node to be the negation of the lemma
        if (v && get_params().spacer_use_lemma_as_cti()) {
            n.new_post (mk_and(lemma->get_cube()));
            n.set_farkas_generalizer (false);
        }
        CASSERT("spacer", n.level() == 0 || check_invariant(n.level()-1));


        IF_VERBOSE(1, verbose_stream () << " F "
                   << std::fixed << std::setprecision(2)
                   << watch.get_seconds () << "\n";);

        return l_false;
    }
    case l_undef:
        // something went wrong
        if (n.weakness() < 100 /* MAX_WEAKENSS */) {
            bool has_new_child = false;
            SASSERT(m_weak_abs);
            m_stats.m_expand_node_undef++;
            if (r && r->get_uninterpreted_tail_size() > 0) {
                model_evaluator_util mev(m);
                mev.set_model(*model);
                // do not trust reach_pred_used
                for (unsigned i = 0, sz = reach_pred_used.size(); i < sz; ++i)
                { reach_pred_used[i] = false; }
                has_new_child = create_children(n,*r,mev,reach_pred_used);
            }
            IF_VERBOSE(1, verbose_stream() << " UNDEF "
                       << std::fixed << std::setprecision(2)
                       << watch.get_seconds () << "\n";);
            if (has_new_child) { return l_undef; }

            // -- failed to create a child, bump weakness and repeat
            // -- the recursion is bounded by the levels of weakness supported
            n.bump_weakness();
            return expand_node(n);
        }
        TRACE("spacer", tout << "unknown state: "
              << mk_pp(m_pm.mk_and(cube), m) << "\n";);
        throw unknown_exception();
    }
    UNREACHABLE();
    throw unknown_exception();
}

//
// check if predicate transformer has a satisfiable predecessor state.
// returns either a satisfiable predecessor state or
// return a property that blocks state and is implied by the
// predicate transformer (or some unfolding of it).
//

bool context::propagate(unsigned min_prop_lvl,
                        unsigned max_prop_lvl, unsigned full_prop_lvl)
{
    scoped_watch _w_(m_propagate_watch);

    if (min_prop_lvl == infty_level()) { return false; }

    timeit _timer (get_verbosity_level() >= 1,
                   "spacer::context::propagate",
                   verbose_stream ());

    if (full_prop_lvl < max_prop_lvl) { full_prop_lvl = max_prop_lvl; }

    if (m_params.pdr_simplify_formulas_pre()) {
        simplify_formulas();
    }
    IF_VERBOSE (1, verbose_stream () << "Propagating: " << std::flush;);

    for (unsigned lvl = min_prop_lvl; lvl <= full_prop_lvl; lvl++) {
        IF_VERBOSE (1,
                    if (lvl > max_prop_lvl && lvl == max_prop_lvl + 1)
                        verbose_stream () << " ! ";
                    verbose_stream () << lvl << " " << std::flush;);

        checkpoint();
        CTRACE ("spacer", lvl > max_prop_lvl && lvl == max_prop_lvl + 1,
                tout << "In full propagation\n";);

        bool all_propagated = true;
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            checkpoint();
            pred_transformer& r = *it->m_value;
            all_propagated = r.propagate_to_next_level(lvl) && all_propagated;
        }
        //CASSERT("spacer", check_invariant(lvl));

        if (all_propagated) {
            for (it = m_rels.begin(); it != end; ++it) {
                checkpoint ();
                pred_transformer& r = *it->m_value;
                r.propagate_to_infinity (lvl);
            }
            if (lvl <= max_prop_lvl) {
                m_inductive_lvl = lvl;
                IF_VERBOSE(1, verbose_stream () << "\n";);
                return true;
            }
            break;
        }

        if (all_propagated && lvl == max_prop_lvl) {
            m_inductive_lvl = lvl;
            return true;
        } else if (all_propagated && lvl > max_prop_lvl) { break; }
    }
    if (m_params.pdr_simplify_formulas_post()) {
        simplify_formulas();
    }

    IF_VERBOSE(1, verbose_stream () << "\n";);
    return false;
}

reach_fact *context::mk_reach_fact (pob& n, model_evaluator_util &mev,
                                    const datalog::rule& r)
{
    timeit _timer1 (is_trace_enabled("spacer_timeit"),
                    "mk_reach_fact",
                    verbose_stream ());
    expr_ref res(m);
    reach_fact_ref_vector child_reach_facts;

    pred_transformer& pt = n.pt ();

    ptr_vector<func_decl> preds;
    pt.find_predecessors (r, preds);

    expr_ref_vector path_cons (m);
    path_cons.push_back (pt.get_transition (r));
    app_ref_vector vars (m);

    for (unsigned i = 0; i < preds.size (); i++) {
        func_decl* pred = preds[i];
        pred_transformer& ch_pt = get_pred_transformer (pred);
        // get a reach fact of body preds used in the model
        expr_ref o_ch_reach (m);
        reach_fact *kid = ch_pt.get_used_origin_reach_fact (mev, i);
        child_reach_facts.push_back (kid);
        m_pm.formula_n2o (kid->get (), o_ch_reach, i);
        path_cons.push_back (o_ch_reach);
        // collect o-vars to eliminate
        for (unsigned j = 0; j < pred->get_arity (); j++)
        { vars.push_back(m.mk_const(m_pm.o2o(ch_pt.sig(j), 0, i))); }

        const ptr_vector<app> &v = kid->aux_vars ();
        for (unsigned j = 0, sz = v.size (); j < sz; ++j)
        { vars.push_back(m.mk_const(m_pm.n2o(v [j]->get_decl(), i))); }
    }
    // collect aux vars to eliminate
    ptr_vector<app>& aux_vars = pt.get_aux_vars (r);
    bool elim_aux = get_params ().spacer_elim_aux ();
    if (elim_aux) { vars.append(aux_vars.size(), aux_vars.c_ptr()); }

    res = m_pm.mk_and (path_cons);

    // -- pick an implicant from the path condition
    if (get_params().spacer_reach_dnf()) {
        expr_ref_vector u(m), lits(m);
        u.push_back (res);
        compute_implicant_literals (mev, u, lits);
        res = m_pm.mk_and (lits);
    }


    TRACE ("spacer",
           tout << "Reach fact, before QE:\n";
           tout << mk_pp (res, m) << "\n";
           tout << "Vars:\n";
           for (unsigned i = 0; i < vars.size(); ++i) {
               tout << mk_pp(vars.get (i), m) << "\n";
           }
        );

    {
        timeit _timer1 (is_trace_enabled("spacer_timeit"),
                        "mk_reach_fact::qe_project",
                        verbose_stream ());
        qe_project (m, vars, res, mev.get_model (), false, m_use_native_mbp);
    }


    TRACE ("spacer",
           tout << "Reach fact, after QE project:\n";
           tout << mk_pp (res, m) << "\n";
           tout << "Vars:\n";
           for (unsigned i = 0; i < vars.size(); ++i) {
               tout << mk_pp(vars.get (i), m) << "\n";
           }
        );

    SASSERT (vars.empty ());

    m_stats.m_num_reach_queries++;
    ptr_vector<app> empty;
    reach_fact *f = alloc(reach_fact, m, r, res, elim_aux ? empty : aux_vars);
    for (unsigned i = 0, sz = child_reach_facts.size (); i < sz; ++i)
    { f->add_justification(child_reach_facts.get(i)); }
    return f;
}


/**
   \brief create children states from model cube.
*/
bool context::create_children(pob& n, datalog::rule const& r,
                              model_evaluator_util &mev,
                              const vector<bool> &reach_pred_used)
{

    scoped_watch _w_ (m_create_children_watch);
    pred_transformer& pt = n.pt();
    expr* const T   = pt.get_transition(r);
    expr* const phi = n.post();

    TRACE("spacer",
          tout << "Model:\n";
          model_smt2_pp(tout, m, *mev.get_model (), 0);
          tout << "\n";
          tout << "Transition:\n" << mk_pp(T, m) << "\n";
          tout << "Phi:\n" << mk_pp(phi, m) << "\n";);

    SASSERT (r.get_uninterpreted_tail_size () > 0);

    ptr_vector<func_decl> preds;
    pt.find_predecessors(r, preds);

    ptr_vector<pred_transformer> pred_pts;

    for (ptr_vector<func_decl>::iterator it = preds.begin ();
         it != preds.end (); it++) {
        pred_pts.push_back (&get_pred_transformer (*it));
    }

    expr_ref_vector forms(m), Phi(m);

    // obtain all formulas to consider for model generalization
    forms.push_back(T);
    forms.push_back(phi);

    compute_implicant_literals (mev, forms, Phi);

    //pt.remove_predecessors (Phi);

    app_ref_vector vars(m);
    unsigned sig_size = pt.head()->get_arity();
    for (unsigned i = 0; i < sig_size; ++i) {
        vars.push_back(m.mk_const(m_pm.o2n(pt.sig(i), 0)));
    }
    ptr_vector<app>& aux_vars = pt.get_aux_vars(r);
    vars.append(aux_vars.size(), aux_vars.c_ptr());

    n.get_skolems(vars);

    expr_ref phi1 = m_pm.mk_and (Phi);
    qe_project (m, vars, phi1, mev.get_model (), true,
                m_use_native_mbp, !m_ground_cti);
    //qe::reduce_array_selects (*mev.get_model (), phi1);
    SASSERT (!m_ground_cti || vars.empty ());

    TRACE ("spacer",
           tout << "Implicant\n";
           tout << mk_pp (m_pm.mk_and (Phi), m) << "\n";
           tout << "Projected Implicant\n" << mk_pp (phi1, m) << "\n";
        );

    // expand literals. Ideally, we do not want to split aliasing
    // equalities. Unfortunately, the interface does not allow for
    // that yet.
    // XXX This mixes up with derivation. Needs more thought.
    // Phi.reset ();
    // flatten_and (phi1, Phi);
    // if (!Phi.empty ())
    // {
    //   expand_literals (m, Phi);
    //   phi1 = m_pm.mk_and (Phi);
    // }


    derivation *deriv = alloc (derivation, n, r, phi1, vars);
    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
        unsigned j;
        if (get_params ().spacer_order_children () == 1)
            // -- reverse order
        { j = sz - i - 1; }
        else
            // -- default order
        { j = i; }

        pred_transformer &pt = get_pred_transformer (preds [j]);

        const ptr_vector<app> *aux = nullptr;
        expr_ref sum(m);
        // XXX This is a bit confusing. The summary is returned over
        // XXX o-variables. But it is simpler if it is returned over n-variables instead.
        sum = pt.get_origin_summary (mev, prev_level (n.level ()),
                                     j, reach_pred_used [j], &aux);
        deriv->add_premise (pt, j, sum, reach_pred_used [j], aux);
    }

    // create post for the first child and add to queue
    pob* kid = deriv->create_first_child (mev);

    // -- failed to create derivation, cleanup and bail out
    if (!kid) {
        dealloc(deriv);
        return false;
    }
    SASSERT (kid);
    kid->set_derivation (deriv);

    // Optionally disable derivation optimization
    if (!get_params().spacer_use_derivations()) { kid->reset_derivation(); }

    // -- deriviation is abstract if the current weak model does
    // -- not satisfy 'T && phi'. It is possible to recover from
    // -- that more gracefully. For now, we just remove the
    // -- derivation completely forcing it to be recomputed
    if (m_weak_abs && (!mev.is_true(T) || !mev.is_true(phi)))
    { kid->reset_derivation(); }

    m_pob_queue.push (*kid);
    m_stats.m_num_queries++;
    return true;
}




void context::collect_statistics(statistics& st) const
{
    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (it = m_rels.begin(); it != end; ++it) {
        it->m_value->collect_statistics(st);
    }
    st.update("SPACER num queries", m_stats.m_num_queries);
    st.update("SPACER num reach queries", m_stats.m_num_reach_queries);
    st.update("SPACER num reuse reach facts", m_stats.m_num_reuse_reach);
    st.update("SPACER max query lvl", m_stats.m_max_query_lvl);
    st.update("SPACER max depth", m_stats.m_max_depth);
    st.update("SPACER inductive level", m_inductive_lvl);
    st.update("SPACER cex depth", m_stats.m_cex_depth);
    st.update("SPACER expand node undef", m_stats.m_expand_node_undef);
    st.update("SPACER num lemmas", m_stats.m_num_lemmas);
    st.update("SPACER restarts", m_stats.m_num_restarts);

    st.update ("time.spacer.init_rules", m_init_rules_watch.get_seconds ());
    st.update ("time.spacer.solve", m_solve_watch.get_seconds ());
    st.update ("time.spacer.solve.propagate", m_propagate_watch.get_seconds ());
    st.update ("time.spacer.solve.reach", m_reach_watch.get_seconds ());
    st.update ("time.spacer.solve.reach.is-reach", m_is_reach_watch.get_seconds ());
    st.update ("time.spacer.solve.reach.children",
               m_create_children_watch.get_seconds ());
    m_pm.collect_statistics(st);

    for (unsigned i = 0; i < m_lemma_generalizers.size(); ++i) {
        m_lemma_generalizers[i]->collect_statistics(st);
    }

    // brunch out
    verbose_stream () << "BRUNCH_STAT max_query_lvl " << m_stats.m_max_query_lvl << "\n";
    verbose_stream () << "BRUNCH_STAT num_queries " << m_stats.m_num_queries << "\n";
    verbose_stream () << "BRUNCH_STAT num_reach_queries " << m_stats.m_num_reach_queries << "\n";
    verbose_stream () << "BRUNCH_STAT num_reach_reuse " << m_stats.m_num_reuse_reach << "\n";
    verbose_stream () << "BRUNCH_STAT inductive_lvl " << m_inductive_lvl << "\n";
    verbose_stream () << "BRUNCH_STAT max_depth " << m_stats.m_max_depth << "\n";
    verbose_stream () << "BRUNCH_STAT cex_depth " << m_stats.m_cex_depth << "\n";
}

void context::reset_statistics()
{
    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (it = m_rels.begin(); it != end; ++it) {
        it->m_value->reset_statistics();
    }
    m_stats.reset();
    m_pm.reset_statistics();

    for (unsigned i = 0; i < m_lemma_generalizers.size(); ++i) {
        m_lemma_generalizers[i]->reset_statistics();
    }

    m_init_rules_watch.reset ();
    m_solve_watch.reset ();
    m_propagate_watch.reset ();
    m_reach_watch.reset ();
    m_is_reach_watch.reset ();
    m_create_children_watch.reset ();
}

bool context::check_invariant(unsigned lvl)
{
    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (; it != end; ++it) {
        checkpoint();
        if (!check_invariant(lvl, it->m_key)) {
            return false;
        }
    }
    return true;
}

bool context::check_invariant(unsigned lvl, func_decl* fn)
{
    smt::kernel ctx(m, m_pm.fparams2());
    pred_transformer& pt = *m_rels.find(fn);
    expr_ref_vector conj(m);
    expr_ref inv = pt.get_formulas(next_level(lvl), false);
    if (m.is_true(inv)) { return true; }
    pt.add_premises(m_rels, lvl, conj);
    conj.push_back(m.mk_not(inv));
    expr_ref fml(m.mk_and(conj.size(), conj.c_ptr()), m);
    ctx.assert_expr(fml);
    lbool result = ctx.check();
    TRACE("spacer", tout << "Check invariant level: " << lvl << " " << result << "\n" << mk_pp(fml, m) << "\n";);
    return result == l_false;
}

expr_ref context::get_constraints (unsigned level)
{
    expr_ref res(m);
    expr_ref_vector constraints(m);

    decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
    for (; it != end; ++it) {
        pred_transformer& r = *it->m_value;
        expr_ref c = r.get_formulas(level, false);

        if (m.is_true(c)) { continue; }

        // replace local constants by bound variables.
        expr_ref_vector args(m);
        for (unsigned i = 0; i < r.sig_size(); ++i)
        { args.push_back(m.mk_const(m_pm.o2n(r.sig(i), 0))); }

        expr_ref pred(m);
        pred = m.mk_app(r.head (), r.sig_size(), args.c_ptr());

        constraints.push_back(m.mk_implies(pred, c));
    }

    if (constraints.empty()) { return expr_ref(m.mk_true(), m); }
    return m_pm.mk_and (constraints);
}

void context::add_constraints (unsigned level, const expr_ref& c)
{
    if (!c.get()) { return; }
    if (m.is_true(c)) { return; }

    expr_ref_vector constraints (m);
    constraints.push_back (c);
    flatten_and (constraints);

    for (unsigned i = 0, sz = constraints.size(); i < sz; ++i) {
        expr *c = constraints.get (i);
        expr *e1, *e2;
        if (m.is_implies(c, e1, e2)) {
            SASSERT (is_app (e1));
            pred_transformer *r = nullptr;
            if (m_rels.find (to_app (e1)->get_decl (), r))
            { r->add_lemma(e2, level); }
        }
    }
}

inline bool pob_lt::operator() (const pob *pn1, const pob *pn2) const
{
    SASSERT (pn1);
    SASSERT (pn2);
    const pob& n1 = *pn1;
    const pob& n2 = *pn2;

    if (n1.level() != n2.level()) { return n1.level() < n2.level(); }

    if (n1.depth() != n2.depth()) { return n1.depth() < n2.depth(); }

    // -- a more deterministic order of proof obligations in a queue
    // if (!n1.get_context ().get_params ().spacer_nondet_tie_break ())
    {
        const expr* p1 = n1.post ();
        const expr* p2 = n2.post ();
        ast_manager &m = n1.get_ast_manager ();


        // -- order by size. Less conjunctions is a proxy for
        // -- generality.  Currently, this takes precedence over
        // -- predicates which might not be the best choice
        unsigned sz1 = 1;
        unsigned sz2 = 1;

        if (m.is_and(p1)) { sz1 = to_app(p1)->get_num_args(); }
        if (m.is_and(p2)) { sz2 = to_app(p2)->get_num_args(); }
        if (sz1 != sz2) { return sz1 < sz2; }

        // -- when all else fails, order by identifiers of the
        // -- expressions.  This roughly means that expressions created
        // -- earlier are preferred.  Note that variables in post are
        // -- based on names of the predicates. Hence this guarantees an
        // -- order over predicates as well. That is, two expressions
        // -- are equal if and only if they correspond to the same proof
        // -- obligation of the same predicate.
        if (p1->get_id() != p2->get_id()) { return p1->get_id() < p2->get_id(); }

        if (n1.pt().head()->get_id() == n2.pt().head()->get_id()) {
            IF_VERBOSE (1,
                        verbose_stream ()
                        << "dup: " << n1.pt ().head ()->get_name ()
                        << "(" << n1.level () << ", " << n1.depth () << ") "
                        << p1->get_id () << "\n";
                        //<< " p1: " << mk_pp (const_cast<expr*>(p1), m) << "\n"
                );
        }

        // XXX see comment below on identical nodes
        // SASSERT (n1.pt ().head ()->get_id () != n2.pt ().head ()->get_id ());
        // -- if expression comparison fails, compare by predicate id
        if (n1.pt().head ()->get_id () != n2.pt ().head ()->get_id ())
        { return n1.pt().head()->get_id() < n2.pt().head()->get_id(); }

        /** XXX Identical nodes. This should not happen. However,
         * currently, when propagating reachability, we might call
         * expand_node() twice on the same node, causing it to generate
         * the same proof obligation multiple times */
        return &n1 < &n2;
    }
    // else
    //   return &n1 < &n2;
}



}
