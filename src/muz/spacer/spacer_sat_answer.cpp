#include "muz/spacer/spacer_sat_answer.h"
#include "muz/base/dl_context.h"
#include "muz/base/dl_rule.h"
#include "ast/scoped_proof.h"
#include "smt/smt_solver.h"

namespace spacer {

struct ground_sat_answer_op::frame {
    reach_fact *m_rf;
    pred_transformer &m_pt;
    expr_ref_vector m_gnd_subst;
    expr_ref m_gnd_eq;
    expr_ref m_fact;
    unsigned m_visit;
    expr_ref_vector m_kids;

    frame(reach_fact *rf, pred_transformer &pt,
          const expr_ref_vector &gnd_subst)
        : m_rf(rf), m_pt(pt), m_gnd_subst(gnd_subst),
          m_gnd_eq(pt.get_ast_manager()), m_fact(pt.get_ast_manager()),
          m_visit(0), m_kids(pt.get_ast_manager()) {

        ast_manager &m = pt.get_ast_manager();
        spacer::manager &pm = pt.get_manager();

        m_fact = m.mk_app(head(), m_gnd_subst.size(), m_gnd_subst.data());

        // compute ground equalities implied by the fact
        SASSERT(m_gnd_subst.size() == pt.head()->get_arity());
        expr_ref_vector eqs(m);
        for (unsigned i = 0, sz = pt.sig_size(); i < sz; ++i) {
            eqs.push_back(
                m.mk_eq(m.mk_const(pm.o2n(pt.sig(i), 0)), m_gnd_subst.get(i)));
        }
        m_gnd_eq = mk_and(eqs);
    }

    func_decl* head() {return m_pt.head();}
    expr* fact() {return m_fact;}
    const datalog::rule &rule() {return m_rf->get_rule();}
    pred_transformer &pt() {return m_pt;}
};

ground_sat_answer_op::ground_sat_answer_op(const context &ctx) :
    m_ctx(ctx), m(m_ctx.get_ast_manager()), m_pm(m_ctx.get_manager()),
    m_pinned(m) {
}

proof_ref ground_sat_answer_op::operator()(pred_transformer &query) {
    // -- turn on proof mode so that proof constructing API in ast_manager work correctly
    scoped_proof _pf(m);

    scoped_ptr<solver_factory> factory(mk_smt_strategic_solver_factory(symbol::null));
    m_solver = (*factory)(m, params_ref::get_empty(),
                          m.proofs_enabled() /*proofs*/, true /*models*/, false /*unsat_core*/, symbol::null /*logic*/);

    // m_solver = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
    vector<frame> todo, new_todo;

    // -- find substitution for a query if query is not nullary
    expr_ref_vector qsubst(m);
    if (query.head()->get_arity() > 0) {
        solver::scoped_push _s_(*m_solver);
        m_solver->assert_expr(query.get_last_rf()->get());
        lbool res = m_solver->check_sat(0, nullptr);
        CTRACE("spacer_sat", res != l_true, tout << "solver at check:\n";
               m_solver->display(tout) << "res: " << res << "\n";);
        if (res != l_true) throw default_exception("spacer: could not validate first proof step");
        model_ref mdl;
        m_solver->get_model(mdl);
        mdl->compress();
        model::scoped_model_completion _scm(mdl, true);
        for (unsigned i = 0, sz = query.sig_size(); i < sz; ++i) {
            expr_ref arg(m), val(m);
            arg = m.mk_const(m_pm.o2n(query.sig(i), 0));
            val = (*mdl)(arg);
            qsubst.push_back(val);
        }
    }

    todo.push_back(frame(query.get_last_rf(), query, qsubst));
    expr_ref root_fact(m);
    root_fact = todo.back().fact();

    while (!todo.empty()) {
        frame &curr = todo.back();
        if (m_cache.contains(curr.fact())) {
            todo.pop_back();
            continue;
        }

        if (curr.m_visit == 0) {
            new_todo.reset();
            mk_children(curr, new_todo);
            curr.m_visit = 1;
            // curr becomes invalid
            todo.append(new_todo);
        }
        else {
            proof* pf = mk_proof_step(curr);
            m_pinned.push_back(curr.fact());
            m_cache.insert(curr.fact(), pf);
            todo.pop_back();
        }
    }
    m_solver.reset();

    // turn proof of root fact into a refutation
    proof_ref pf1(m_cache.find(root_fact), m);
    proof_ref pf2(m.mk_asserted(m.mk_implies(m.get_fact(pf1), m.mk_false())), m);
    pf1 = m.mk_modus_ponens(pf1, pf2);
    return pf1;
}


void ground_sat_answer_op::mk_children(frame &fr, vector<frame> &todo) {
    const datalog::rule &r = fr.rule();
    ptr_vector<func_decl> preds;
    fr.pt().find_predecessors(r, preds);

    if (preds.empty()) return;

    const reach_fact_ref_vector &kid_rfs = fr.m_rf->get_justifications();
    solver::scoped_push _s_(*m_solver);
    m_solver->assert_expr(fr.m_gnd_eq);
    unsigned ut_sz = r.get_uninterpreted_tail_size();
    for (unsigned i = 0; i < ut_sz; ++i) {
        expr_ref f(m);
        m_pm.formula_n2o(kid_rfs.get(i)->get(), f, i);
        m_solver->assert_expr(f);
    }
    m_solver->assert_expr(fr.pt().transition());
    m_solver->assert_expr(fr.pt().rule2tag(&r));

    TRACE("spacer_sat",
          tout << "Solver in mk_children\n";
          m_solver->display(tout) << "\n";);

    lbool res = m_solver->check_sat(0, nullptr);
    CTRACE("spacer_sat", res != l_true,
           m_solver->display(tout) << "\n" "Result: " << res << "\n";);
    if(res != l_true)
        throw default_exception("spacer: could not validate a proof step");

    model_ref mdl;
    m_solver->get_model(mdl);
    mdl->compress();
    expr_ref_vector subst(m);
    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
        subst.reset();
        mk_child_subst_from_model(preds.get(i), i, mdl, subst);
        todo.push_back(frame(kid_rfs.get(i),
                             m_ctx.get_pred_transformer(preds.get(i)), subst));
        fr.m_kids.push_back(todo.back().fact());
    }
    TRACE("spacer_sat", tout << "Children for fact: " << fr.m_fact << " are " << fr.m_kids << "\n";
          tout << "gnd_eq for fact are: " << fr.m_gnd_eq << "\n";
          );
}


void ground_sat_answer_op::mk_child_subst_from_model(func_decl *pred,
                                                      unsigned j, model_ref &mdl,
                                                      expr_ref_vector &subst) {
    
    model::scoped_model_completion _scm(mdl, true);
    pred_transformer &pt = m_ctx.get_pred_transformer(pred);
    for (unsigned i = 0, sz = pt.sig_size(); i < sz; ++i) {
        expr_ref arg(m), val(m);
        arg = m.mk_const(m_pm.o2o(pt.sig(i), 0, j));
        val = (*mdl)(arg);
        subst.push_back(val);
    }
}

proof *ground_sat_answer_op::mk_proof_step(frame &fr) {
    svector<std::pair<unsigned, unsigned>> positions;
    vector<expr_ref_vector> substs;

    proof_ref_vector premises(m);
    datalog::rule_manager &rm = m_ctx.get_datalog_context().get_rule_manager();
    expr_ref rule_fml(m);
    rm.to_formula(fr.rule(), rule_fml);
    // premises.push_back(fr.rule().get_proof());
    premises.push_back(m.mk_asserted(rule_fml));
    for (auto &k : fr.m_kids) {premises.push_back(m_cache.find(k));}

    for (unsigned i = 0; i < premises.size(); i++) {
        positions.push_back(std::make_pair(0,i));
    }
    for (unsigned i = 0; i <= premises.size(); i++) {
        substs.push_back(expr_ref_vector(m));
    }
    m_pinned.push_back(m.mk_hyper_resolve(premises.size(),
                                          premises.data(),
                                          fr.fact(),
                                          positions, substs));
    TRACE("spacer_sat", tout << "pf step:\n"
          << "premises: " << premises << "\n"
          << "fact: " << mk_pp(fr.fact(), m) << "\n";);
    return to_app(m_pinned.back());
}

}
