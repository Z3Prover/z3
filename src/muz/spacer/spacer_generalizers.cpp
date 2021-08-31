/*++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_generalizers.cpp

Abstract:

    Lemma generalizers.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-20.
    Arie Gurfinkel

Revision History:

--*/


#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "ast/ast_util.h"
#include "ast/expr_abstract.h"
#include "ast/rewriter/var_subst.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/factor_equivs.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/substitution/matcher.h"
#include "ast/expr_functors.h"
#include "smt/smt_solver.h"
#include "qe/mbp/mbp_term_graph.h"

namespace spacer {
void lemma_sanity_checker::operator()(lemma_ref &lemma) {
    unsigned uses_level;
    expr_ref_vector cube(lemma->get_ast_manager());
    cube.append(lemma->get_cube());
    ENSURE(lemma->get_pob()->pt().check_inductive(lemma->level(),
                                                  cube, uses_level,
                                                  lemma->weakness()));
}

namespace{
    class contains_array_op_proc : public i_expr_pred {
        ast_manager &m;
        family_id m_array_fid;
    public:
        contains_array_op_proc(ast_manager &manager) :
            m(manager), m_array_fid(m.mk_family_id("array"))
            {}
        bool operator()(expr *e) override {
            return is_app(e) && to_app(e)->get_family_id() == m_array_fid;
        }
    };
}

// ------------------------
// lemma_bool_inductive_generalizer
/// Inductive generalization by dropping and expanding literals
void lemma_bool_inductive_generalizer::operator()(lemma_ref &lemma) {
    if (lemma->get_cube().empty()) return;

    m_st.count++;
    scoped_watch _w_(m_st.watch);

    unsigned uses_level;
    pred_transformer &pt = lemma->get_pob()->pt();
    ast_manager &m = pt.get_ast_manager();

    contains_array_op_proc has_array_op(m);
    check_pred has_arrays(has_array_op, m);

    expr_ref_vector cube(m);
    cube.append(lemma->get_cube());

    bool dirty = false;
    expr_ref true_expr(m.mk_true(), m);
    ptr_vector<expr> processed;
    expr_ref_vector extra_lits(m);

    unsigned weakness = lemma->weakness();

    unsigned i = 0, num_failures = 0;
    while (i < cube.size() &&
           (!m_failure_limit || num_failures < m_failure_limit)) {
        expr_ref lit(m);
        lit = cube.get(i);
        if (m_array_only && !has_arrays(lit)) {
            processed.push_back(lit);
            ++i;
            continue;
        }
        cube[i] = true_expr;
        if (cube.size() > 1 &&
            pt.check_inductive(lemma->level(), cube, uses_level, weakness)) {
            num_failures = 0;
            dirty = true;
            for (i = 0; i < cube.size() &&
                     processed.contains(cube.get(i)); ++i);
        } else {
            // check if the literal can be expanded and any single
            // literal in the expansion can replace it
            extra_lits.reset();
            extra_lits.push_back(lit);
            expand_literals(m, extra_lits);
            SASSERT(extra_lits.size() > 0);
            bool found = false;
            if (extra_lits.get(0) != lit && extra_lits.size() > 1) {
                for (unsigned j = 0, sz = extra_lits.size(); !found && j < sz; ++j) {
                    cube[i] = extra_lits.get(j);
                    if (pt.check_inductive(lemma->level(), cube, uses_level, weakness)) {
                        num_failures = 0;
                        dirty = true;
                        found = true;
                        processed.push_back(extra_lits.get(j));
                        for (i = 0; i < cube.size() &&
                                 processed.contains(cube.get(i)); ++i);
                    }
                }
            }
            if (!found) {
                cube[i] = lit;
                processed.push_back(lit);
                ++num_failures;
                ++m_st.num_failures;
                ++i;
            }
        }
    }

    if (dirty) {
        TRACE("spacer",
               tout << "Generalized from:\n" << mk_and(lemma->get_cube())
               << "\ninto\n" << mk_and(cube) << "\n";);

        lemma->update_cube(lemma->get_pob(), cube);
        SASSERT(uses_level >= lemma->level());
        lemma->set_level(uses_level);
    }
}

void lemma_bool_inductive_generalizer::collect_statistics(statistics &st) const
{
    st.update("time.spacer.solve.reach.gen.bool_ind", m_st.watch.get_seconds());
    st.update("bool inductive gen", m_st.count);
    st.update("bool inductive gen failures", m_st.num_failures);
}

void unsat_core_generalizer::operator()(lemma_ref &lemma)
{
    m_st.count++;
    scoped_watch _w_(m_st.watch);
    ast_manager &m = lemma->get_ast_manager();

    pred_transformer &pt = lemma->get_pob()->pt();

    unsigned old_sz = lemma->get_cube().size();
    unsigned old_level = lemma->level();
    (void)old_level;

    unsigned uses_level;
    expr_ref_vector core(m);
    VERIFY(pt.is_invariant(lemma->level(), lemma.get(), uses_level, &core));

    CTRACE("spacer", old_sz > core.size(),
           tout << "unsat core reduced lemma from: "
           << old_sz << " to " << core.size() << "\n";);
    CTRACE("spacer", old_level < uses_level,
           tout << "unsat core moved lemma up from: "
           << old_level << " to " << uses_level << "\n";);
    if (old_sz > core.size()) {
        lemma->update_cube(lemma->get_pob(), core);
        lemma->set_level(uses_level);
    }
}

void unsat_core_generalizer::collect_statistics(statistics &st) const
{
    st.update("time.spacer.solve.reach.gen.unsat_core", m_st.watch.get_seconds());
    st.update("gen.unsat_core.cnt", m_st.count);
    st.update("gen.unsat_core.fail", m_st.num_failures);
}

namespace {
class collect_array_proc {
    array_util m_au;
    func_decl_set &m_symbs;
    sort *m_sort;
public:
    collect_array_proc(ast_manager &m, func_decl_set& s) :
        m_au(m), m_symbs(s), m_sort(nullptr) {}

    void operator()(app* a)
    {
        if (a->get_family_id() == null_family_id && m_au.is_array(a)) {
            if (m_sort && m_sort != a->get_sort()) { return; }
            if (!m_sort) { m_sort = a->get_sort(); }
            m_symbs.insert(a->get_decl());
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};
}

bool lemma_array_eq_generalizer::is_array_eq (ast_manager &m, expr* e) {

    expr *e1 = nullptr, *e2 = nullptr;
    if (m.is_eq(e, e1, e2) && is_app(e1) && is_app(e2)) {
        app *a1 = to_app(e1);
        app *a2 = to_app(e2);
        array_util au(m);
        if (a1->get_family_id() == null_family_id &&
            a2->get_family_id() == null_family_id &&
            au.is_array(a1) && au.is_array(a2))
            return true;
    }
    return false;
}

void lemma_array_eq_generalizer::operator() (lemma_ref &lemma)
{

    ast_manager &m = lemma->get_ast_manager();


    expr_ref_vector core(m);
    expr_ref v(m);
    func_decl_set symb;
    collect_array_proc cap(m, symb);


    // -- find array constants
    core.append (lemma->get_cube());
    v = mk_and(core);
    for_each_expr(cap, v);

    CTRACE("core_array_eq", symb.size() > 1 && symb.size() <= 8,
          tout << "found " << symb.size() << " array variables in: \n"
          << v << "\n";);

    // too few constants or too many constants
    if (symb.size() <= 1 || symb.size() > 8) { return; }


    // -- for every pair of constants (A, B), check whether the
    // -- equality (A=B) generalizes a literal in the lemma

    ptr_vector<func_decl> vsymbs;
    for (auto * fdecl : symb) {vsymbs.push_back(fdecl);}

    // create all equalities
    expr_ref_vector eqs(m);
    for (unsigned i = 0, sz = vsymbs.size(); i < sz; ++i) {
        for (unsigned j = i + 1; j < sz; ++j) {
            eqs.push_back(m.mk_eq(m.mk_const(vsymbs.get(i)),
                                  m.mk_const(vsymbs.get(j))));
        }
    }

    // smt-solver to check whether a literal is generalized.  using
    // default params. There has to be a simpler way to approximate
    // this check
    ref<solver> sol = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
    // literals of the new lemma
    expr_ref_vector lits(m);
    lits.append(core);
    expr *t = nullptr;
    bool dirty = false;
    for (unsigned i = 0, sz = core.size(); i < sz; ++i) {
        // skip a literal is it is already an array equality
        if (m.is_not(lits.get(i), t) && is_array_eq(m, t)) continue;
        solver::scoped_push _pp_(*sol);
        sol->assert_expr(lits.get(i));
        for (auto *e : eqs) {
            solver::scoped_push _p_(*sol);
            sol->assert_expr(e);
            lbool res = sol->check_sat(0, nullptr);

            if (res == l_false) {
                TRACE("core_array_eq",
                      tout << "strengthened " << mk_pp(lits.get(i), m)
                      << " with " << mk_pp(mk_not(m, e), m) << "\n";);
                lits[i] = mk_not(m, e);
                dirty = true;
                break;
            }
        }
    }

    // nothing changed
    if (!dirty) return;

    TRACE("core_array_eq",
           tout << "new possible core " << mk_and(lits) << "\n";);


    pred_transformer &pt = lemma->get_pob()->pt();
    // -- check if the generalized result is consistent with trans
    unsigned uses_level1;
    if (pt.check_inductive(lemma->level(), lits, uses_level1, lemma->weakness())) {
        TRACE("core_array_eq", tout << "Inductive!\n";);
        lemma->update_cube(lemma->get_pob(), lits);
        lemma->set_level(uses_level1);
    }
    else
    {TRACE("core_array_eq", tout << "Not-Inductive!\n";);}
}

void lemma_eq_generalizer::operator() (lemma_ref &lemma) {
    TRACE("core_eq", tout << "Transforming equivalence classes\n";);

    if (lemma->get_cube().empty()) return;

    ast_manager &m = m_ctx.get_ast_manager();
    mbp::term_graph egraph(m);
    egraph.add_lits(lemma->get_cube());

    // -- expand the cube with all derived equalities
    expr_ref_vector core(m);
    egraph.to_lits(core, true);

    // -- if the core looks different from the original cube
    if (core.size() != lemma->get_cube().size() ||
        core.get(0) != lemma->get_cube().get(0)) {
        // -- update the lemma
        lemma->update_cube(lemma->get_pob(), core);
    }
}


};
