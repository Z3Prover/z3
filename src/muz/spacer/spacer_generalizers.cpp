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
#include "ast/expr_abstract.h"
#include "ast/rewriter/var_subst.h"
#include "ast/for_each_expr.h"
#include "ast/factor_equivs.h"


namespace spacer {
void lemma_sanity_checker::operator()(lemma_ref &lemma) {
    unsigned uses_level;
    expr_ref_vector cube(lemma->get_ast_manager());
    cube.append(lemma->get_cube());
    ENSURE(lemma->get_pob()->pt().check_inductive(lemma->level(),
                                                  cube, uses_level));
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

    expr_ref_vector cube(m);
    cube.append(lemma->get_cube());

    bool dirty = false;
    expr_ref true_expr(m.mk_true(), m);
    ptr_vector<expr> processed;
    expr_ref_vector extra_lits(m);

    unsigned i = 0, num_failures = 0;
    while (i < cube.size() &&
           (!m_failure_limit || num_failures < m_failure_limit)) {
        expr_ref lit(m);
        lit = cube.get(i);
        cube[i] = true_expr;
        if (cube.size() > 1 &&
            pt.check_inductive(lemma->level(), cube, uses_level)) {
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
            if (extra_lits.get(0) != lit) {
                SASSERT(extra_lits.size() > 1);
                for (unsigned j = 0, sz = extra_lits.size(); !found && j < sz; ++j) {
                    cube[i] = extra_lits.get(j);
                    if (pt.check_inductive(lemma->level(), cube, uses_level)) {
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

    unsigned uses_level;
    expr_ref_vector core(m);
    VERIFY(pt.is_invariant(old_level, lemma->get_expr(), uses_level, &core));

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
            if (m_sort && m_sort != get_sort(a)) { return; }
            if (!m_sort) { m_sort = get_sort(a); }
            m_symbs.insert(a->get_decl());
        }
    }
    void operator()(var*) {}
    void operator()(quantifier*) {}
};
}

void lemma_array_eq_generalizer::operator() (lemma_ref &lemma)
{
    TRACE("core_array_eq", tout << "Looking for equalities\n";);

    // -- find array constants
    ast_manager &m = lemma->get_ast_manager();
    manager &pm = m_ctx.get_manager();
    (void)pm;

    expr_ref_vector core(m);
    expr_ref v(m);
    func_decl_set symb;
    collect_array_proc cap(m, symb);

    core.append (lemma->get_cube());
    v = mk_and(core);
    for_each_expr(cap, v);

    TRACE("core_array_eq",
          tout << "found " << symb.size() << " array variables in: \n"
          << mk_pp(v, m) << "\n";);

    // too few constants
    if (symb.size() <= 1) { return; }
    // too many constants, skip this
    if (symb.size() >= 8) { return; }


    // -- for every pair of variables, try an equality
    typedef func_decl_set::iterator iterator;
    ptr_vector<func_decl> vsymbs;
    for (iterator it = symb.begin(), end = symb.end();
            it != end; ++it)
    { vsymbs.push_back(*it); }

    expr_ref_vector eqs(m);

    for (unsigned i = 0, sz = vsymbs.size(); i < sz; ++i)
        for (unsigned j = i + 1; j < sz; ++j)
        { eqs.push_back(m.mk_eq(m.mk_const(vsymbs.get(i)),
                                m.mk_const(vsymbs.get(j)))); }

    smt::kernel solver(m, m_ctx.get_manager().fparams2());
    expr_ref_vector lits(m);
    for (unsigned i = 0, core_sz = core.size(); i < core_sz; ++i) {
        SASSERT(lits.size() == i);
        solver.push();
        solver.assert_expr(core.get(i));
        for (unsigned j = 0, eqs_sz = eqs.size(); j < eqs_sz; ++j) {
            solver.push();
            solver.assert_expr(eqs.get(j));
            lbool res = solver.check();
            solver.pop(1);

            if (res == l_false) {
                TRACE("core_array_eq",
                      tout << "strengthened " << mk_pp(core.get(i), m)
                      << " with " << mk_pp(m.mk_not(eqs.get(j)), m) << "\n";);
                lits.push_back(m.mk_not(eqs.get(j)));
                break;
            }
        }
        solver.pop(1);
        if (lits.size() == i) { lits.push_back(core.get(i)); }
    }

    /**
       HACK: if the first 3 arguments of pt are boolean, assume
       they correspond to SeaHorn encoding and condition the equality on them.
    */
    // pred_transformer &pt = n.pt ();
    // if (pt.sig_size () >= 3 &&
    //     m.is_bool (pt.sig (0)->get_range ()) &&
    //     m.is_bool (pt.sig (1)->get_range ()) &&
    //     m.is_bool (pt.sig (2)->get_range ()))
    // {
    //   lits.push_back (m.mk_const (pm.o2n(pt.sig (0), 0)));
    //   lits.push_back (m.mk_not (m.mk_const (pm.o2n(pt.sig (1), 0))));
    //   lits.push_back (m.mk_not (m.mk_const (pm.o2n(pt.sig (2), 0))));
    // }

    TRACE("core_array_eq", tout << "new possible core "
          << mk_pp(pm.mk_and(lits), m) << "\n";);


    pred_transformer &pt = lemma->get_pob()->pt();
    // -- check if it is consistent with the transition relation
    unsigned uses_level1;
    if (pt.check_inductive(lemma->level(), lits, uses_level1)) {
        TRACE("core_array_eq", tout << "Inductive!\n";);
        lemma->update_cube(lemma->get_pob(),lits);
        lemma->set_level(uses_level1);
        return;
    } else
    { TRACE("core_array_eq", tout << "Not-Inductive!\n";);}
}

void lemma_eq_generalizer::operator() (lemma_ref &lemma)
{
    TRACE("core_eq", tout << "Transforming equivalence classes\n";);

    ast_manager &m = m_ctx.get_ast_manager();
    expr_ref_vector core(m);
    core.append (lemma->get_cube());

    bool dirty;
    expr_equiv_class eq_classes(m);
    factor_eqs(core, eq_classes);
    // create all possible equalities to allow for simple inductive generalization
    dirty = equiv_to_expr_full(eq_classes, core);
    if (dirty) {
        lemma->update_cube(lemma->get_pob(), core);
    }
}
};
