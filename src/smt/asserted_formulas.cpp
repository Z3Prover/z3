/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    asserted_formulas.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-11.

Revision History:

--*/
#include"asserted_formulas.h"
#include"ast_ll_pp.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"
#include"arith_simplifier_plugin.h"
#include"array_simplifier_plugin.h"
#include"datatype_simplifier_plugin.h"
#include"bv_simplifier_plugin.h"
#include"arith_solver_plugin.h"
#include"occurs.h"
#include"for_each_expr.h"
#include"well_sorted.h"
#include"pull_ite_tree.h"
#include"push_app_ite.h"
#include"elim_term_ite.h"
#include"pattern_inference.h"
#include"nnf.h"
#include"cnf.h"
#include"expr_context_simplifier.h"
#include"bv_elim.h"
#include"inj_axiom.h"
#include"der.h"
#include"elim_bounds.h"
#include"warning.h"
#include"eager_bit_blaster.h"
#include"bit2int.h"
#include"distribute_forall.h"
#include"quasi_macros.h"

asserted_formulas::asserted_formulas(ast_manager & m, front_end_params & p):
    m_manager(m),
    m_params(p),
    m_pre_simplifier(m),
    m_simplifier(m),
    m_defined_names(m),
    m_static_features(m),
    m_asserted_formulas(m),
    m_asserted_formula_prs(m),
    m_asserted_qhead(0),
    m_subst(m),
    m_vars_qhead(0),
    m_macro_manager(m, m_simplifier),
    m_bit2int(m),
    m_bv_sharing(m),
    m_inconsistent(false),
    m_cancel_flag(false) {

    m_bsimp = 0;
    m_bvsimp = 0;
    arith_simplifier_plugin * arith_simp = 0;
    setup_simplifier_plugins(m_simplifier, m_bsimp, arith_simp, m_bvsimp);
    SASSERT(m_bsimp != 0);
    SASSERT(arith_simp != 0);
    m_simplifier.set_subst_map(&m_subst);
    m_macro_finder = alloc(macro_finder, m_manager, m_macro_manager);

    basic_simplifier_plugin * basic_simp = 0;
    bv_simplifier_plugin * bv_simp = 0;
    setup_simplifier_plugins(m_pre_simplifier, basic_simp, arith_simp, bv_simp);
    m_bit2int.set_bv_simplifier(bv_simp);
    m_pre_simplifier.enable_presimp();
}

void asserted_formulas::setup() {
    switch (m_params.m_lift_ite) {
    case LI_FULL:
        m_params.m_ng_lift_ite = LI_NONE; 
        break;
    case LI_CONSERVATIVE:
        if (m_params.m_ng_lift_ite == LI_CONSERVATIVE)
            m_params.m_ng_lift_ite = LI_NONE;
        break;
    default:
        break;
    }
 
    if (m_params.m_relevancy_lvl == 0)
        m_params.m_relevancy_lemma = false;
   
    switch (m_params.m_cnf_mode) {
    case CNF_QUANT: 
        if (m_params.m_nnf_mode == NNF_SKOLEM)
            m_params.m_nnf_mode = NNF_QUANT;
        break;
    case CNF_OPPORTUNISTIC:
        if (m_params.m_nnf_mode == NNF_SKOLEM)
            m_params.m_nnf_mode = NNF_QUANT;
        break;
    case CNF_FULL:
        m_params.m_nnf_mode = NNF_FULL;
        break;
    default:
        break;
    }
}

void asserted_formulas::setup_simplifier_plugins(simplifier & s, basic_simplifier_plugin * & bsimp, arith_simplifier_plugin * & asimp, bv_simplifier_plugin * & bvsimp) {
    bsimp = alloc(basic_simplifier_plugin, m_manager);
    s.register_plugin(bsimp);
    asimp = alloc(arith_simplifier_plugin, m_manager, *bsimp, m_params);
    s.register_plugin(asimp);
    s.register_plugin(alloc(array_simplifier_plugin, m_manager, *bsimp, s, m_params));
    bvsimp = alloc(bv_simplifier_plugin, m_manager, *bsimp, m_params);
    s.register_plugin(bvsimp);
    s.register_plugin(alloc(datatype_simplifier_plugin, m_manager, *bsimp));
}

void asserted_formulas::init(unsigned num_formulas, expr * const * formulas, proof * const * prs) {
    SASSERT(m_asserted_formulas.empty());
    SASSERT(m_asserted_formula_prs.empty());
    SASSERT(!m_inconsistent);
    SASSERT(m_scopes.empty());
    m_asserted_formulas.append(num_formulas, formulas);
    if (m_manager.proofs_enabled())
        m_asserted_formula_prs.append(num_formulas, prs);
}

bool asserted_formulas::has_bv() const {
    // approaximated answer... assume the formula has bit-vectors if the bv_simplifier_plugin was invoked at least once.
    return m_bvsimp->reduce_invoked();
}

asserted_formulas::~asserted_formulas() {
}

void asserted_formulas::push_assertion(expr * e, proof * pr, expr_ref_vector & result, proof_ref_vector & result_prs) {
    if (inconsistent()) {
        SASSERT(!result.empty());
        return;
    }
    if (m_manager.is_false(e))
        m_inconsistent = true;
    ::push_assertion(m_manager, e, pr, result, result_prs);
}

void asserted_formulas::set_eliminate_and(bool flag) {
    if (m_bsimp->eliminate_and() == flag)
        return;
    TRACE("eliminate_and", tout << "flushing cache...\n";);
    flush_cache();
    m_bsimp->set_eliminate_and(flag);
}

void asserted_formulas::assert_expr(expr * e, proof * _in_pr) {
    if (inconsistent()) 
        return;
    if (!m_params.m_preprocess) {
        push_assertion(e, _in_pr, m_asserted_formulas, m_asserted_formula_prs);
        return;
    }
    proof_ref  in_pr(_in_pr, m_manager);
    expr_ref   r1(m_manager);
    proof_ref  pr1(m_manager);
    expr_ref   r2(m_manager);
    proof_ref  pr2(m_manager);
    TRACE("assert_expr_before_simp", tout << mk_ll_pp(e, m_manager) << "\n";);
    TRACE("assert_expr_bug", tout << mk_ismt2_pp(e, m_manager) << "\n";);
    if (m_params.m_pre_simplifier) {
        m_pre_simplifier(e, r1, pr1);
    }
    else {
        r1  = e;
        pr1 = 0;
    }
    set_eliminate_and(false); // do not eliminate and before nnf.
    m_simplifier(r1, r2, pr2);
    TRACE("assert_expr_bug", tout << "after...\n" << mk_ismt2_pp(r1, m_manager) << "\n";);
    if (m_manager.proofs_enabled()) {
        if (e == r2)
            pr2 = in_pr;
        else
            pr2 = m_manager.mk_modus_ponens(in_pr, m_manager.mk_transitivity(pr1, pr2));
    }
    TRACE("assert_expr_after_simp", tout << mk_ll_pp(r1, m_manager) << "\n";);
    push_assertion(r2, pr2, m_asserted_formulas, m_asserted_formula_prs);
    TRACE("asserted_formulas_bug", tout << "after assert_expr\n"; display(tout););
}

void asserted_formulas::assert_expr(expr * e) {
    if (inconsistent()) 
        return;
    assert_expr(e, m_manager.mk_asserted(e));
}

void asserted_formulas::get_assertions(ptr_vector<expr> & result) {
    result.append(m_asserted_formulas.size(), m_asserted_formulas.c_ptr());
}

void asserted_formulas::push_scope() {
    SASSERT(inconsistent() || m_asserted_qhead == m_asserted_formulas.size());
    TRACE("asserted_formulas_scopes", tout << "push:\n"; display(tout););
    m_scopes.push_back(scope());
    m_macro_manager.push_scope();
    scope & s = m_scopes.back();
    s.m_asserted_formulas_lim    = m_asserted_formulas.size();
    SASSERT(inconsistent() || s.m_asserted_formulas_lim == m_asserted_qhead);
    s.m_vars_lim                 = m_vars.size();
    s.m_forbidden_vars_lim       = m_forbidden_vars.size();
    s.m_inconsistent_old         = m_inconsistent;
    m_defined_names.push_scope();
    m_bv_sharing.push_scope();
    commit();
}
 
void asserted_formulas::pop_scope(unsigned num_scopes) {
    TRACE("asserted_formulas_scopes", tout << "before pop " << num_scopes << "\n"; display(tout););
    m_bv_sharing.pop_scope(num_scopes);
    m_macro_manager.pop_scope(num_scopes);
    unsigned new_lvl    = m_scopes.size() - num_scopes;
    scope & s           = m_scopes[new_lvl];
    m_inconsistent      = s.m_inconsistent_old;
    restore_subst(s.m_vars_lim);
    restore_forbidden_vars(s.m_forbidden_vars_lim);
    m_defined_names.pop_scope(num_scopes);
    m_asserted_formulas.shrink(s.m_asserted_formulas_lim);
    if (m_manager.proofs_enabled())
        m_asserted_formula_prs.shrink(s.m_asserted_formulas_lim);
    m_asserted_qhead    = s.m_asserted_formulas_lim;
    m_vars_qhead        = m_vars.size();
    m_scopes.shrink(new_lvl);
    flush_cache();
    TRACE("asserted_formulas_scopes", tout << "after pop " << num_scopes << "\n"; display(tout););
}

void asserted_formulas::restore_subst(unsigned old_size) {
    unsigned sz  = m_vars.size();
    SASSERT(sz >= old_size);
    TRACE("asserted_formulas_bug", tout << "restore_subst, old_size: " << old_size << ", curr_size: " << sz << "\n";);
    for (unsigned i = old_size; i < sz; i++) {
        SASSERT(is_app(m_vars[i]));
        TRACE("asserted_formulas_bug", tout << "removing subst: " << mk_pp(m_vars[i], m_manager) << "\n";);
        m_subst.erase(m_vars[i]);
        SASSERT(!m_subst.contains(m_vars[i]));
    }
    if (old_size != sz)
        flush_cache();
    m_vars.shrink(old_size);
}

void asserted_formulas::restore_forbidden_vars(unsigned old_size) {
    unsigned sz  = m_forbidden_vars.size();
    SASSERT(sz >= old_size);
    for (unsigned i = old_size; i < sz; i++) {
        TRACE("solver_bug", tout << "unmarking: " << m_forbidden_vars[i]->get_decl()->get_name() << "\n";);
        m_forbidden.mark(m_forbidden_vars[i], false);
    }
    m_forbidden_vars.shrink(old_size);
}

void asserted_formulas::reset() {
    m_defined_names.reset();
    m_asserted_qhead = 0;
    m_asserted_formulas.reset();
    m_asserted_formula_prs.reset();
    m_subst.reset();
    m_vars.reset();
    m_vars_qhead = 0;
    m_forbidden.reset();
    m_forbidden_vars.reset();
    m_macro_manager.reset();
    m_bv_sharing.reset();
    m_inconsistent = false;
}

void asserted_formulas::set_cancel_flag(bool f) {
    m_cancel_flag = f; 
}

#ifdef Z3DEBUG
bool asserted_formulas::check_well_sorted() const {
    for (unsigned i = 0; i < m_asserted_formulas.size(); i++) { 
        if (!is_well_sorted(m_manager, m_asserted_formulas.get(i))) return false; 
    }
    return true;
}
#endif

void asserted_formulas::reduce() {
    if (inconsistent()) 
        return;
    if (canceled()) {
        return;
    }
    if (m_asserted_qhead == m_asserted_formulas.size())
        return;
    if (!m_params.m_preprocess)
        return;

    if (m_macro_manager.has_macros())
        expand_macros();
    TRACE("before_reduce", display(tout););
    IF_VERBOSE(10000, verbose_stream() << "total size: " << get_total_size() << "\n";);
    CASSERT("well_sorted", check_well_sorted());

#define INVOKE(COND, FUNC) if (COND) { FUNC; IF_VERBOSE(10000, verbose_stream() << "total size: " << get_total_size() << "\n";); }  TRACE("reduce_step_ll", ast_mark visited; display_ll(tout, visited);); TRACE("reduce_step", display(tout << #FUNC << " ");); CASSERT("well_sorted",check_well_sorted()); if (inconsistent() || canceled()) { TRACE("after_reduce", display(tout);); TRACE("after_reduce_ll", ast_mark visited; display_ll(tout, visited);); return;  }
    
    set_eliminate_and(false); // do not eliminate and before nnf.
    INVOKE(m_params.m_propagate_booleans, propagate_booleans());
    INVOKE(m_params.m_propagate_values, propagate_values());
    INVOKE(m_params.m_macro_finder && has_quantifiers(), find_macros());
    INVOKE((m_params.m_quant_elim && has_quantifiers()), quant_elim());
    INVOKE(m_params.m_nnf_cnf, nnf_cnf());
    INVOKE(m_params.m_context_simplifier, context_simplifier());
    INVOKE(m_params.m_strong_context_simplifier, strong_context_simplifier());
    INVOKE(m_params.m_eliminate_and, eliminate_and());
    INVOKE(m_params.m_pull_cheap_ite_trees, pull_cheap_ite_trees());
    INVOKE(m_params.m_pull_nested_quantifiers && has_quantifiers(), pull_nested_quantifiers());
    INVOKE(m_params.m_ng_lift_ite != LI_NONE, ng_lift_ite());
    INVOKE(m_params.m_lift_ite != LI_NONE, lift_ite());
    INVOKE(m_params.m_solver, solve());
    INVOKE(m_params.m_eliminate_term_ite && m_params.m_lift_ite != LI_FULL, eliminate_term_ite());
    INVOKE(m_params.m_refine_inj_axiom && has_quantifiers(), refine_inj_axiom());
    TRACE("der_bug", tout << "before DER:\n"; display(tout););
    INVOKE(m_params.m_der && has_quantifiers(), apply_der());    
    TRACE("der_bug", tout << "after DER:\n"; display(tout););    
    INVOKE(m_params.m_distribute_forall && has_quantifiers(), apply_distribute_forall());    
    TRACE("qbv_bug", tout << "after distribute_forall:\n"; display(tout););    
    INVOKE(m_params.m_macro_finder && has_quantifiers(), find_macros());
    TRACE("qbv_bug", tout << "before demod:\n"; display(tout););    
    INVOKE(m_params.m_pre_demod && has_quantifiers(), apply_demodulators());
    TRACE("qbv_bug", tout << "after demod:\n"; display(tout););    
    INVOKE(m_params.m_quasi_macros && has_quantifiers(), apply_quasi_macros());    
    INVOKE(m_params.m_simplify_bit2int, apply_bit2int());
    INVOKE(m_params.m_eliminate_bounds && has_quantifiers(), cheap_quant_fourier_motzkin());
    INVOKE(!m_params.m_bb_eager && has_quantifiers() && m_params.m_ematching, infer_patterns());
    INVOKE(m_params.m_max_bv_sharing && has_bv(), max_bv_sharing());
    INVOKE(m_params.m_bb_quantifiers, elim_bvs_from_quantifiers());
    INVOKE(m_params.m_bb_eager, apply_eager_bit_blaster());                     
    INVOKE(m_params.m_bb_eager && m_params.m_nnf_cnf, nnf_cnf());   // bit-blaster destroys CNF
    INVOKE(m_params.m_bb_quantifiers && m_params.m_der && has_quantifiers(), apply_der()); // bit-vector elimination + bit-blasting creates new opportunities for der.
    INVOKE(m_params.m_bb_eager && has_quantifiers() && m_params.m_ematching, infer_patterns());
    // temporary HACK: make sure that arith & bv are list-assoc 
    // this may destroy some simplification steps such as max_bv_sharing
    reduce_asserted_formulas(); 

    CASSERT("well_sorted",check_well_sorted());

    IF_VERBOSE(10, verbose_stream() << "simplifier done.\n";);
    TRACE("after_reduce", display(tout););
    TRACE("after_reduce_ll", ast_mark visited; display_ll(tout, visited););
    TRACE("macros", m_macro_manager.display(tout););
    flush_cache();
}

void asserted_formulas::eliminate_and() {
    IF_IVERBOSE(10, verbose_stream() << "eliminating and...\n";);
    set_eliminate_and(true);
    reduce_asserted_formulas();    
    TRACE("after_elim_and", display(tout););
}

bool asserted_formulas::trivial_solve(expr * lhs, expr * rhs, app_ref & var, expr_ref & subst, proof_ref& pr) {
    if (is_uninterp_const(lhs) && !m_forbidden.is_marked(lhs)) {
        var   = to_app(lhs); 
        subst = rhs;
        if (m_manager.proofs_enabled()) {
            app* n = m_manager.mk_eq(lhs,rhs);
            pr = m_manager.mk_reflexivity(m_manager.mk_iff(n,n));
        }
        TRACE("solve_bug", 
              tout << "trivial solve " << 
              mk_pp(var, m_manager) << " |-> " <<
              mk_pp(subst, m_manager) << "\n";);                    
        return true;
    }
    else if (is_uninterp_const(rhs) && !m_forbidden.is_marked(rhs)) {
        var   = to_app(rhs);
        subst = lhs;
        if (m_manager.proofs_enabled()) {
            app* m = m_manager.mk_eq(lhs,rhs);
            pr = m_manager.mk_commutativity(m);
        }
        TRACE("solve_bug", 
              tout << "trivial solve " << 
              mk_pp(var, m_manager) << " |-> " <<
              mk_pp(subst, m_manager) << "\n";);
        return true;
    }
    return false;
}

bool asserted_formulas::is_pos_literal(expr * n) {
    return is_app(n) && to_app(n)->get_num_args() == 0 && to_app(n)->get_family_id() == null_family_id;
}

bool asserted_formulas::is_neg_literal(expr * n) {
    if (m_manager.is_not(n))
        return is_pos_literal(to_app(n)->get_arg(0));
    return false;
}

unsigned asserted_formulas::get_formulas_last_level() const {
    if (m_scopes.empty()) {
        return 0;
    }
    else {
        return m_scopes.back().m_asserted_formulas_lim;
    }
}


/**
   \brief (ite x (= c1 y) (= c2 y)) where y is a constant. -> (= y (ite x c1 c2))
*/
bool asserted_formulas::solve_ite_definition_core(expr * lhs1, expr * rhs1, expr * lhs2, expr * rhs2, expr * cond, app_ref & var, expr_ref & subst) {
    if (rhs1 == rhs2 && is_uninterp_const(rhs1) && !occurs(rhs1, cond) && !occurs(rhs1, lhs1) && !occurs(rhs1, lhs2)) {
        var = to_app(rhs1);
        m_bsimp->mk_ite(cond, lhs1, lhs2, subst);
        return true;
    }
    return false;
}

bool asserted_formulas::solve_ite_definition(expr * arg1, expr * arg2, expr * arg3, app_ref & var, expr_ref & subst) {

    if (!m_manager.is_eq(arg2) || !m_manager.is_eq(arg3)) 
        return false;

    app * app2  = to_app(arg2);
    app * app3  = to_app(arg3);
    expr * lhs1 = app2->get_arg(0);
    expr * rhs1 = app2->get_arg(1);
    expr * lhs2 = app3->get_arg(0);
    expr * rhs2 = app3->get_arg(1);

    if (solve_ite_definition_core(lhs1, rhs1, lhs2, rhs2, arg1, var, subst))
        return true;
    if (solve_ite_definition_core(rhs1, lhs1, lhs2, rhs2, arg1, var, subst))
        return true;
    if (solve_ite_definition_core(lhs1, rhs1, rhs2, lhs2, arg1, var, subst))
        return true;
    if (solve_ite_definition_core(rhs1, lhs1, rhs2, lhs2, arg1, var, subst))
        return true;
    return false;
}

bool asserted_formulas::solve_core(expr * n, app_ref & var, expr_ref & subst, proof_ref& pr) {
    if (m_manager.is_eq(n)) {
        // equality case
        app * eq   = to_app(n);
        expr * lhs = eq->get_arg(0);
        expr * rhs = eq->get_arg(1);
        TRACE("solve_bug", tout << mk_bounded_pp(n, m_manager) << "\n" << mk_bounded_pp(lhs, m_manager) << "\n" << mk_bounded_pp(rhs, m_manager) << "\n";);
        if (trivial_solve(lhs, rhs, var, subst, pr)) {
            return true;
        }
        else {
            sort * s          = m_manager.get_sort(lhs);
            family_id fid     = s->get_family_id();
            solver_plugin * p = m_solver_plugins.get_plugin(fid);
            if (p != 0 && p->solve(lhs, rhs, m_forbidden, var, subst)) {
                if (m_manager.proofs_enabled()) {
                    app* new_eq = m_manager.mk_eq(var,subst);
                    pr = m_manager.mk_th_lemma(p->get_family_id(), m_manager.mk_iff(n,new_eq),0,0);
                }
                TRACE("solve_bug", tout << "theory solve\n";);
                return true;
            }
        }
        return false;
    }
    else if (m_manager.is_iff(n)) {
        // <=> case
        app * iff  = to_app(n);
        expr * lhs = iff->get_arg(0);
        expr * rhs = iff->get_arg(1);
        if (trivial_solve(lhs, rhs, var, subst, pr)) {
            return true;
        }
        return false;
    }
    else {
        if (m_manager.is_ite(n)) {
            //
            // (ite x (= c1 y) (= c2 y)) where y is a constant. -> (= y (ite x c1 c2))
            // 
            app * ite = to_app(n);
            if (solve_ite_definition(ite->get_arg(0), ite->get_arg(1), ite->get_arg(2), var, subst)) {
                if (m_manager.proofs_enabled()) {
                    pr = m_manager.mk_rewrite(n, m_manager.mk_eq(var, subst));
                }
                return true;
            }
        }

        // check if literal
        expr * lit = n;
        if (is_pos_literal(lit)) {
            var   = to_app(lit);
            subst = m_manager.mk_true();
            if (m_manager.proofs_enabled()) {
                // [rewrite]: (iff (iff l true) l)
                // [symmetry T1]: (iff l (iff l true))
                pr = m_manager.mk_rewrite(m_manager.mk_eq(var, subst), n);
                pr = m_manager.mk_symmetry(pr);
            }
            
            return true;
        }
        else if (is_neg_literal(lit)) {
            var   = to_app(to_app(lit)->get_arg(0));
            subst = m_manager.mk_false(); 
            if (m_manager.proofs_enabled()) {
                // [rewrite]: (iff (iff l false) ~l)
                // [symmetry T1]: (iff ~l (iff l false))
                pr = m_manager.mk_rewrite(m_manager.mk_eq(var, subst), n);
                pr = m_manager.mk_symmetry(pr);
            }

            return true;
        }
    }
    return false;
}

void asserted_formulas::collect_static_features() {
    if (m_params.m_display_features) {
        unsigned sz   = m_asserted_formulas.size();
        unsigned head = m_asserted_qhead;
        while (head < sz) {
            expr * f   = m_asserted_formulas.get(head);
            head++;
            m_static_features.collect(f);
        }
        m_static_features.display_primitive(std::cout);
        m_static_features.display(std::cout);
    }
}

void asserted_formulas::display(std::ostream & out) const {
    out << "asserted formulas:\n";
    for (unsigned i = 0; i < m_asserted_formulas.size(); i++) {
        if (i == m_asserted_qhead)
            out << "[HEAD] ==>\n";
        out << mk_ismt2_pp(m_asserted_formulas.get(i), m_manager) << "\n";
    }
    out << "inconsistent: " << inconsistent() << "\n";
}

void asserted_formulas::display_ll(std::ostream & out, ast_mark & pp_visited) const {
    if (!m_asserted_formulas.empty()) {
        unsigned sz = m_asserted_formulas.size();
        for (unsigned i = 0; i < sz; i++) 
            ast_def_ll_pp(out, m_manager, m_asserted_formulas.get(i), pp_visited, true, false);
        out << "asserted formulas:\n";
        for (unsigned i = 0; i < sz; i++) 
            out << "#" << m_asserted_formulas[i]->get_id() << " ";
        out << "\n";
    }
}

void asserted_formulas::collect_statistics(statistics & st) const {
    // m_quant_elim.collect_statistics(st);
}

/**
   \brief Functor used to order solved equations x = t, in a way they can be solved
   efficiently.
*/
class top_sort {
    enum color { White, Grey, Black };
    ast_manager &                m_manager;
    family_id                    m_bfid;
    
    expr_map *                   m_candidate_map;  // Set of candidate substitutions var -> ast
    obj_map<app, unsigned>       m_var2idx;        // var -> index in vars;
    ptr_vector<app> *            m_ordered_vars;   // Result1: set of variables ordered for applying substitution efficiently.
    unsigned_vector *            m_failed_idxs;    // Result2: indices of substitutions that cannot be applied.
    
    svector<color>               m_colors;
    ptr_vector<expr>             m_todo;
    
    expr * get_candidate_def(expr * n) const {
        if (is_app(n) && to_app(n)->get_num_args() == 0 && m_candidate_map->contains(n)) {
            expr *  d = 0;
            proof * p = 0;
            m_candidate_map->get(n, d, p);
            SASSERT(d);
            return d;
        }
        return 0;
    }

    bool is_candidate(expr * n) const {
        return get_candidate_def(n) != 0;
    }
    
    void remove_candidate(app * n) {
        TRACE("solve", tout << "removing candidate #" << n->get_id() << " " << mk_bounded_pp(n, m_manager) << "\n";);
        unsigned idx = UINT_MAX;
        m_var2idx.find(n, idx);
        SASSERT(idx != UINT_MAX);
        m_candidate_map->erase(n);
        m_failed_idxs->push_back(idx);
    }

    color get_color(expr * n) const {
        return m_colors.get(n->get_id(), White);
    }

    void set_color(expr * n, color c) {
        unsigned id  = n->get_id();
        m_colors.reserve(id+1, White);
        m_colors[id] = c;
        if (c == Black && is_candidate(n))
            m_ordered_vars->push_back(to_app(n));
    }

    void main_loop(app * n) {
        m_todo.push_back(n);
        expr * def;
        while (!m_todo.empty()) {
            expr * n = m_todo.back();
            switch (get_color(n)) {
            case Black: 
                m_todo.pop_back();
                break;
            case White: 
                set_color(n, Grey); 
                if (visit_children(n)) {
                    set_color(n, Black);
            }
                break;
            case Grey:
                if (all_black_children(n)) {
                    set_color(n, Black);
                }
                else {
                    def = get_candidate_def(n);
                    if (def) {
                        // Break loop
                        remove_candidate(to_app(n));
                        set_color(n, Black);
                    }
                    // there is another occurrence of n on the stack
                    SASSERT(std::find(m_todo.begin(), m_todo.end() - 1, n) != m_todo.end());
                }
                m_todo.pop_back();
            }
        }
    }

    void visit(expr * n, bool & visited) {
        if (get_color(n) != Black) {
            m_todo.push_back(n);
            visited = false;
        }
    }

    bool visit_children(expr * n) {
        bool visited = true;
        unsigned j;
        expr * def;
        switch (n->get_kind()) {
        case AST_VAR:
            break;
        case AST_APP:
            j = to_app(n)->get_num_args();
            if (j == 0) {
                def = get_candidate_def(n);
                if (def) 
                    visit(def, visited);
            }
            else {
                while (j > 0) {
                    --j;
                    visit(to_app(n)->get_arg(j), visited);
                }
            }
            break;
        case AST_QUANTIFIER:
            visit(to_quantifier(n)->get_expr(), visited);
            break;
        default:
            UNREACHABLE();
        }
        return visited;
    }
    
    bool is_black(expr * n) const {
        return get_color(n) == Black;
    }

    bool all_black_children(expr * n) const {
        expr * def;
        unsigned j;
        switch (n->get_kind()) {
        case AST_VAR:
            return true;
        case AST_APP:
            j = to_app(n)->get_num_args();
            if (j == 0) {
                def = get_candidate_def(n);
                if (def)
                    return is_black(def);
                return true;
            }
            else {
                while (j > 0) {
                    --j;
                    if (!is_black(to_app(n)->get_arg(j))) {
                        return false;
                    }
                }
            }
            return true;
        case AST_QUANTIFIER:
            return is_black(to_quantifier(n)->get_expr());
        default:
            UNREACHABLE();
            return true;
        }
    }
    
public:
    top_sort(ast_manager & m):m_manager(m), m_bfid(m.get_basic_family_id()) {}
    
    void operator()(ptr_vector<app> const & vars, 
                    expr_map & candidates, 
                    ptr_vector<app> & ordered_vars,
                    unsigned_vector & failed_idxs) {
        m_var2idx.reset();
        ptr_vector<app>::const_iterator it  = vars.begin();
        ptr_vector<app>::const_iterator end = vars.end();
        for (unsigned idx = 0; it != end; ++it, ++idx)
            m_var2idx.insert(*it, idx);
        m_candidate_map = &candidates;
        m_ordered_vars  = &ordered_vars;
        m_failed_idxs   = &failed_idxs;
        m_colors.reset();
        it  = vars.begin();
        end = vars.end();
        for (; it != end; ++it) {
            TRACE("top_sort", tout << "processing: " << (*it)->get_decl()->get_name() << "\n";);
            main_loop(*it);
        }
    }
};

void asserted_formulas::get_ordered_subst_vars(ptr_vector<app> & ordered_vars) {
    top_sort sort(m_manager);
    unsigned_vector failed_idxs;
    sort(m_vars, m_subst, ordered_vars, failed_idxs);
    SASSERT(failed_idxs.empty());
}

bool asserted_formulas::solve_core() {
    flush_cache();

    expr_map             tmp_subst(m_manager);
    ptr_vector<app>      tmp_vars;  // domain of m_tmp_subst
    expr_ref_vector      candidates(m_manager);
    proof_ref_vector     candidate_prs(m_manager);
   
    IF_IVERBOSE(10, verbose_stream() << "solving...\n";);
    bool has_subst = false;
    app_ref         var(m_manager);
    expr_ref        subst(m_manager);
    proof_ref       pr1(m_manager);
    unsigned i  = m_asserted_qhead;
    unsigned j  = i;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        TRACE("solve", tout << "processing... #" << n->get_id() << "\n";);
        TRACE("solve", tout << mk_bounded_pp(n, m_manager, 3) << "\n";
              if (pr) tout << mk_bounded_pp(pr, m_manager, 3) << "\n";);

        if (solve_core(n, var, subst, pr1) && !m_forbidden.is_marked(var)) {
            if (m_manager.proofs_enabled()) {
                // TODO: refine potentially useless rewrite step
                if (m_manager.is_eq(n) && to_app(n)->get_arg(0) == var && 
                    to_app(n)->get_arg(1) == subst) {
                    // skip useless rewrite step.
                }
                else {
                    TRACE("solve", tout << mk_bounded_pp(n, m_manager, 3) << "\n";
                          tout << mk_bounded_pp(pr1.get(), m_manager, 5) << "\n";);
                    pr = m_manager.mk_modus_ponens(pr, pr1.get());
                }
                candidate_prs.push_back(pr);
            }

            tmp_subst.insert(var, subst, pr);
            SASSERT(!m_forbidden.is_marked(var));
            TRACE("solve_subst", tout << mk_pp(var, m_manager) << "\n" << mk_pp(subst, m_manager) << "\n";);
            TRACE("solver_bug", tout << mk_pp(var, m_manager) << "\n" << mk_pp(subst, m_manager) << "\n";);
            tmp_vars.push_back(var);
            m_forbidden.mark(var, true);
            candidates.push_back(n);                
            has_subst = true;
            continue;
        }
        if (j < i) {
            m_asserted_formulas.set(j, n);
            if (m_manager.proofs_enabled())
                m_asserted_formula_prs.set(j, pr);
        }
        j++;
    }
    m_asserted_formulas.shrink(j);
    if (m_manager.proofs_enabled())
        m_asserted_formula_prs.shrink(j);

    if (!has_subst) 
        return false;

    ptr_vector<app> ordered_vars;
    unsigned_vector failed_idxs;
    top_sort sort(m_manager);
    sort(tmp_vars, tmp_subst, ordered_vars, failed_idxs);
    // restore substitutions that cannot be applied due to loops.
    unsigned_vector::iterator it  = failed_idxs.begin();
    unsigned_vector::iterator end = failed_idxs.end();
    for (; it != end; ++it) {
        unsigned idx = *it;
        m_asserted_formulas.push_back(candidates.get(idx));
        if (m_manager.proofs_enabled())
            m_asserted_formula_prs.push_back(candidate_prs.get(idx));
        app * var = tmp_vars[idx];
        m_forbidden.mark(var, false);
    }
    IF_IVERBOSE(10, verbose_stream() << "num. eliminated vars: " << ordered_vars.size() << "\n";);
    ptr_vector<app>::iterator it2  = ordered_vars.begin();
    ptr_vector<app>::iterator end2 = ordered_vars.end();
    for (; it2 != end2; ++it2) {
        app * var  = *it2;
        TRACE("solve_res", tout << "var: " << mk_pp(var, m_manager) << "\n";);
        expr * def = 0;
        proof * pr = 0;
        tmp_subst.get(var, def, pr);
        SASSERT(def != 0);
        SASSERT(m_forbidden.is_marked(var));
        m_forbidden.mark(var, false);
        expr_ref  new_def(m_manager);
        proof_ref def_eq_new_def_pr(m_manager);
        proof_ref new_pr(m_manager);
        TRACE("solve_res", tout << "reducing:\n" << mk_ll_pp(def, m_manager););
        m_simplifier(def, new_def, def_eq_new_def_pr);
        TRACE("solve_res", tout << "reducing:\n" << mk_ll_pp(new_def, m_manager););
        new_pr = m_manager.mk_transitivity(pr, def_eq_new_def_pr);
        m_subst.insert(var, new_def, new_pr);
        m_vars.push_back(var);
        TRACE("solve_res", tout << "new substitution:\n" << mk_ll_pp(var, m_manager) << "======>\n" << mk_ll_pp(new_def, m_manager););
    }
    return !ordered_vars.empty();
}

void asserted_formulas::solve() {
    // This method is buggy when unsatisfiable cores are enabled.
    // It may eliminate answer literals.
    // Since I will remove asserted_formulas.cpp in the future, I just disabled it.
    // Note: asserted_formulas.cpp is based on the obsolete preprocessing stack.
    // Users should the solve-eqs tactic if they want to eliminate variables. 
#if 0
    while (solve_core()) {
        IF_IVERBOSE(10, verbose_stream() << "reducing...\n";);
        flush_cache(); // collect garbage
        reduce_asserted_formulas();
    }
#endif
}

void asserted_formulas::reduce_asserted_formulas() {
    if (inconsistent()) {
        return;
    }
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz && !inconsistent(); i++) {
        expr * n    = m_asserted_formulas.get(i);
        SASSERT(n != 0);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        expr_ref new_n(m_manager);
        proof_ref new_pr(m_manager);
        m_simplifier(n, new_n, new_pr);
        TRACE("reduce_asserted_formulas", tout << mk_pp(n, m_manager) << " -> " << mk_pp(new_n, m_manager) << "\n";);
        if (n == new_n.get()) {
            push_assertion(n, pr, new_exprs, new_prs);
        }
        else {
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);
            push_assertion(new_n, new_pr, new_exprs, new_prs);
        }
        if (canceled()) {
            return;
        }
    }
    swap_asserted_formulas(new_exprs, new_prs);
}

void asserted_formulas::swap_asserted_formulas(expr_ref_vector & new_exprs, proof_ref_vector & new_prs) {
    SASSERT(!inconsistent() || !new_exprs.empty());
    m_asserted_formulas.shrink(m_asserted_qhead);
    m_asserted_formulas.append(new_exprs);
    if (m_manager.proofs_enabled()) {
        m_asserted_formula_prs.shrink(m_asserted_qhead);
        m_asserted_formula_prs.append(new_prs);
    }
}

void asserted_formulas::find_macros_core() {
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);
    unsigned sz = m_asserted_formulas.size();
    m_macro_finder->operator()(sz - m_asserted_qhead, m_asserted_formulas.c_ptr() + m_asserted_qhead, 
                               m_asserted_formula_prs.c_ptr() + m_asserted_qhead, new_exprs, new_prs);
    swap_asserted_formulas(new_exprs, new_prs);
    reduce_and_solve();
}

void asserted_formulas::find_macros() {
    IF_IVERBOSE(10, verbose_stream() << "trying to find macros...\n";);
    TRACE("before_find_macros", display(tout););
    find_macros_core();
    TRACE("after_find_macros", display(tout););
}

void asserted_formulas::expand_macros() {
    IF_IVERBOSE(10, verbose_stream() << "expanding macros...\n";);
    find_macros_core();
}

void asserted_formulas::apply_demodulators() {
#if 0
    IF_IVERBOSE(10, verbose_stream() << "applying demodulators...\n";);
    TRACE("before_apply_demodulators", display(tout););
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);
    unsigned sz = m_asserted_formulas.size();
    ufbv_rewriter proc(m_manager, *m_bsimp);
    proc(sz - m_asserted_qhead, 
         m_asserted_formulas.c_ptr() + m_asserted_qhead, 
         m_asserted_formula_prs.c_ptr() + m_asserted_qhead,
         new_exprs, new_prs);
    swap_asserted_formulas(new_exprs, new_prs);
    TRACE("after_apply_demodulators", display(tout););
    reduce_and_solve();
#endif
}

void asserted_formulas::apply_quasi_macros() {
    IF_IVERBOSE(10, verbose_stream() << "finding quasi macros...\n";);
    TRACE("before_quasi_macros", display(tout););
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);      
    quasi_macros proc(m_manager, m_macro_manager, *m_bsimp, m_simplifier);    
    while (proc(m_asserted_formulas.size() - m_asserted_qhead, 
                m_asserted_formulas.c_ptr() + m_asserted_qhead, 
                m_asserted_formula_prs.c_ptr() + m_asserted_qhead,
                new_exprs, new_prs)) {
        swap_asserted_formulas(new_exprs, new_prs);
        new_exprs.reset();
        new_prs.reset();
    }
    TRACE("after_quasi_macros", display(tout););
    reduce_and_solve();
}

void asserted_formulas::nnf_cnf() {
    IF_IVERBOSE(10, verbose_stream() << "applying nnf&cnf...\n";);
    nnf              apply_nnf(m_manager, m_defined_names, m_params);
    cnf              apply_cnf(m_manager, m_defined_names, m_params);
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);
    expr_ref_vector  cnf_todo(m_manager);
    proof_ref_vector cnf_todo_prs(m_manager);
    expr_ref_vector  push_todo(m_manager);
    proof_ref_vector push_todo_prs(m_manager);
    
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    TRACE("nnf_bug", tout << "i: " << i << " sz: " << sz << "\n";);
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        TRACE("nnf_bug", tout << "processing:\n" << mk_pp(n, m_manager) << "\n";);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        cnf_todo.reset();
        cnf_todo_prs.reset();
        expr_ref   r1(m_manager);
        proof_ref  pr1(m_manager);
        CASSERT("well_sorted",is_well_sorted(m_manager, n));
        apply_nnf(n, cnf_todo, cnf_todo_prs, r1, pr1);
        CASSERT("well_sorted",is_well_sorted(m_manager, r1));
        pr = m_manager.mk_modus_ponens(pr, pr1);
        cnf_todo.push_back(r1);
        cnf_todo_prs.push_back(pr);

        if (canceled()) {
            return;
        }
        
        unsigned sz1 = cnf_todo.size();
        for (unsigned j = 0; j < sz1; j++) {
            push_todo.reset();
            push_todo_prs.reset();

            if (canceled()) {
                return;
            }        
        
            expr * n   = cnf_todo.get(j);
            proof * pr = m_manager.proofs_enabled() ? cnf_todo_prs.get(j) : 0;
        
            CASSERT("well_sorted",is_well_sorted(m_manager, n));
            apply_cnf(n, push_todo, push_todo_prs, r1, pr1);
            CASSERT("well_sorted",is_well_sorted(m_manager, r1));

            push_todo.push_back(r1);

            if (m_manager.proofs_enabled()) {
                pr = m_manager.mk_modus_ponens(pr, pr1);
                push_todo_prs.push_back(pr);
            }
        
            unsigned sz2 = push_todo.size();
            for (unsigned k = 0; k < sz2; k++) {
                expr * n   = push_todo.get(k);
                proof * pr = 0;
                m_simplifier(n, r1, pr1);
                CASSERT("well_sorted",is_well_sorted(m_manager, r1));
                if (canceled()) {
                    return;
                }        
                
                if (m_manager.proofs_enabled())
                    pr = m_manager.mk_modus_ponens(push_todo_prs.get(k), pr1);
                else
                    pr = 0;
                push_assertion(r1, pr, new_exprs, new_prs);
            }
        }
    }
    swap_asserted_formulas(new_exprs, new_prs);
}

#define MK_SIMPLE_SIMPLIFIER(NAME, FUNCTOR_DEF, LABEL, MSG)                                                             \
void asserted_formulas::NAME() {                                                                                        \
    IF_IVERBOSE(10, verbose_stream() << MSG << "...\n";);                                                                      \
    TRACE(LABEL, tout << "before:\n"; display(tout););                                                                  \
    FUNCTOR_DEF;                                                                                                        \
    expr_ref_vector  new_exprs(m_manager);                                                                              \
    proof_ref_vector new_prs(m_manager);                                                                                \
    unsigned i  = m_asserted_qhead;                                                                                     \
    unsigned sz = m_asserted_formulas.size();                                                                           \
    for (; i < sz; i++) {                                                                                               \
        expr * n    = m_asserted_formulas.get(i);                                                                       \
        proof * pr  = m_asserted_formula_prs.get(i, 0);                                                                 \
        expr_ref new_n(m_manager);                                                                                      \
        functor(n, new_n);                                                                                              \
        TRACE("simplifier_simple_step", tout << mk_pp(n, m_manager) << "\n" << mk_pp(new_n, m_manager) << "\n";);       \
        if (n == new_n.get()) {                                                                                         \
            push_assertion(n, pr, new_exprs, new_prs);                                                                  \
        }                                                                                                               \
        else if (m_manager.proofs_enabled()) {                                                                          \
            proof_ref new_pr(m_manager);                                                                                \
            new_pr = m_manager.mk_rewrite_star(n, new_n, 0, 0);            \
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);                                                             \
            push_assertion(new_n, new_pr, new_exprs, new_prs);                                                          \
        }                                                                                                               \
        else {                                                                                                          \
            push_assertion(new_n, 0, new_exprs, new_prs);                                                               \
        }                                                                                                               \
    }                                                                                                                   \
    swap_asserted_formulas(new_exprs, new_prs);                                                                         \
    TRACE(LABEL, display(tout););                                                                                       \
    reduce_and_solve();                                                                                                 \
    TRACE(LABEL, display(tout););                                                                                       \
}

MK_SIMPLE_SIMPLIFIER(apply_distribute_forall, distribute_forall functor(m_manager, *m_bsimp), "distribute_forall", "distribute forall");

void asserted_formulas::reduce_and_solve() {
    IF_IVERBOSE(10, verbose_stream() << "reducing...\n";);
    flush_cache(); // collect garbage
    reduce_asserted_formulas();
    if (m_params.m_solver)
        solve();
}

void asserted_formulas::infer_patterns() {
    IF_IVERBOSE(10, verbose_stream() << "pattern inference...\n";);
    TRACE("before_pattern_inference", display(tout););
    pattern_inference infer(m_manager, m_params);
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        expr_ref  new_n(m_manager);
        proof_ref new_pr(m_manager);
        infer(n, new_n, new_pr);
        if (n == new_n.get()) {
            push_assertion(n, pr, new_exprs, new_prs);
        }
        else if (m_manager.proofs_enabled()) {
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);
            push_assertion(new_n, new_pr, new_exprs, new_prs);
        }
        else {
            push_assertion(new_n, 0, new_exprs, new_prs);
        }
    }
    swap_asserted_formulas(new_exprs, new_prs);
    TRACE("after_pattern_inference", display(tout););
}

struct mark_forbidden_proc {
    expr_mark        &  m_forbidden; 
    ptr_vector<app>  &  m_forbidden_vars;
    mark_forbidden_proc(expr_mark & f, ptr_vector<app> & v):m_forbidden(f), m_forbidden_vars(v) {}
    void operator()(var * n) {}
    void operator()(quantifier * n) {}
    void operator()(app * n) {
        if (is_uninterp(n) && !m_forbidden.is_marked(n)) {
            TRACE("solver_bug", tout << "marking: " << n->get_decl()->get_name() << "\n";);
            m_forbidden.mark(n, true);
            m_forbidden_vars.push_back(n);
            SASSERT(m_forbidden.is_marked(n));
        }
    }
};

void asserted_formulas::commit() {
    expr_fast_mark1 uf_visited; // marks used for update_forbidden
    mark_forbidden_proc p(m_forbidden, m_forbidden_vars);
    unsigned sz = m_asserted_formulas.size();
    for (unsigned i = m_asserted_qhead; i < sz; i++)
        quick_for_each_expr(p, uf_visited, m_asserted_formulas.get(i));

    m_macro_manager.mark_forbidden(sz - m_asserted_qhead, m_asserted_formulas.c_ptr() + m_asserted_qhead);

    ptr_vector<app>::const_iterator it2  = m_vars.begin() + m_vars_qhead;
    ptr_vector<app>::const_iterator end2 = m_vars.end();
    for (; it2 != end2; ++it2) {
        app * var = *it2;
        expr * def = get_subst(var);
        m_forbidden.mark(var, true);
        m_forbidden_vars.push_back(var);
        quick_for_each_expr(p, uf_visited, def);
    }
    m_vars_qhead     = m_vars.size();
    m_asserted_qhead = m_asserted_formulas.size();
}

void asserted_formulas::eliminate_term_ite() {
    IF_IVERBOSE(10, verbose_stream() << "eliminating ite term...\n";);
    TRACE("before_elim_term_ite", display(tout););
    elim_term_ite   elim(m_manager, m_defined_names);
    expr_ref_vector  new_exprs(m_manager);
    proof_ref_vector new_prs(m_manager);
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        expr_ref  new_n(m_manager);
        proof_ref new_pr(m_manager);
        elim(n, new_exprs, new_prs, new_n, new_pr);
        SASSERT(new_n.get() != 0);
        DEBUG_CODE({
                for (unsigned i = 0; i < new_exprs.size(); i++) {
                    SASSERT(new_exprs.get(i) != 0);
                }
            });
        if (n == new_n.get()) {
            push_assertion(n, pr, new_exprs, new_prs);
        }
        else if (m_manager.proofs_enabled()) {
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);
            push_assertion(new_n, new_pr, new_exprs, new_prs);
        }
        else {
            push_assertion(new_n, 0, new_exprs, new_prs);
        }
    }
    swap_asserted_formulas(new_exprs, new_prs);
    TRACE("after_elim_term_ite", display(tout););
    reduce_and_solve();
    TRACE("after_elim_term_ite", display(tout););
}

void asserted_formulas::propagate_values() {
    IF_IVERBOSE(10, verbose_stream() << "constant propagation...\n";);
    TRACE("propagate_values", tout << "before:\n"; display(tout););
    flush_cache();
    bool found = false;
    // Separate the formulas in two sets: C and R
    // C is a set which contains formulas of the form
    // { x = n }, where x is a variable and n a numberal.
    // R contains the rest.
    // 
    // - new_exprs1 is the set C
    // - new_exprs2 is the set R
    //
    // The loop also updates the m_cache. It adds the entries x -> n to it.
    expr_ref_vector  new_exprs1(m_manager);
    proof_ref_vector new_prs1(m_manager);
    expr_ref_vector  new_exprs2(m_manager);
    proof_ref_vector new_prs2(m_manager);
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        if (m_manager.is_eq(n)) {
            expr * lhs = to_app(n)->get_arg(0);
            expr * rhs = to_app(n)->get_arg(1);
            if (m_manager.is_value(lhs) || m_manager.is_value(rhs)) {
                if (m_manager.is_value(lhs))
                    std::swap(lhs, rhs);
                if (!m_manager.is_value(lhs) && !m_simplifier.is_cached(lhs)) {
                    new_exprs1.push_back(n);
                    if (m_manager.proofs_enabled())
                        new_prs1.push_back(pr);
                    TRACE("propagate_values", tout << "found:\n" << mk_pp(lhs, m_manager) << "\n->\n" << mk_pp(rhs, m_manager) << "\n";);
                    m_simplifier.cache_result(lhs, rhs, pr);
                    found = true;
                    continue;
                }
            }
        }
        new_exprs2.push_back(n);
        if (m_manager.proofs_enabled())
            new_prs2.push_back(pr);
    }
    TRACE("propagate_values", tout << "found: " << found << "\n";);
    // If C is not empty, then reduce R using the updated simplifier cache with entries
    // x -> n for each constraint 'x = n' in C.
    if (found) {
        unsigned sz = new_exprs2.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * n    = new_exprs2.get(i);
            proof * pr  = new_prs2.get(i, 0);
            expr_ref new_n(m_manager);
            proof_ref new_pr(m_manager);
            m_simplifier(n, new_n, new_pr);
            if (n == new_n.get()) {
                push_assertion(n, pr, new_exprs1, new_prs1);
            }
            else {
                new_pr = m_manager.mk_modus_ponens(pr, new_pr);
                push_assertion(new_n, new_pr, new_exprs1, new_prs1);
            }
        }
        swap_asserted_formulas(new_exprs1, new_prs1);
        // IMPORTANT: the cache MUST be flushed. This guarantees that all entries
        // x->n will be removed from m_cache. If we don't do that, the next transformation
        // may simplify constraints in C using these entries, and the variables x in C
        // will be (silently) eliminated, and models produced by Z3 will not contain them.
        flush_cache(); 
    }
    TRACE("propagate_values", tout << "afer:\n"; display(tout););
}

void asserted_formulas::propagate_booleans() {
    bool cont     = true;
    bool modified = false;
    flush_cache();
    while (cont) {
        TRACE("propagate_booleans", tout << "before:\n"; display(tout););
        IF_IVERBOSE(10, verbose_stream() << "boolean propagation...\n";);
        cont        = false;
        unsigned i  = m_asserted_qhead;
        unsigned sz = m_asserted_formulas.size();
#define PROCESS() {                                                                                                             \
            expr * n    = m_asserted_formulas.get(i);                                                                           \
            proof * pr  = m_asserted_formula_prs.get(i, 0);                                                                     \
            expr_ref new_n(m_manager);                                                                                          \
            proof_ref new_pr(m_manager);                                                                                        \
            m_simplifier(n, new_n, new_pr);                                                                                     \
            m_asserted_formulas.set(i, new_n);                                                                                  \
            if (m_manager.proofs_enabled()) {                                                                                   \
                new_pr = m_manager.mk_modus_ponens(pr, new_pr);                                                                 \
                m_asserted_formula_prs.set(i, new_pr);                                                                          \
            }                                                                                                                   \
            if (n != new_n) {                                                                                                   \
                cont = true;                                                                                                    \
                modified = true;                                                                                                \
            }                                                                                                                   \
            if (m_manager.is_not(new_n))                                                                                        \
                m_simplifier.cache_result(to_app(new_n)->get_arg(0), m_manager.mk_false(), m_manager.mk_iff_false(new_pr));     \
            else                                                                                                                \
                m_simplifier.cache_result(new_n, m_manager.mk_true(), m_manager.mk_iff_true(new_pr));                           \
        }
        for (; i < sz; i++) {
            PROCESS();
        }
        flush_cache();
        TRACE("propagate_booleans", tout << "middle:\n"; display(tout););
        i = sz;
        while (i > m_asserted_qhead) {
            --i;
            PROCESS();
        }
        flush_cache();
        TRACE("propagate_booleans", tout << "after:\n"; display(tout););
    }
    if (modified)
        reduce_asserted_formulas();
}

#define MK_SIMPLIFIER(NAME, FUNCTOR, TAG, MSG, REDUCE)                  \
bool asserted_formulas::NAME() {                                        \
    IF_IVERBOSE(10, verbose_stream() << MSG << "...\n";);               \
    TRACE(TAG, ast_mark visited; display_ll(tout, visited););           \
    FUNCTOR;                                                            \
    bool changed = false;                                               \
    expr_ref_vector  new_exprs(m_manager);                              \
    proof_ref_vector new_prs(m_manager);                                \
    unsigned i  = m_asserted_qhead;                                     \
    unsigned sz = m_asserted_formulas.size();                           \
    for (; i < sz; i++) {                                               \
        expr * n    = m_asserted_formulas.get(i);                       \
        proof * pr  = m_asserted_formula_prs.get(i, 0);                 \
        expr_ref  new_n(m_manager);                                     \
        proof_ref new_pr(m_manager);                                    \
        functor(n, new_n, new_pr);                                      \
        if (n == new_n.get()) {                                         \
            push_assertion(n, pr, new_exprs, new_prs);                  \
        }                                                               \
        else if (m_manager.proofs_enabled()) {                          \
            changed = true;                                             \
            if (!new_pr) new_pr = m_manager.mk_rewrite(n, new_n);       \
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);             \
            push_assertion(new_n, new_pr, new_exprs, new_prs);          \
        }                                                               \
        else {                                                          \
            changed = true;                                             \
            push_assertion(new_n, 0, new_exprs, new_prs);               \
        }                                                               \
    }                                                                   \
    swap_asserted_formulas(new_exprs, new_prs);                         \
    TRACE(TAG, ast_mark visited; display_ll(tout, visited););           \
    if (changed && REDUCE) {                                            \
        reduce_and_solve();                                             \
        TRACE(TAG, ast_mark visited; display_ll(tout, visited););       \
    }                                                                   \
    return changed;                                                     \
}

MK_SIMPLIFIER(pull_cheap_ite_trees, pull_cheap_ite_tree_star functor(m_manager, m_simplifier), "pull_cheap_ite_trees", "pull cheap ite trees", false);

MK_SIMPLIFIER(pull_nested_quantifiers, pull_nested_quant functor(m_manager), "pull_nested_quantifiers", "pull nested quantifiers", false);

proof * asserted_formulas::get_inconsistency_proof() const {
    if (!inconsistent())
        return 0;
    if (!m_manager.proofs_enabled())
        return 0;
    unsigned sz = m_asserted_formulas.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * f = m_asserted_formulas.get(i);
        if (m_manager.is_false(f))
            return m_asserted_formula_prs.get(i);
    }
    UNREACHABLE();
    return 0;
}

MK_SIMPLE_SIMPLIFIER(context_simplifier, expr_context_simplifier functor(m_manager), "context_simplifier", "context simplifier");

MK_SIMPLE_SIMPLIFIER(strong_context_simplifier, expr_strong_context_simplifier functor(m_params, m_manager), "strong_context_simplifier", "strong context simplifier");


void asserted_formulas::refine_inj_axiom() {
    IF_IVERBOSE(10, verbose_stream() << "refining injectivity...\n";);
    TRACE("inj_axiom", display(tout););
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        expr_ref new_n(m_manager);
        if (is_quantifier(n) && simplify_inj_axiom(m_manager, to_quantifier(n), new_n)) {
            TRACE("inj_axiom", tout << "simplifying...\n" << mk_pp(n, m_manager) << "\n" << mk_pp(new_n, m_manager) << "\n";);
            m_asserted_formulas.set(i, new_n);
            if (m_manager.proofs_enabled()) {
                proof_ref new_pr(m_manager);     
                new_pr = m_manager.mk_rewrite(n, new_n);
                new_pr = m_manager.mk_modus_ponens(pr, new_pr);
                m_asserted_formula_prs.set(i, new_pr);
            }
        }
    }
    TRACE("inj_axiom", display(tout););
}

MK_SIMPLIFIER(apply_bit2int, bit2int& functor = m_bit2int, "bit2int", "propagate bit-vector over integers", true);

MK_SIMPLIFIER(apply_der_core, der_star functor(m_manager), "der", "destructive equality resolution", true);

void asserted_formulas::apply_der() {
    // Keep applying DER until it cannot be applied anymore.
    // The simplifications applied by REDUCE may create new opportunities for applying DER.
    while(!inconsistent() && apply_der_core()) {
    }

    TRACE("a_der", for (unsigned i = 0; i<m_asserted_formulas.size(); i++)
        tout << mk_pp(m_asserted_formulas.get(i), m_manager) << std::endl; );
}


MK_SIMPLIFIER(cheap_quant_fourier_motzkin, elim_bounds_star functor(m_manager), "elim_bounds", "cheap fourier-motzkin", true);

// MK_SIMPLIFIER(quant_elim, qe::expr_quant_elim_star1 &functor = m_quant_elim, 
//              "quantifiers", "quantifier elimination procedures", true);

bool asserted_formulas::quant_elim() {
    throw default_exception("QUANT_ELIM option is deprecated, please consider using the 'qe' tactic.");
    return false;
}

MK_SIMPLIFIER(apply_eager_bit_blaster, eager_bit_blaster functor(m_manager, m_params), "eager_bb", "eager bit blasting", false);

MK_SIMPLIFIER(elim_bvs_from_quantifiers, bv_elim_star functor(m_manager), "bv_elim", "eliminate bit-vectors from quantifiers", true);

#define LIFT_ITE(NAME, FUNCTOR, MSG)                                                                                            \
void asserted_formulas::NAME() {                                                                                                \
    IF_IVERBOSE(10, verbose_stream() << MSG;);                                                                                         \
    TRACE("lift_ite", display(tout););                                                                                          \
    FUNCTOR;                                                                                                                    \
    unsigned i  = m_asserted_qhead;                                                                                             \
    unsigned sz = m_asserted_formulas.size();                                                                                   \
    for (; i < sz; i++) {                                                                                                       \
        expr * n    = m_asserted_formulas.get(i);                                                                               \
        proof * pr  = m_asserted_formula_prs.get(i, 0);                                                                         \
        expr_ref  new_n(m_manager);                                                                                             \
        proof_ref new_pr(m_manager);                                                                                            \
        functor(n, new_n, new_pr);                                                                                              \
        TRACE("lift_ite_step", tout << mk_pp(n, m_manager) << "\n";);                                                           \
        IF_IVERBOSE(10000, verbose_stream() << "lift before: " << get_num_exprs(n)  << ", after: " << get_num_exprs(new_n) << "\n";);  \
        m_asserted_formulas.set(i, new_n);                                                                                      \
        if (m_manager.proofs_enabled()) {                                                                                       \
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);                                                                     \
            m_asserted_formula_prs.set(i, new_pr);                                                                              \
        }                                                                                                                       \
    }                                                                                                                           \
    TRACE("lift_ite", display(tout););                                                                                          \
    reduce_and_solve();                                                                                                         \
}

LIFT_ITE(lift_ite, push_app_ite functor(m_simplifier, m_params.m_lift_ite == LI_CONSERVATIVE), "lifting ite...\n");
LIFT_ITE(ng_lift_ite, ng_push_app_ite functor(m_simplifier, m_params.m_ng_lift_ite == LI_CONSERVATIVE), "lifting ng ite...\n");

unsigned asserted_formulas::get_total_size() const {
    expr_mark visited;
    unsigned r  = 0;
    unsigned sz = m_asserted_formulas.size();
    for (unsigned i = 0; i < sz; i++)
        r += get_num_exprs(m_asserted_formulas.get(i), visited);
    return r;
}

void asserted_formulas::max_bv_sharing() {
    IF_IVERBOSE(10, verbose_stream() << "maximizing bv sharing...\n";);
    TRACE("bv_sharing", display(tout););
    unsigned i  = m_asserted_qhead;
    unsigned sz = m_asserted_formulas.size();
    for (; i < sz; i++) {
        expr * n    = m_asserted_formulas.get(i);
        proof * pr  = m_asserted_formula_prs.get(i, 0);
        expr_ref new_n(m_manager);
        proof_ref new_pr(m_manager);
        m_bv_sharing(n, new_n, new_pr);
        m_asserted_formulas.set(i, new_n);
        if (m_manager.proofs_enabled()) {
            new_pr = m_manager.mk_modus_ponens(pr, new_pr);
            m_asserted_formula_prs.set(i, new_pr);
        }
    }
    reduce_asserted_formulas();
    TRACE("bv_sharing", display(tout););
    
}

