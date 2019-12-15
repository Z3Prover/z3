/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/
#include "math/lp/nla_grobner.h"
#include "math/lp/nla_core.h"
#include "math/lp/factorization_factory_imp.h"
using namespace nla;

grobner::grobner(core *c, intervals *s)
    : common(c, s),
      m_gc(m_nex_creator, 
           c->m_reslim,
           c->m_nla_settings.grobner_eqs_threshold(),
           c->m_nla_settings.grobner_superposed_expr_size_limit()
           ),
      m_look_for_fixed_vars_in_rows(false) {
    std::function<void (lp::explanation const& e, std::ostream & out)> de;
    de = [this](lp::explanation const& e, std::ostream& out) { m_core->print_explanation(e, out); };
    m_gc = de;
}

void grobner::grobner_lemmas() {
    c().lp_settings().stats().m_grobner_calls++;
    init();
    ptr_vector<grobner_core::equation> eqs;
    TRACE("grobner", tout << "before:\n"; display(tout););
    compute_basis();
    TRACE("grobner", tout << "after:\n"; display(tout););
}

void grobner::check_eq(grobner_core::equation* target) {
    if (m_intervals->check_nex(target->expr(), target->dep())) {
        TRACE("grobner", tout << "created a lemma for "; m_gc.display_equation(tout, *target) << "\n";
              tout << "vars = \n";
              for (lpvar j : get_vars_of_expr(target->expr())) {
                  c().print_var(j, tout);
              }
              tout << "\ntarget->expr() val = " << get_nex_val(target->expr(), [this](unsigned j) { return c().val(j); }) << "\n";);
        register_report();       
    }
}

void grobner::register_report() {
    m_reported++;
}

void grobner::compute_basis(){
    c().lp_settings().stats().m_grobner_basis_computatins++;
    if (m_rows.size() < 2) {
        TRACE("nla_grobner", tout << "there are only " << m_rows.size() << " rows, exiting compute_basis()\n";);
        return;
    }
    m_gc.compute_basis_loop();

    TRACE("grobner", display(tout););
    for (grobner_core::equation* e : m_gc.equations()) {
        check_eq(e);
    }
}

void grobner::add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, svector<lpvar> & q) {
    if (c().active_var_set_contains(j) || c().var_is_fixed(j)) return;
    TRACE("grobner", tout << "j = " << j << ", "; c().print_var(j, tout) << "\n";);
    const auto& matrix = c().m_lar_solver.A_r();
    c().insert_to_active_var_set(j);
    for (auto & s : matrix.m_columns[j]) {
        unsigned row = s.var();
        if (m_rows.contains(row)) continue;       
        if (matrix.m_rows[row].size() > c().m_nla_settings.grobner_row_length_limit()) {
            TRACE("grobner", tout << "ignore the row " << row << " with the size " << matrix.m_rows[row].size() << "\n";); 
            continue;
        }
        m_rows.insert(row);
        for (auto& rc : matrix.m_rows[row]) {
            add_var_and_its_factors_to_q_and_collect_new_rows(rc.var(), q);
        }
    }

    if (!c().is_monic_var(j))
        return;

    const monic& m = c().emons()[j];
    for (auto fcn : factorization_factory_imp(m, c())) {
        for (const factor& fc: fcn) {
            q.push_back(var(fc));
        }
    }            
}

void grobner::find_nl_cluster() {
    prepare_rows_and_active_vars();
    svector<lpvar> q;
    for (lpvar j : c().m_to_refine) {        
        TRACE("grobner", c().print_monic(c().emons()[j], tout) << "\n";);
        q.push_back(j);
    }
    
    while (!q.empty()) {
        lpvar j = q.back();        
        q.pop_back();
        add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
    }
    set_active_vars_weights();
    TRACE("grobner", display(tout););
}

void grobner::prepare_rows_and_active_vars() {
    m_rows.clear();
    m_rows.resize(c().m_lar_solver.row_count());
    c().clear_and_resize_active_var_set();
}


std::unordered_set<lpvar> grobner::get_vars_of_expr_with_opening_terms(const nex *e ) {
    auto ret = get_vars_of_expr(e);
    auto & ls = c().m_lar_solver;
    svector<lpvar> added;
    for (auto j : ret) {
        added.push_back(j);
    }
    for (unsigned i = 0; i < added.size(); ++i) {
        lpvar j = added[i];
        if (ls.column_corresponds_to_term(j)) {
            const auto& t = c().m_lar_solver.get_term(ls.local_to_external(j));
            for (auto p : t) {
                if (ret.find(p.var()) == ret.end()) {
                    added.push_back(p.var());
                    ret.insert(p.var());
                }
            }
        }
    }
    return ret;
}

void grobner::display_matrix(std::ostream & out) const {
    const auto& matrix = c().m_lar_solver.A_r();
    out << m_rows.size() << " rows" <<"\n";
    out << "the matrix\n";          
    for (const auto & r : matrix.m_rows) {
        c().print_term(r, out) << std::endl;
    }
}

void grobner::init() {
    m_gc.reset();
    m_reported = 0;
    find_nl_cluster();
    c().clear_and_resize_active_var_set();
    TRACE("grobner", tout << "m_rows.size() = " << m_rows.size() << "\n";);
    for (unsigned i : m_rows) {
        add_row(i);
    }
}

void grobner::add_row(unsigned i) {    
    const auto& row = c().m_lar_solver.A_r().m_rows[i];    
    TRACE("grobner", tout << "adding row to gb\n"; c().m_lar_solver.print_row(row, tout) << '\n';
          for (auto p : row) c().print_var(p.var(), tout) << "\n"; );
    nex_creator::sum_factory sf(m_nex_creator);
    ci_dependency* dep = create_sum_from_row(row, m_nex_creator, sf, m_look_for_fixed_vars_in_rows, &m_gc.dep());
    nex* e = m_nex_creator.simplify(sf.mk());
    TRACE("grobner", tout << "e = " << *e << "\n";);
    m_gc.assert_eq_0(e, dep);
}

/// -------------------------------
/// grobner_core

bool grobner_core::compute_basis_loop() {
    while (!done()) {
        if (compute_basis_step()) {
            TRACE("grobner", tout << "progress in compute_basis_step\n";);
            return true;
        }
        TRACE("grobner", tout << "continue compute_basis_loop\n";);
    }
    TRACE("grobner", tout << "return false from compute_basis_loop\n";);
    TRACE("grobner_stats", print_stats(tout););
    return false;
}

// return true iff cannot pick_next()
bool grobner_core::compute_basis_step() {
    equation* eq = pick_next();
    if (!eq) {
        TRACE("grobner", tout << "cannot pick an equation\n";);
        return true;
    }
    m_stats.m_compute_steps++;
    simplify_using_to_superpose(*eq);
    if (!canceled() && simplify_to_superpose_with_eq(eq)) {
        TRACE("grobner", tout << "eq = "; display_equation(tout, *eq););
        superpose(eq);
        insert_to_superpose(eq);
        simplify_m_to_simplify(eq);
        TRACE("grobner", tout << "end of iteration:\n"; display(tout););
    }
    return false;
}

grobner_core::equation* grobner_core::pick_next() {
    equation* r = nullptr;
    ptr_buffer<equation> to_delete;
    for (equation* curr : m_to_simplify) {
        if (is_trivial(curr))
            to_delete.push_back(curr);
        else if (is_simpler(curr, r)) {
            TRACE("grobner", tout << "preferring "; display_equation(tout, *curr););
            r = curr;
        }
    }
    for (equation* e : to_delete)
        del_equation(e);
    if (r)
        m_to_simplify.erase(r);
    TRACE("grobner", tout << "selected equation: "; if (!r) tout << "<null>\n"; else display_equation(tout, *r););
    return r;
}

grobner_core::equation_set const& grobner_core::equations() {
    m_all_eqs.reset();
    for (auto e : m_to_simplify) m_all_eqs.insert(e);
    for (auto e : m_to_superpose) m_all_eqs.insert(e);
    return m_all_eqs;
}

void grobner_core::reset() {
    del_equations(0);
    SASSERT(m_equations_to_delete.empty());    
    m_to_superpose.reset();
    m_to_simplify.reset();
    m_stats.reset();
}

// Return true if the equation is of the form 0 = 0.
bool grobner_core::is_trivial(equation* eq) const {
    return eq->expr()->is_scalar() && eq->expr()->to_scalar().value().is_zero();
}

// returns true if eq1 is simpler than eq2
bool grobner_core::is_simpler(equation * eq1, equation * eq2) {
    if (!eq2)
        return true;
    if (is_trivial(eq1))
        return true;
    if (is_trivial(eq2))
        return false;
    return m_nex_creator.gt(eq2->expr(), eq1->expr());
}

void grobner_core::del_equation(equation * eq) {
    m_to_superpose.erase(eq);
    m_to_simplify.erase(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
    m_equations_to_delete[eq->m_bidx] = nullptr;
    dealloc(eq);
}

void grobner_core::simplify_using_to_superpose(equation& eq) {
    bool simplified;
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, eq); tout << "using equalities of m_to_superpose of size " << m_to_superpose.size() << "\n";);
    do {
        simplified = false;
        for (equation* p : m_to_superpose) {
            if (simplify_source_target(*p, eq)) {
                simplified = true;
            }
            if (canceled() || eq.expr()->is_scalar()) {
                break;
            }
        }
    }
    while (simplified && !eq.expr()->is_scalar());

    TRACE("grobner",
          if (simplified) { tout << "simplification result: ";  display_equation(tout, eq);}
          else  {tout << "no simplification\n";});
}
           

const nex* grobner_core::get_highest_monomial(const nex* e) const {
    switch (e->type()) {
    case expr_type::MUL:
        return e;
    case expr_type::SUM:
        return e->to_sum()[0];
    case expr_type::VAR:
        return e;
    default:
        TRACE("grobner", tout << *e << "\n";);
        return nullptr;
    }    
}

// source 3f + k + l = 0, so f = (-k - l)/3
// target 2fg + 3fp + e = 0  
// target is replaced by 2(-k/3 - l/3)g + 3(-k/3 - l/3)p + e = -2/3kg -2/3lg - kp -lp + e

bool grobner_core::simplify_target_monomials(equation const& source, equation& target) {
    nex const* high_mon = get_highest_monomial(source.expr());
    if (high_mon == nullptr)
        return false;
    SASSERT(high_mon->all_factors_are_elementary());
    TRACE("grobner_d", tout << "source = "; display_equation(tout, source) << "target = "; display_equation(tout, target) << "high_mon = " << *high_mon << "\n";);

    nex * te = target.m_expr;    
    nex_sum  * targ_sum;
    if (te->is_sum()) {
        targ_sum = to_sum(te);
    } else if (te->is_mul()) {
        targ_sum = m_nex_creator.mk_sum(te);
    } else {
        TRACE("grobner_d", tout << "return false\n";);
        return false;
    }

    return simplify_target_monomials_sum(source, target, *targ_sum, *high_mon);   
}

unsigned grobner_core::find_divisible(nex_sum const& targ_sum, const nex& high_mon) const {
    unsigned j = 0;
    for (auto t : targ_sum) {
        if (divide_ignore_coeffs_check_only(*t, high_mon)) {
            TRACE("grobner_d", tout << "yes div: " << *t << " / " << high_mon << "\n";);
            return j;
        }
        ++j;
    }
    TRACE("grobner_d", tout << "no div: " << targ_sum << " / " << high_mon << "\n";);
    return -1;
}

bool grobner_core::simplify_target_monomials_sum(equation const& source,
                                            equation& target, nex_sum& targ_sum,
                                            const nex& high_mon) {
    unsigned j = find_divisible(targ_sum, high_mon);
    if (j + 1 == 0)
        return false;
    m_changed_leading_term = (j == 0);
    unsigned targ_orig_size = targ_sum.size();
    simplify_target_monomials_sum_j(source, target, targ_sum, high_mon, j, false); // false to avoid divisibility test
    for (j++; j < targ_orig_size; j++) {
        simplify_target_monomials_sum_j(source, target, targ_sum, high_mon, j, true);
    }

    TRACE("grobner_d", tout << "targ_sum = " << targ_sum << "\n";);    
    target.m_expr = m_nex_creator.simplify(&targ_sum);
    target.m_dep = m_dep_manager.mk_join(source.dep(), target.dep());
    TRACE("grobner_d", tout << "target = "; display_equation(tout, target););

    return true;
}

bool grobner_core::divide_ignore_coeffs_check_only_nex_mul(nex_mul const& t, const nex& h) const {
    TRACE("grobner_d", tout << "t = " << t << ", h=" << h << "\n";);  
    SASSERT(m_nex_creator.is_simplified(t) && m_nex_creator.is_simplified(h));
    unsigned j = 0; // points to t
    for(unsigned k = 0; k < h.number_of_child_powers(); k++) {
        lpvar h_var = h.get_child_exp(k)->to_var().var();
        bool p_swallowed = false;
        for (; j < t.size() && !p_swallowed; j++) {
            const nex_pow& tp = t[j];
            if (tp.e()->to_var().var() == h_var) {
                if (tp.pow() >= h.get_child_pow(k)) {
                    p_swallowed = true;
                }
            }
        }
        if (!p_swallowed) {
            TRACE("grobner_d", tout << "no div " << t << " / " << h << "\n";);
            return false;
        }
    }
    TRACE("grobner_d", tout << "division " << t << " / " << h << "\n";);
    return true;   
}

// return true if h divides n
bool grobner_core::divide_ignore_coeffs_check_only(nex const& n , const nex& h) const {
    if (n.is_mul())
        return divide_ignore_coeffs_check_only_nex_mul(n.to_mul(), h);
    if (!n.is_var())
        return false;

    const nex_var& v = n.to_var();
    if (h.is_var()) {
        return v.var() == h.to_var().var();
    }

    if (h.is_mul()) {
        if (h.number_of_child_powers() > 1)
            return false;
        if (h.get_child_pow(0) != 1)
            return false;
        const nex* e = h.get_child_exp(0);
        return e->is_var() && e->to_var().var() == v.var();        
    }
        
    return false;        
}

nex_mul * grobner_core::divide_ignore_coeffs_perform_nex_mul(nex_mul const& t, const nex& h) {

    m_nex_creator.m_mk_mul.reset();

    unsigned j = 0; // j points to t and k runs over h
    for(unsigned k = 0; k < h.number_of_child_powers(); k++) {
        lpvar h_var = to_var(h.get_child_exp(k))->var();
        for (; j < t.size(); j++) {
            auto const &tp = t[j];
            if (tp.e()->to_var().var() == h_var) {
                unsigned h_pow = h.get_child_pow(k);
                SASSERT(tp.pow() >= h_pow);
                j++;
                if (tp.pow() > h_pow) {
                    m_nex_creator.m_mk_mul *= nex_pow(tp.e(), tp.pow() - h_pow);
                }
                break;
            } else {
                m_nex_creator.m_mk_mul *= tp;
            }
        }
    }
    for (; j < t.size(); j++) {
        m_nex_creator.m_mk_mul *= t[j];
    }

    nex_mul* r = m_nex_creator.m_mk_mul.mk();
    TRACE("grobner", tout << "r = " << *r << " = " << t << " / " << h << "\n";);    
    TRACE("grobner_d", tout << "r = " << *r << " = " << t << " / " << h << "\n";);
    return r;
}

// perform the division t / h, but ignores the coefficients
// h does not change
nex_mul * grobner_core::divide_ignore_coeffs_perform(nex* e, const nex& h) {
    if (e->is_mul())
        return divide_ignore_coeffs_perform_nex_mul(e->to_mul(), h);
    SASSERT(e->is_var());
    return m_nex_creator.mk_mul(); // return the empty nex_mul
}

// if targ_sum->children()[j] = c*high_mon*p,
// and  b*high_mon + e = 0, so high_mon = -e/b
// then targ_sum->children()[j] =  - (c/b) * e*p


void grobner_core::simplify_target_monomials_sum_j(equation const& source, equation& target, nex_sum& targ_sum, const nex& high_mon, unsigned j, bool test_divisibility) { 
    nex * ej = targ_sum[j];
    TRACE("grobner_d", tout << "high_mon = " << high_mon << ", ej = " << *ej << "\n";);
    if (test_divisibility && !divide_ignore_coeffs_check_only(*ej, high_mon)) {
        TRACE("grobner_d", tout << "no div\n";);
        return;
    }
    nex_mul * ej_over_high_mon = divide_ignore_coeffs_perform(ej, high_mon);
    TRACE("grobner_d", tout << "ej_over_high_mon = " << *ej_over_high_mon << "\n";);
    rational c = ej->is_mul() ? to_mul(ej)->coeff() : rational(1);
    TRACE("grobner_d", tout << "c = " << c << "\n";);

    nex_creator::sum_factory sf(m_nex_creator);
    add_mul_skip_first(sf ,-c/high_mon.coeff(), source.expr(), ej_over_high_mon);

    targ_sum[j] = sf.mk();
    TRACE("grobner_d", tout << "targ_sum = " << targ_sum << "\n";);    
}

// return true iff simplified

bool grobner_core::simplify_source_target(equation const& source, equation& target) {
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, target); tout << "\nusing: "; display_equation(tout, source););
    TRACE("grobner_d", tout << "simplifying: " << *(target.expr()) <<  " using " << *(source.expr()) << "\n";);
    SASSERT(m_nex_creator.is_simplified(*source.expr()));
    SASSERT(m_nex_creator.is_simplified(*target.expr()));
    if (target.expr()->is_scalar()) {
        TRACE("grobner_d", tout << "no simplification\n";);
        return false;
    }
    if (source.get_num_monomials() == 0) {
        TRACE("grobner_d", tout << "no simplification\n";);
        return false;
    }
    m_stats.m_simplified++;
    bool result = false;
    while (!canceled() && simplify_target_monomials(source, target)) {
        TRACE("grobner", tout << "simplified target = "; display_equation(tout, target) << "\n";);
        result = true;
    } 
    if (result) {
        target.m_dep = m_dep_manager.mk_join(target.dep(), source.dep());
        update_stats_max_degree_and_size(&target);
        TRACE("grobner", tout << "simplified "; display_equation(tout, target) << "\n";);
        TRACE("grobner_d", tout << "simplified to " << *(target.expr()) << "\n";);
        return true;
    }
    TRACE("grobner_d", tout << "no simplification\n";);
    return false;
}

void grobner_core::process_simplified_target(equation* target, ptr_buffer<equation>& to_remove) {
    if (is_trivial(target)) {
        to_remove.push_back(target);
    } else if (m_changed_leading_term) {
        insert_to_simplify(target);
        to_remove.push_back(target);
    }
}


bool grobner_core::simplify_to_superpose_with_eq(equation* eq) {
    TRACE("grobner_d", tout << "eq->exp " << *(eq->expr()) <<  "\n";);

    ptr_buffer<equation> to_insert;
    ptr_buffer<equation> to_remove;
    ptr_buffer<equation> to_delete;
    for (equation * target : m_to_superpose) {
        if (canceled() || done())
            break;
        m_changed_leading_term = false;
        // if the leading term is simplified, then the equation has to be moved to m_to_simplify
        if (simplify_source_target(*eq, *target)) {
            process_simplified_target(target, to_remove);
        }
        if (is_trivial(target)) {
            to_delete.push_back(target);
        }
        else {
            SASSERT(m_nex_creator.is_simplified(*target->expr()));
        }
    }
    for (equation* eq : to_insert) 
        insert_to_superpose(eq);
    for (equation* eq : to_remove)
        m_to_superpose.erase(eq);
    for (equation* eq : to_delete) 
        del_equation(eq);
    return !canceled();
}

/*
    Use the given equation to simplify m_to_simplify equations
*/
void  grobner_core::simplify_m_to_simplify(equation* eq) {
    TRACE("grobner_d", tout << "eq->exp " << *(eq->expr()) <<  "\n";);
    ptr_buffer<equation> to_delete;
    for (equation* target : m_to_simplify) {
        if (simplify_source_target(*eq, *target) && is_trivial(target))
            to_delete.push_back(target);
    }
    for (equation* eq : to_delete)
        del_equation(eq);
}

// if e is the sum then add to r all children of e multiplied by beta, except the first one
// which corresponds to the highest monomial,
// otherwise do nothing
void grobner_core::add_mul_skip_first(nex_creator::sum_factory& sf, const rational& beta, nex const*e, nex_mul* c) {
    if (e->is_sum()) {
        nex_sum const & es = e->to_sum();
        for (unsigned j = 1; j < es.size(); j++) {
            sf += m_nex_creator.mk_mul(beta, es[j], c);
        }
    } else {
        TRACE("grobner_d", tout << "e = " << *e << "\n";);
    }
}

// let e1: alpha*ab+q=0, and e2: beta*ac+e=0, then beta*qc - alpha*eb = 0
nex * grobner_core::expr_superpose(nex const* e1, nex const* e2, const nex* ab, const nex* ac, nex_mul* b, nex_mul* c) {
    TRACE("grobner", tout << "e1 = " << *e1 << "\ne2 = " << *e2 <<"\n";);    
    nex_creator::sum_factory sf(m_nex_creator);
    rational alpha = - ab->coeff();
    TRACE("grobner", tout << "e2 *= " << alpha << "*(" <<  *b << ")\n";);
    add_mul_skip_first(sf, alpha, e2, b);
    rational beta = ac->coeff();
    TRACE("grobner", tout << "e1 *= " << beta << "*(" <<  *c << ")\n";);
    add_mul_skip_first(sf, beta, e1, c);
    nex * ret = m_nex_creator.simplify(sf.mk());
    TRACE("grobner", tout << "e1 = " << *e1 << "\ne2 = " << *e2 <<"\nsuperpose = " << *ret << "\n";);
    CTRACE("grobner", ret->is_scalar(), tout << "\n";);
    return ret;
}

// let eq1: ab+q=0, and eq2: ac+e=0, then qc - eb = 0
void grobner_core::superpose(equation * eq1, equation * eq2) {
    TRACE("grobner_d", tout << "eq1="; display_equation(tout, *eq1) << "eq2="; display_equation(tout, *eq2););
    const nex * ab = get_highest_monomial(eq1->expr()); 
    const nex * ac = get_highest_monomial(eq2->expr());
    nex_mul *b = nullptr, *c = nullptr;
    TRACE("grobner_d", tout << "ab="; if(ab) { tout << *ab; } else { tout << "null"; };
          tout  << " , " << " ac="; if(ac) { tout << *ac; } else { tout << "null"; }; tout << "\n";);
    if (!find_b_c(ab, ac, b, c)) {
        TRACE("grobner_d", tout << "there is no non-trivial common divider, no superposing\n";);
        return;
    }
    equation* eq = alloc(equation);
    TRACE("grobner_d", tout << "eq1="; display_equation(tout, *eq1) << "eq2="; display_equation(tout, *eq2););
    init_equation(eq, expr_superpose(eq1->expr(), eq2->expr(), ab, ac, b, c), m_dep_manager.mk_join(eq1->dep(), eq2->dep()));
    if (m_nex_creator.gt(eq->expr(), eq1->expr()) || m_nex_creator.gt(eq->expr(), eq2->expr()) ||
        eq->expr()->size() > m_superposed_exp_size_limit) {
        TRACE("grobner", display_equation(tout, *eq) << " is too complex: deleting it\n;";);
        del_equation(eq);
    } else {
        m_stats.m_superposed++;
        update_stats_max_degree_and_size(eq);
        insert_to_simplify(eq);
    }
}



// Let a be the greatest common divider of ab and bc,
// then ab/a is stored in b, and ac/a is stored in c
bool grobner_core::find_b_c(const nex* ab, const nex* ac, nex_mul*& b, nex_mul*& c) {
    if (!find_b_c_check_only(ab, ac))
        return false;
    nex_creator::mul_factory fb(m_nex_creator), fc(m_nex_creator);
    unsigned ab_size = ab->number_of_child_powers();
    unsigned ac_size = ac->number_of_child_powers();
    unsigned i = 0, j = 0;
    for (;;) {
        const nex* m = ab->get_child_exp(i);
        const nex* n = ac->get_child_exp(j);
        if (m_nex_creator.gt(m, n)) {
            fb *= nex_pow(const_cast<nex*>(m), ab->get_child_pow(i));
            if (++i == ab_size)
                break;
        } else if (m_nex_creator.gt(n, m)) {
            fc *= nex_pow(const_cast<nex*>(n), ac->get_child_pow(j));
            if (++j == ac_size)
                break;
        } else {
            unsigned b_pow = ab->get_child_pow(i);
            unsigned c_pow = ac->get_child_pow(j);
            if (b_pow > c_pow) {
                fb *= nex_pow(const_cast<nex*>(m), b_pow - c_pow);
            } else if (c_pow > b_pow) {
                fc *= nex_pow(const_cast<nex*>(n), c_pow - b_pow);
            } // otherwise the power are equal and no child added to either b or c
            i++; j++;
           
            if (i == ab_size || j == ac_size) {
                break;
            }
        }
    }    
    while (i != ab_size) {
        fb *= nex_pow(const_cast<nex*>(ab->get_child_exp(i)), ab->get_child_pow(i));
        i++;
    }
    while (j != ac_size) {
        fc *= nex_pow(const_cast<nex*>(ac->get_child_exp(j)), ac->get_child_pow(j));
        j++;
    }
    b = fb.mk();
    c = fc.mk();
    TRACE("nla_grobner", tout << "b=" << *b << ", c=" <<*c << "\n";);
    // debug region
    nex_mul *a = divide_ignore_coeffs_perform(m_nex_creator.clone(ab), *b);
    SASSERT(ab->get_degree() == a->get_degree() + b->get_degree());
    SASSERT(ac->get_degree() == a->get_degree() + c->get_degree());
    SASSERT(test_find_b_c(ab, ac, b, c));
    return true;
}

// Finds out if ab and bc have a non-trivial common divider
bool grobner_core::find_b_c_check_only(const nex* ab, const nex* ac) const {
    if (ab == nullptr || ac == nullptr)
        return false;
    SASSERT(m_nex_creator.is_simplified(*ab) && m_nex_creator.is_simplified(*ac));
    unsigned i = 0, j = 0; // i points to ab, j points to ac
    for (;;) {
        const nex* m = ab->get_child_exp(i);
        const nex* n = ac->get_child_exp(j);
        if (m_nex_creator.gt(m , n)) {
            i++;
            if (i == ab->number_of_child_powers())
                return false;
        } else if (m_nex_creator.gt(n, m)) {
            j++;
            if (j == ac->number_of_child_powers())
                return false;
        } else {
            TRACE("grobner", tout << "found common " << *m << "\n";);
            return true;
        }
    }

    TRACE("grobner", tout << "not found common " << " in " << *ab << " and " << *ac << "\n";);
    return false;
}

void grobner_core::superpose(equation * eq) {
    for (equation * target : m_to_superpose) {
        superpose(eq, target);
    }
}

bool grobner_core::canceled() {
    return m_limit.get_cancel_flag();
}

bool grobner_core::done() {
    return num_of_equations() >= m_grobner_eqs_threshold || canceled();    
}

void grobner_core::del_equations(unsigned old_size) {
    TRACE("grobner", );
    SASSERT(m_equations_to_delete.size() >= old_size);
    for (unsigned i = m_equations_to_delete.size(); i-- > old_size; ) {
        equation* eq = m_equations_to_delete[i];
        if (eq)
            del_equation(eq);
    }
    m_equations_to_delete.shrink(old_size);    
}

std::ostream& grobner_core::print_stats(std::ostream & out) const {
    return out << "stats:\nsteps = " << m_stats.m_compute_steps << "\nsimplified: " <<
        m_stats.m_simplified << "\nsuperposed: " <<
        m_stats.m_superposed << "\nexpr degree: " << m_stats.m_max_expr_degree <<
        "\nexpr size: " << m_stats.m_max_expr_size << "\n";
}

void grobner_core::update_stats_max_degree_and_size(const equation *e) {
    if (m_stats.m_max_expr_size < e->expr()->size()) {
        TRACE("grobner_stats_d", tout << "expr size = " << e->expr()->size() << "\n";);
        TRACE("grobner_stats_d", display_equation(tout, *e););
        
        m_stats.m_max_expr_size = e->expr()->size();
    }
    auto deg = e->expr()->get_degree();
    if (m_stats.m_max_expr_degree < deg) {
        TRACE("grobner_stats_d", tout << "expr degree = " << deg << "\n";);
        m_stats.m_max_expr_degree = deg;
    }
}

void grobner_core::display_equations(std::ostream & out, equation_set const & v, char const * header) const {
    out << header << "\n";
    for (const equation* e : v) 
        display_equation(out, *e);
}

std::ostream& grobner_core::display_equation(std::ostream & out, const equation & eq) const {
    out << "expr = " << *eq.expr() << "\n";
    return display_dependency(out, eq.dep());
}

std::ostream& grobner_core::display(std::ostream& out) const {
    display_equations(out, m_to_superpose, "m_to_superpose:");
    display_equations(out, m_to_simplify, "m_to_simplify:");
    return out;
}

void grobner_core::assert_eq_0(nex* e, common::ci_dependency * dep) {
    if (e == nullptr || is_zero_scalar(e))
        return;
    equation * eq = alloc(equation);
    init_equation(eq, e, dep);
    TRACE("grobner",
          display_equation(tout, *eq);
          /*tout << "\nvars\n";          
          for (unsigned j : get_vars_of_expr_with_opening_terms(e)) {
              c().print_var(j, tout << "(") << ")\n";
          } */);
    insert_to_simplify(eq);
    update_stats_max_degree_and_size(eq);
}

void grobner_core::init_equation(equation* eq, nex*e, common::ci_dependency * dep) {
    eq->m_bidx      = m_equations_to_delete.size();
    eq->m_dep       = dep;
    eq->m_expr      = e;
    m_equations_to_delete.push_back(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
}

grobner_core::~grobner_core() {
    del_equations(0);
}

std::ostream& grobner_core::display_dependency(std::ostream& out, common::ci_dependency* dep) const {
    svector<lp::constraint_index> expl;
    m_dep_manager.linearize(dep, expl);       
    lp::explanation e(expl);
    if (!expl.empty()) {
        out << "constraints\n";    
        m_print_explanation(e, out);
        out << "\n";
    }  else {
        out << "no deps\n";
    }    
    return out;
}

#ifdef Z3DEBUG
bool grobner_core::test_find_b(const nex* ab, const nex_mul* b) {
    nex_mul& ab_clone = m_nex_creator.clone(ab)->to_mul();
    nex_mul * a= divide_ignore_coeffs_perform(&ab_clone, *b);
    ab_clone.m_coeff = rational(1);
    SASSERT(b->coeff().is_one());
    nex * m = m_nex_creator.mk_mul(a, m_nex_creator.clone(b));
    m = m_nex_creator.simplify(m);
    return m_nex_creator.equal(m, &ab_clone);
}

bool grobner_core::test_find_b_c(const nex* ab, const nex* ac, const nex_mul* b, const nex_mul* c) {
    return test_find_b(ab, b) && test_find_b(ac, c);    
}

#endif
