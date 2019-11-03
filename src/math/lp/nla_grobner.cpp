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
namespace nla {
nla_grobner::nla_grobner(core *c, intervals *s)
    : common(c, s),
      m_nl_gb_exhausted(false),
      m_dep_manager(m_val_manager, m_alloc),
      m_changed_leading_term(false) {}

bool nla_grobner::internalize_gb_eq(equation* ) {
    NOT_IMPLEMENTED_YET();
    return false;
}

void nla_grobner::add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, std::queue<lpvar> & q) {
    SASSERT(!c().active_var_set_contains(j));
    const auto& matrix = c().m_lar_solver.A_r();
    c().insert_to_active_var_set(j);
    for (auto & s : matrix.m_columns[j]) {
        unsigned row = s.var();
        if (m_rows.contains(row)) continue;
        m_rows.insert(row);
        for (auto& rc : matrix.m_rows[row]) {
            if (c().active_var_set_contains(rc.var()))
                continue;
            q.push(rc.var());
        }
    }

    if (!c().is_monic_var(j))
        return;

    const monic& m = c().emons()[j];
    for (auto fcn : factorization_factory_imp(m, c())) {
        for (const factor& fc: fcn) {
            lpvar j = var(fc);
            if (! c().active_var_set_contains(j))
                add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
        }
    }            
}

void nla_grobner::find_nl_cluster() {
    prepare_rows_and_active_vars();
    std::queue<lpvar> q;
    for (lpvar j : c().m_to_refine) {        
        TRACE("grobner", c().print_monic(c().emons()[j], tout) << "\n";);
        q.push(j);
    }

    while (!q.empty()) {
        unsigned j = q.front();        
        q.pop();
        if (c().active_var_set_contains(j))
            continue;
        add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
    }
    set_active_vars_weights();
    TRACE("grobner", display(tout););
}

void nla_grobner::prepare_rows_and_active_vars() {
    m_rows.clear();
    m_rows.resize(c().m_lar_solver.row_count());
    c().clear_and_resize_active_var_set();
}

void nla_grobner::display_matrix(std::ostream & out) const {
    const auto& matrix = c().m_lar_solver.A_r();
    out << m_rows.size() << " rows" <<"\n";
    out << "the matrix\n";
          
    for (const auto & r : matrix.m_rows) {
        c().print_term(r, out) << std::endl;
    }
}
std::ostream & nla_grobner::display(std::ostream & out) const {
    display_equations(out, m_to_superpose, "m_to_superpose:");
    display_equations(out, m_to_simplify, "m_to_simplify:");
    return out;
}

void nla_grobner::process_var(nex_mul* m, lpvar j, ci_dependency* & dep, rational & coeff) {
    if (c().var_is_fixed(j)) {                                       
        if (!m_tmp_var_set.contains(j)) {
            m_tmp_var_set.insert(j);
            lp::constraint_index lc,uc;
            c().m_lar_solver.get_bound_constraint_witnesses_for_column(j, lc, uc);
            dep = m_dep_manager.mk_join(dep, m_dep_manager.mk_join(m_dep_manager.mk_leaf(lc), m_dep_manager.mk_leaf(uc))); 
        }
        coeff *= c().m_lar_solver.column_upper_bound(j).x; 
    }                                                           
    else {                                                      
        m->add_child(m_nex_creator.mk_var(j));                                    
    }                                                           
}                                                               


common::ci_dependency* nla_grobner::dep_from_vector(svector<lp::constraint_index> & cs) {
    ci_dependency * d = nullptr;
    for (auto c : cs)
        d = m_dep_manager.mk_join(d, m_dep_manager.mk_leaf(c));
    return d;
}

void nla_grobner::add_row(unsigned i) {    
    const auto& row = c().m_lar_solver.A_r().m_rows[i];    
    TRACE("grobner", tout << "adding row to gb\n"; c().m_lar_solver.print_row(row, tout) << '\n';
          for (auto p : row) {
              c().print_var(p.var(), tout) << "\n";
          }
          );
    nex_sum * ns = m_nex_creator.mk_sum();
    

    svector<lp::constraint_index> fixed_vars_constraints;
    create_sum_from_row(row, m_nex_creator, *ns, true); // true to treat fixed vars as scalars
    nex* e = m_nex_creator.simplify(ns);
    TRACE("grobner", tout << "e = " << *e << "\n";);
    m_tmp_var_set.clear();    
    assert_eq_0(e, get_fixed_vars_dep_from_row(row, m_dep_manager));
}

void nla_grobner::simplify_equations_to_process() {
    for (equation *eq : m_to_simplify) {
        eq->exp() = m_nex_creator.simplify(eq->exp());
    }
}

void nla_grobner::init() {
    m_reported = 0;
    m_conflict = false;
    m_equations_to_unfreeze.clear();
    del_equations(0);
    SASSERT(m_equations_to_delete.size() == 0);    
    m_num_of_equations = 0;
    m_to_superpose.reset();
    m_to_simplify.reset();

    find_nl_cluster();
    c().clear_and_resize_active_var_set();
    for (unsigned i : m_rows) {
        add_row(i);
    }
    simplify_equations_to_process();
}

bool nla_grobner::is_trivial(equation* eq) const {
    SASSERT(m_nex_creator.is_simplified(eq->exp()));
    return eq->exp()->size() == 0;
}

bool nla_grobner::is_better_choice(equation * eq1, equation * eq2) {
    if (!eq2)
        return true;
    if (is_trivial(eq1))
        return true;
    if (is_trivial(eq2))
        return false;
    return m_nex_creator.lt(eq1->exp(), eq2->exp());
}

void nla_grobner::del_equation(equation * eq) {
    m_to_superpose.erase(eq);
    m_to_simplify.erase(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
    m_equations_to_delete[eq->m_bidx] = 0;
    dealloc(eq);
}

nla_grobner::equation* nla_grobner::pick_next() {
    equation * r = nullptr;
    ptr_buffer<equation> to_delete;
    for (equation * curr : m_to_simplify) {
        if (is_trivial(curr))
            to_delete.push_back(curr);
        else if (is_better_choice(curr, r))
            r = curr;
    }
    for (equation * e : to_delete) 
        del_equation(e);
    if (r)
        m_to_simplify.erase(r);
    TRACE("grobner", tout << "selected equation: "; if (!r) tout << "<null>\n"; else display_equation(tout, *r););
    return r;
}

nla_grobner::equation* nla_grobner::simplify_using_processed(equation* eq) {
    bool result = false;
    bool simplified;
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *eq); tout << "using already processed equalities of size " << m_to_superpose.size() << "\n";);
    do {
        simplified = false;
        for (equation * p : m_to_superpose) {
            equation * new_eq  = simplify_source_target(p, eq);           
            if (new_eq) {
                result     = true;
                simplified = true;
                eq         = new_eq;
            }            
            if (canceled()) {
                return nullptr;
            }
            if (eq->exp()->is_scalar())
                break;                
        }
        if (eq->exp()->is_scalar())
            break;
    }
    while (simplified);
    if (result && eq->exp()->is_scalar()) {
        TRACE("grobner",);
    }

    TRACE("grobner", tout << "simplification result: "; display_equation(tout, *eq););
    return result ? eq : nullptr;

}

const nex* nla_grobner::get_highest_monomial(const nex* e) const {
    switch (e->type()) {
    case expr_type::MUL:
        return to_mul(e);
    case expr_type::SUM:
        return *(to_sum(e)->begin());
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
bool nla_grobner::simplify_target_monomials(equation * source, equation * target) {
    auto * high_mon = get_highest_monomial(source->exp());
    if (high_mon == nullptr)
        return false;
    SASSERT(high_mon->all_factors_are_elementary());
    TRACE("grobner", tout << "source = "; display_equation(tout, *source) << "target = "; display_equation(tout, *target) << "high_mon = " << *high_mon << "\n";);

    nex * te = target->exp();    
    nex_sum * targ_sum;
    if (te->is_sum()) {
        targ_sum = to_sum(te);
    } else if (te->is_mul()) {
        targ_sum = m_nex_creator.mk_sum(te);
    } else {
        TRACE("grobner", tout << "return false\n";);
        return false;
    }

    return simplify_target_monomials_sum(source, target, targ_sum, high_mon);   
}

unsigned nla_grobner::find_divisible(nex_sum* targ_sum,
                                                           const nex* high_mon) const {
    for (unsigned j = 0; j < targ_sum->size(); j++) {
        auto t = (*targ_sum)[j];
        if (divide_ignore_coeffs_check_only(t, high_mon)) {
            TRACE("grobner", tout << "yes div: " << *targ_sum << " / " << *high_mon << "\n";);
            return j;
        }
    }
    TRACE("grobner", tout << "no div: " << *targ_sum << " / " << *high_mon << "\n";);
    return -1;
}


bool nla_grobner::simplify_target_monomials_sum(equation * source,
                                                equation * target, nex_sum* targ_sum,
                                                const nex* high_mon) {
    unsigned j = find_divisible(targ_sum, high_mon);
    if (j + 1 == 0)
        return false;
    m_changed_leading_term = (j == 0);
    unsigned targ_orig_size = targ_sum->size();
    for (; j < targ_orig_size; j++) {
        simplify_target_monomials_sum_j(source, target, targ_sum, high_mon, j);
    }
    TRACE("grobner_d", tout << "targ_sum = " << *targ_sum << "\n";);    
    target->exp() = m_nex_creator.simplify(targ_sum);
    target->dep() = m_dep_manager.mk_join(source->dep(), target->dep());
    TRACE("grobner_d", tout << "target = "; display_equation(tout, *target););
    return true;
}

nex_mul* nla_grobner::divide_ignore_coeffs(nex* ej, const nex* h) {
    TRACE("grobner", tout << "ej = " << *ej << " , h = " << *h << "\n";);
    if (!divide_ignore_coeffs_check_only(ej, h))
        return nullptr;
    return divide_ignore_coeffs_perform(ej, h);
}

bool nla_grobner::divide_ignore_coeffs_check_only_nex_mul(nex_mul* t , const nex* h) const {
    TRACE("grobner", tout << "t = " << *t << ", h=" << *h << "\n";);  
    SASSERT(m_nex_creator.is_simplified(t) && m_nex_creator.is_simplified(h));
    unsigned j = 0; // points to t
    for(unsigned k = 0; k < h->number_of_child_powers(); k++) {
        lpvar h_var = to_var(h->get_child_exp(k))->var();
        bool p_swallowed = false;
        for (; j < t->size() && !p_swallowed; j++) {
            auto &tp = (*t)[j];
            if (to_var(tp.e())->var() == h_var) {
                if (tp.pow() >= static_cast<int>(h->get_child_pow(k))) {
                    p_swallowed = true;
                }
            }
        }
        if (!p_swallowed) {
            TRACE("grobner", tout << "no div " << *t << " / " << *h << "\n";);
            return false;
        }
    }
    TRACE("grobner", tout << "division " << *t << " / " << *h << "\n";);
    return true;
    
}

// return true if h divides t
bool nla_grobner::divide_ignore_coeffs_check_only(nex* n , const nex* h) const {
    if (n->is_mul())
        return divide_ignore_coeffs_check_only_nex_mul(to_mul(n), h);
    if (!n->is_var())
        return false;

    const nex_var * v = to_var(n);
    if (h->is_var()) {
        return v->var() == to_var(h)->var();
    }

    if (h->is_mul() || h->is_var()) {
        if (h->number_of_child_powers() > 1)
            return false;
        if (h->get_child_pow(0) != 1)
            return false;
        const nex* e = h->get_child_exp(0);
        return e->is_var() && to_var(e)->var() == v->var();        
    }
        
    return false;        
}

nex_mul * nla_grobner::divide_ignore_coeffs_perform_nex_mul(nex_mul* t, const nex* h) {
    nex_mul * r = m_nex_creator.mk_mul();
    unsigned j = 0; // points to t
    for(unsigned k = 0; k < h->number_of_child_powers(); k++) {
        lpvar h_var = to_var(h->get_child_exp(k))->var();
        for (; j < t->size(); j++) {
            auto &tp = (*t)[j];
            if (to_var(tp.e())->var() == h_var) {
                int h_pow = h->get_child_pow(k);
                SASSERT(tp.pow() >= h_pow);
                j++;
                if (tp.pow() > h_pow)
                    r->add_child_in_power(tp.e(), tp.pow() - h_pow);
                break;
            } else {
                r->add_child_in_power(tp);
            }
        }
    }
    TRACE("grobner", tout << "r = " << *r << " = " << *t << " / " << *h << "\n";);
    return r;
}

// perform the division t / h, but ignores the coefficients
// h does not change
nex_mul * nla_grobner::divide_ignore_coeffs_perform(nex* e, const nex* h) {
    if (e->is_mul())
        return divide_ignore_coeffs_perform_nex_mul(to_mul(e), h);
    SASSERT(e->is_var());
    return m_nex_creator.mk_mul(); // return the empty nex_mul
}

// if targ_sum->children()[j] = c*high_mon*p,
// and  b*high_mon + e = 0, so high_mon = -e/b
// then targ_sum->children()[j] =  - (c/b) * e*p

void nla_grobner::simplify_target_monomials_sum_j(equation * source, equation *target, nex_sum* targ_sum, const nex* high_mon, unsigned j) {    
    nex * ej = (*targ_sum)[j];
    TRACE("grobner_d", tout << "high_mon = " << *high_mon << ", ej = " << *ej << "\n";);
    nex_mul * ej_over_high_mon = divide_ignore_coeffs(ej, high_mon);
    if (ej_over_high_mon == nullptr) {
        TRACE("grobner_d", tout << "no div\n";);
        return;
    }
    TRACE("grobner_d", tout << "ej_over_high_mon = " << *ej_over_high_mon << "\n";);
    rational c = ej->is_mul()? to_mul(ej)->coeff() : rational(1);
    TRACE("grobner_d", tout << "c = " << c << "\n";);
    
    nex_sum * ej_sum = m_nex_creator.mk_sum();
    (*targ_sum)[j] = ej_sum;
    add_mul_skip_first(ej_sum ,-c/high_mon->coeff(), source->exp(), ej_over_high_mon);
    TRACE("grobner_d", tout << "targ_sum = " << *targ_sum << "\n";);    
}


nla_grobner::equation * nla_grobner::simplify_source_target(equation * source, equation * target) {
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *target); tout << "using: "; display_equation(tout, *source););
    TRACE("grobner_d", tout << "simplifying: " << *(target->exp()) <<  " using " << *(source->exp()) << "\n";);
    SASSERT(m_nex_creator.is_simplified(source->exp()));
    SASSERT(m_nex_creator.is_simplified(target->exp()));
    if (target->exp()->is_scalar()) {
        TRACE("grobner_d", tout << "no simplification\n";);
        return nullptr;
    }
    if (source->get_num_monomials() == 0) {
        TRACE("grobner_d", tout << "no simplification\n";);
        return nullptr;
    }
    m_stats.m_simplify++;
    bool result = false;
    do {
        if (simplify_target_monomials(source, target)) {
            TRACE("grobner", tout << "simplified target = ";display_equation(tout, *target) << "\n";);
            result = true;
        } else {
            break;
        }
    } while (!canceled());
    TRACE("grobner", tout << "result: " << result << "\n"; if (result) display_equation(tout, *target););
    if (result) {
        target->dep() = m_dep_manager.mk_join(target->dep(), source->dep());
        TRACE("grobner_d", tout << "simplied to " << *(target->exp()) << "\n";);
        return target;
    }
    TRACE("grobner_d", tout << "no simplification\n";);
    return nullptr;
}
 
void nla_grobner::process_simplified_target(ptr_buffer<equation>& to_insert, equation* new_target, equation*& target, ptr_buffer<equation>& to_remove) {
    if (new_target != target) {
        m_equations_to_unfreeze.push_back(target);
        to_remove.push_back(target);
        if (m_changed_leading_term) {
            insert_to_simplify(new_target);
            to_remove.push_back(target);
        }
        else {
            to_insert.push_back(new_target);
        }
        target = new_target;
    }
    else {
        if (m_changed_leading_term) {
            insert_to_simplify(target);
            to_remove.push_back(target);
        }
    }
    if(m_intervals->check_cross_nested_expr(target->exp(), target->dep())) {
        TRACE("grobner", tout << "created a lemma for "; display_equation(tout, *target) << "\n";
              tout << "vars = \n";
              for (lpvar j : get_vars_of_expr(target->exp())) {
                  c().print_var(j, tout);
              }
              tout << "\ntarget->exp() val = " << get_nex_val(target->exp(), [this](unsigned j) { return c().val(j); }) << "\n";);
        register_report();       
    }
}

bool nla_grobner::simplify_to_superpose_with_eq(equation* eq) {
    TRACE("grobner_d", tout << "eq->exp " << *(eq->exp()) <<  "\n";);

    ptr_buffer<equation> to_insert;
    ptr_buffer<equation> to_remove;
    ptr_buffer<equation> to_delete;
    equation_set::iterator it  = m_to_superpose.begin();
    equation_set::iterator end = m_to_superpose.end();
    for (; it != end && !canceled() && !done(); ++it) {
        equation * target        = *it;
        m_changed_leading_term = false;
        // if the leading term is simplified, then the equation has to be moved to m_to_simplify
        equation * new_target    = simplify_source_target(eq, target);
        if (new_target != nullptr) {
            process_simplified_target(to_insert, new_target, target, to_remove);
        }
        if (is_trivial(target))
            to_delete.push_back(target);
        else 
            SASSERT(m_nex_creator.is_simplified(target->exp()));
    }
    for (equation* eq : to_insert) 
        insert_to_superpose(eq);
    for (equation* eq : to_remove)
        m_to_superpose.erase(eq);
    for (equation* eq : to_delete) 
        del_equation(eq);
    return !canceled();
}

void  nla_grobner::simplify_to_superpose(equation* eq) {
    TRACE("grobner_d", tout << "eq->exp " << *(eq->exp()) <<  "\n";);
    ptr_buffer<equation> to_insert;
    ptr_buffer<equation> to_remove;
    ptr_buffer<equation> to_delete;
    for (equation* target : m_to_simplify) {
        equation * new_target = simplify_source_target(eq, target);
        if (new_target != nullptr && new_target != target) {
            m_equations_to_unfreeze.push_back(target);
            to_insert.push_back(new_target);
            to_remove.push_back(target);
            target = new_target;
        }
        if (is_trivial(target))
            to_delete.push_back(target);
    }
    for (equation* eq : to_insert)
        insert_to_simplify(eq);
    for (equation* eq : to_remove)
        m_to_simplify.erase(eq);
    for (equation* eq : to_delete)
        del_equation(eq);

}

// if e is the sum then add to r all children of e multiplied by beta, except the first one
// which corresponds to the highest monomial,
// otherwise do nothing
void nla_grobner::add_mul_skip_first(nex_sum* r, const rational& beta, nex *e, nex_mul* c) {
    if (e->is_sum()) {
        nex_sum *es = to_sum(e);
        for (unsigned j = 1; j < es->size(); j++) {
            r->add_child(m_nex_creator.mk_mul(beta, (*es)[j], c));
        }
        TRACE("grobner", tout << "r = " << *r << "\n";);        
    } else {
        TRACE("grobner", tout << "e = " << *e << "\n";);
    }
}


// let e1: alpha*ab+q=0, and e2: beta*ac+e=0, then beta*qc - alpha*eb = 0
nex * nla_grobner::expr_superpose(nex* e1, nex* e2, const nex* ab, const nex* ac, nex_mul* b, nex_mul* c) {
    TRACE("grobner", tout << "e1 = " << *e1 << "\ne2 = " << *e2 <<"\n";);    
    nex_sum * r = m_nex_creator.mk_sum();
    rational alpha = - ab->coeff();
    TRACE("grobner", tout << "e2 *= " << alpha << "*(" <<  *b << ")\n";);
    add_mul_skip_first(r, alpha, e2, b);
    rational beta = ac->coeff();
    TRACE("grobner", tout << "e1 *= " << beta << "*(" <<  *c << ")\n";);
    add_mul_skip_first(r, beta, e1, c);
    nex * ret = m_nex_creator.simplify(r);
    TRACE("grobner", tout << "e1 = " << *e1 << "\ne2 = " << *e2 <<"\nsuperpose = " << *ret << "\n";);
    if (ret->is_scalar()) {
        TRACE("grobner",);
    }
    return ret;
}
// let eq1: ab+q=0, and eq2: ac+e=0, then qc - eb = 0
void nla_grobner::superpose(equation * eq1, equation * eq2) {
    TRACE("grobner", tout << "eq1="; display_equation(tout, *eq1) << "eq2="; display_equation(tout, *eq2););
    const nex * ab = get_highest_monomial(eq1->exp()); 
    const nex * ac = get_highest_monomial(eq2->exp());
    nex_mul *b, *c;
    TRACE("grobner", tout << "ab="; if(ab) { tout << *ab; } else { tout << "null"; };
          tout  << " , " << " ac="; if(ac) { tout << *ac; } else { tout << "null"; }; tout << "\n";);
    if (!find_b_c(ab, ac, b, c)) {
        return;
    }
    equation* eq = alloc(equation);
    init_equation(eq, expr_superpose( eq1->exp(), eq2->exp(), ab, ac, b, c), m_dep_manager.mk_join(eq1->dep(), eq2->dep()));
    if(m_intervals->check_cross_nested_expr(eq->exp(), eq->dep())) {
        register_report();
    }
    insert_to_simplify(eq);
}

void nla_grobner::register_report() {
    m_reported++;
    if (c().current_lemma().expl().size() == 0)
        m_conflict = true;
}
// Let a be the greatest common divider of ab and bc,
// then ab/a is stored in b, and ac/a is stored in c
bool nla_grobner::find_b_c(const nex* ab, const nex* ac, nex_mul*& b, nex_mul*& c) {
    if (!find_b_c_check_only(ab, ac))
        return false;
    b = m_nex_creator.mk_mul(); c = m_nex_creator.mk_mul();
    unsigned ab_size = ab->number_of_child_powers();
    unsigned ac_size = ac->number_of_child_powers();
    unsigned i = 0, j = 0;
    //    nex_pow* bp = ab->begin();
    //    nex_pow* cp = ac->begin();
    for (;;) {
        const nex* m = ab->get_child_exp(i);
        const nex* n = ac->get_child_exp(j);
        if (m_nex_creator.lt(m, n)) {
            b->add_child_in_power(const_cast<nex*>(m), ab->get_child_pow(i));
            if (++i == ab_size)
                break;
        } else if (m_nex_creator.lt(n, m)) {
            c->add_child_in_power(const_cast<nex*>(n), ac->get_child_pow(j));
            if (++j == ac_size)
                break;
        } else {
            unsigned b_pow = ab->get_child_pow(i);
            unsigned c_pow = ac->get_child_pow(j);
            if (b_pow > c_pow) {
                b->add_child_in_power(const_cast<nex*>(m), b_pow - c_pow);
            } else if (c_pow > b_pow) {
                c->add_child_in_power(const_cast<nex*>(n), c_pow - b_pow);
            } // otherwise the power are equal and no child added to either b or c
            i++; j++;
           
            if (i == ab_size || j == ac_size) {
                break;
            }
        }
    }
    
    while (i != ab_size) {
        c->add_child_in_power(const_cast<nex*>(ab->get_child_exp(i)), ab->get_child_pow(i));
        i++;
    }
    while (j != ac_size) {
        c->add_child_in_power(const_cast<nex*>(ac->get_child_exp(j)), ac->get_child_pow(j));
        j++;
    }
    TRACE("nla_grobner", tout << "b=" << *b << ", c=" <<*c << "\n";);
    return true;
}
// Finds out if ab and bc have a non-trivial common divider
bool nla_grobner::find_b_c_check_only(const nex* ab, const nex* ac) const {
    if (ab == nullptr || ac == nullptr)
        return false;
    SASSERT(m_nex_creator.is_simplified(ab) && m_nex_creator.is_simplified(ab));
    unsigned i = 0, j = 0; // i points to ab, j points to ac
    for (;;) {
        const nex* m = ab->get_child_exp(i);
        const nex* n = ac->get_child_exp(j);
        if (m_nex_creator.lt(m , n)) {
            i++;
            if (i == ab->number_of_child_powers())
                return false;
        } else if (m_nex_creator.lt(n, m)) {
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


void nla_grobner::superpose(equation * eq) {
    for (equation * target : m_to_superpose) {
        superpose(eq, target);
    }
}


bool nla_grobner::compute_basis_step() {
    equation * eq = pick_next();
    if (!eq)
        return true;
    m_stats.m_num_processed++;
    equation * new_eq = simplify_using_processed(eq);
    if (new_eq != nullptr && eq != new_eq) {
        // equation was updated using non destructive updates
        m_equations_to_unfreeze.push_back(eq);
        eq = new_eq;
    }
    if (canceled()) return false;
    if (!simplify_to_superpose_with_eq(eq)) return false;
    TRACE("grobner", tout << "eq = "; display_equation(tout, *eq););
    superpose(eq);
    insert_to_superpose(eq);
    simplify_to_superpose(eq);
    TRACE("grobner", tout << "end of iteration:\n"; display(tout););
    return false;
}

void nla_grobner::compute_basis(){
    compute_basis_init();        
    if (!compute_basis_loop()) {
        set_gb_exhausted();
    }
}
void nla_grobner::compute_basis_init(){
    c().lp_settings().stats().m_grobner_basis_computatins++;    
    m_num_of_equations = 0;
    
}        

bool nla_grobner::canceled() const {
    return c().lp_settings().get_cancel_flag();
}


bool nla_grobner::done() const {
    if (
        m_num_of_equations >= c().m_nla_settings.grobner_eqs_threshold() 
        ||
        canceled()
        ||
        m_reported > 10
        ||
        m_conflict) {
        TRACE("grobner", tout << "done()\n";);
        return true;
    }
    return false;
}

bool nla_grobner::compute_basis_loop(){
    while (!done()) {
        if (compute_basis_step())
            return true;
    }
    return false;
}

void nla_grobner::set_gb_exhausted(){
    m_nl_gb_exhausted = true;
}

void nla_grobner::update_statistics(){
    /* todo : implement
      m_stats.m_gb_simplify      += gb.m_stats.m_simplify;
    m_stats.m_gb_superpose     += gb.m_stats.m_superpose;
    m_stats.m_gb_num_to_superpose += gb.m_stats.m_num_to_superpose;
    m_stats.m_gb_compute_basis++;*/
}


bool nla_grobner::push_calculation_forward(ptr_vector<equation>& eqs, unsigned & next_weight) {
    return  (!m_nl_gb_exhausted) &&
        try_to_modify_eqs(eqs, next_weight);
}

bool nla_grobner::try_to_modify_eqs(ptr_vector<equation>& eqs, unsigned& next_weight) {
    NOT_IMPLEMENTED_YET();
    return false;
}


void nla_grobner::grobner_lemmas() {
    c().lp_settings().stats().m_grobner_calls++;    
    init();
    
    ptr_vector<equation> eqs;
    unsigned next_weight =
        (unsigned)(var_weight::MAX_DEFAULT_WEIGHT) + 1; // next weight using during perturbation phase. 
    do {
        TRACE("grobner", tout << "before:\n"; display(tout););
        compute_basis();
        update_statistics();
        TRACE("grobner", tout << "after:\n"; display(tout););
        // if (find_conflict(eqs))
        //     return;
    }
    while(push_calculation_forward(eqs, next_weight));
}
void nla_grobner:: del_equations(unsigned old_size) {
    TRACE("grobner", );
    SASSERT(m_equations_to_delete.size() >= old_size);
    equation_vector::iterator it  = m_equations_to_delete.begin();
    equation_vector::iterator end = m_equations_to_delete.end();
    it += old_size;
    for (; it != end; ++it) {
        equation * eq = *it;
        if (eq)
            del_equation(eq);
    }
    m_equations_to_delete.shrink(old_size);    
}

void nla_grobner::display_equations(std::ostream & out, equation_set const & v, char const * header) const {
    out << header << "\n";
    for (const equation* e : v) 
        display_equation(out, *e);
}

std::ostream& nla_grobner::display_equation(std::ostream & out, const equation & eq) const {
    out << "m_exp = " << *eq.exp() << "\n";
    out << "dep = "; display_dependency(out, eq.dep()) << "\n";
    return out;
}

void nla_grobner::assert_eq_0(nex* e, ci_dependency * dep) {
    if (e == nullptr || is_zero_scalar(e))
        return;
    equation * eq = alloc(equation);
    init_equation(eq, e, dep);
    TRACE("grobner", display_equation(tout, *eq);
    for (unsigned j : get_vars_of_expr(e)) {
        c().print_var(j, tout) << "\n";
    });
    insert_to_simplify(eq);
}

void nla_grobner::init_equation(equation* eq, nex*e, ci_dependency * dep) {
    unsigned bidx   = m_equations_to_delete.size();
    eq->m_bidx      = bidx;
    eq->dep()       = dep;
    eq->exp()       = e;
    m_equations_to_delete.push_back(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
}

nla_grobner::~nla_grobner() {
    del_equations(0);
}

std::ostream& nla_grobner::display_dependency(std::ostream& out, ci_dependency* dep) const {
    svector<lp::constraint_index> expl;
    m_dep_manager.linearize(dep, expl);   
    {
        lp::explanation e(expl);
        if (!expl.empty()) {
            out << "upper constraints\n";    
            m_core->print_explanation(e, out);
        }else {
            out << "no constraints\n";
        }
    }
    return out;
}
    
} // end of nla namespace
