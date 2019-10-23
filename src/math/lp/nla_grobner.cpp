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
nla_grobner::nla_grobner(core *c
                         ) :
    common(c),
    m_nl_gb_exhausted(false),
    m_dep_manager(m_val_manager, m_alloc),
    m_changed_leading_term(false)
{}

// Scan the grobner basis eqs for equations of the form x - k = 0 or x = 0 is found, and x is not fixed,
// then assert bounds for x, and continue
bool nla_grobner::scan_for_linear(ptr_vector<equation>& eqs) {
    bool result = false;
    for (nla_grobner::equation* eq : eqs) {
        if (!eq->is_linear_combination()) {
            TRACE("non_linear", tout << "processing new equality:\n"; display_equation(tout, *eq););
            TRACE("non_linear_bug", tout << "processing new equality:\n"; display_equation(tout, *eq););
            if (internalize_gb_eq(eq))
                result = true;
        }
    }
    return result;
}

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

void nla_grobner::display(std::ostream & out) {
    const auto& matrix = c().m_lar_solver.A_r();
    out << "rows = " << m_rows.size() << "\n";
    for (unsigned k : m_rows) {
        c().print_term(matrix.m_rows[k], out) << "\n";
    }
    out << "the matrix =\n";
          
    for (const auto & r : matrix.m_rows) {
        c().print_term(r, out) << std::endl;
    }
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

/**
   \brief Create a new monomial using the given coeff and m. Fixed
   variables in m are substituted by their values.  The arg dep is
   updated to store these dependencies. The set already_found is
   updated with the fixed variables in m.  A variable is only
   added to dep if it is not already in already_found.

   Return null if the monomial was simplified to 0.
*/
nex * nla_grobner::mk_monomial_in_row(rational coeff, lpvar j, ci_dependency * & dep) {
    NOT_IMPLEMENTED_YET();
    return nullptr; 
    /*
      ptr_buffer<expr> vars;
    rational r;

    if (c().is_monic_var(j)) {
        coeff *= get_monomial_coeff(m);
        m      = get_monomial_body(m);
        if (m_util.is_mul(m)) {
            SASSERT(is_pure_monomial(m));
            for (unsigned i = 0; i < to_app(m)->get_num_args(); i++) {
                expr * arg = to_app(m)->get_arg(i);
                process_var(arg);
            }
        }
        else {
            process_var(m);
        }
    }
    else {
        process_var(m);
    }
    if (!coeff.is_zero())
        return gb.mk_monomial(coeff, vars.size(), vars.c_ptr());
    else
        return nullptr;
    */
}

common::ci_dependency* nla_grobner::dep_from_vector(svector<lp::constraint_index> & cs) {
    ci_dependency * d = nullptr;
    for (auto c : cs)
        d = m_dep_manager.mk_join(d, m_dep_manager.mk_leaf(c));
    return d;
}

void nla_grobner::add_row(unsigned i) {    
    const auto& row = c().m_lar_solver.A_r().m_rows[i];    
    TRACE("grobner", tout << "adding row to gb\n"; c().m_lar_solver.print_row(row, tout););
    nex_sum * ns = m_nex_creator.mk_sum();

    svector<lp::constraint_index> fixed_vars_constraints;
    create_sum_from_row(row, m_nex_creator, *ns, true); // true to treat fixed vars as scalars
    TRACE("grobner", tout << "ns = " << *ns << "\n";);
    m_tmp_var_set.clear();    
    assert_eq_0(ns, get_fixed_vars_dep_from_row(row, m_dep_manager));
}

void nla_grobner::simplify_equations_to_process() {
    for (equation *eq : m_to_simplify) {
        eq->exp() = m_nex_creator.simplify(eq->exp());
    }
}

void nla_grobner::init() {
    find_nl_cluster();
    c().clear_and_resize_active_var_set();
    for (unsigned i : m_rows) {
        add_row(i);
    }
    simplify_equations_to_process();
}

bool nla_grobner::is_trivial(equation* eq) const {
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
    NOT_IMPLEMENTED_YET();
    /*
    m_to_superpose.erase(eq);
    m_to_simplify.erase(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
    m_equations_to_delete[eq->m_bidx] = 0;
    del_monomials(eq->m_exp);
    dealloc(eq);
    */
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
        }        
    }
    while (simplified);
    TRACE("grobner", tout << "simplification result: "; display_equation(tout, *eq););
    return result ? eq : nullptr;

}

nex_mul* nla_grobner::get_highest_monomial(nex* e) const {
    switch (e->type()) {
    case expr_type::MUL:
        return to_mul(e);
    case expr_type::SUM:
        return to_mul((*to_sum(e))[0]);
    default:
        return nullptr;
    }    
}
// source 3f + k + l = 0, so f = (-k - l)/3
// target 2fg + 3fp + e = 0  
// target is replaced by 2(-k/3 - l/3)g + 3(-k/3 - l/3)p + e = -2/3kg -2/3lg - kp -lp + e
bool nla_grobner::simplify_target_monomials(equation * source, equation * target) {
    const nex_mul * high_mon = get_highest_monomial(source->exp());
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

bool nla_grobner::simplify_target_monomials_sum_check_only(nex_sum* targ_sum,
                                                           const nex_mul* high_mon) {
    for (auto t : *targ_sum) {
        if (!t->is_mul()) continue; // what if t->is_var()
        if (divide_ignore_coeffs_check_only(to_mul(t), high_mon)) {
            TRACE("grobner", tout << "yes div: " << *targ_sum << " / " << high_mon << "\n";);
            return true;
        }
    }
    TRACE("grobner", tout << "no div: " << *targ_sum << " / " << high_mon << "\n";);
    return false;
}


bool nla_grobner::simplify_target_monomials_sum(equation const * source,
                                                equation *target, nex_sum* targ_sum,
                                                const nex_mul* high_mon) {
    if (!simplify_target_monomials_sum_check_only(targ_sum, high_mon))
        return false;
    unsigned targ_orig_size = targ_sum->size();
    for (unsigned j = 0; j < targ_orig_size; j++) {
        simplify_target_monomials_sum_j(source, target, targ_sum, high_mon, j);
    }
    return true;
}

nex_mul* nla_grobner::divide_ignore_coeffs(nex* ej, const nex_mul* h) {
    if (!ej->is_mul())
        return nullptr;
    nex_mul* m = to_mul(ej);
    if (!divide_ignore_coeffs_check_only(m, h))
        return nullptr;
    return divide_ignore_coeffs_perform(m, h);
}

// return true if h divides t
bool nla_grobner::divide_ignore_coeffs_check_only(nex_mul* t , const nex_mul* h) {
    SASSERT(m_nex_creator.is_simplified(t) && m_nex_creator.is_simplified(h));
    unsigned j = 0; // points to t
    for(auto & p : *h) {
        bool p_swallowed = false;
        lpvar h_var = to_var(p.e())->var();
        for (; j < t->size() && !p_swallowed; j++) {
            auto &tp = (*t)[j];
            if (to_var(tp.e())->var() == h_var) {
                if (tp.pow() >= p.pow()) {
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

// perform the division t / h, but ignores the coefficients
nex_mul * nla_grobner::divide_ignore_coeffs_perform(nex_mul* t, const nex_mul* h) {
    nex_mul * r = m_nex_creator.mk_mul();
    unsigned j = 0; // points to t
    for(auto & p : *h) {
        bool p_swallowed = false;
        lpvar h_var = to_var(p.e())->var();
        for (; j < t->size() && !p_swallowed; j++) {
            auto &tp = (*t)[j];
            if (to_var(tp.e())->var() == h_var) {
                if (tp.pow() >= p.pow()) {
                    p_swallowed = true;
                    if (tp.pow() > p.pow())
                        r->add_child_in_power(tp.e(), tp.pow() - p.pow());
                } 
            } else {
                r->add_child_in_power(tp);
            }
        }
    }
    TRACE("grobner", tout << "r = " << *r << " = " << *t << " / " << *h << "\n";);
    return r;
}

bool nla_grobner::simplify_target_monomials_sum_j(equation const * source, equation *target, nex_sum* targ_sum, const nex_mul* high_mon, unsigned j) {    

    nex * ej = (*targ_sum)[j];
    nex * ej_over_high_mon = divide_ignore_coeffs(ej, high_mon);
    if (ej_over_high_mon == nullptr)
        return false;
    
    NOT_IMPLEMENTED_YET();
    return false;
    /*
          unsigned i          = 0;
    unsigned new_target_sz = 0;
    unsigned target_sz         = target->m_monomials.size();
    monomial const * LT = source->get_monomial(0); 
    m_tmp_monomials.reset();
    for (; i < target_sz; i++) {
        monomial * targ_i = target->m_monomials[i];
        if (divide_ignore_coeffs(targ_i, LT)) {
            if (i == 0)
                m_changed_leading_term = true;
            if (!m_tmp_vars1.empty())
                target->m_lc = false;
            mul_append_skip_first(source, - targ_i->m_coeff / (LT->m_coeff), m_tmp_vars1);
            del_monomial(targ_i);
        }
        else {
            if (i != new_target_sz) {
                target->m_monomials[new_target_sz] = targ_i;
            }
            new_target_sz++;
        }
    }
    if (new_target_sz < target_sz) {
        target->m_monomials.shrink(new_target_sz);
        target->m_monomials.append(m_tmp_monomials.size(), m_tmp_monomials.c_ptr());
        simplify_eq(target);
        TRACE("grobner", tout << "result: "; display_equation(tout, *target););
        return true;
    }
    return false;
    */
    return false;
}


nla_grobner::equation * nla_grobner::simplify_source_target(equation * source, equation * target) {
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *target); tout << "using: "; display_equation(tout, *source););
    if (source->get_num_monomials() == 0)
        return nullptr;
    m_stats.m_simplify++;
    bool result = false;
    do {
        if (simplify_target_monomials(source, target)) {
            result = true;
        } else {
            break;
        }
    } while (!canceled());
    TRACE("grobner", tout << "result: " << result << "\n"; if (result) display_equation(tout, *target););
    if (result) {
        target->dep() = m_dep_manager.mk_join(target->dep(), source->dep());
        return target;
    }
    return nullptr;}
 
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
}

bool nla_grobner::simplify_processed_with_eq(equation* eq) {
    ptr_buffer<equation> to_insert;
    ptr_buffer<equation> to_remove;
    ptr_buffer<equation> to_delete;
    equation_set::iterator it  = m_to_superpose.begin();
    equation_set::iterator end = m_to_superpose.end();
    for (; it != end && !canceled(); ++it) {
        equation * target        = *it;
        m_changed_leading_term = false;
        // if the leading term is simplified, then the equation has to be moved to m_to_simplify
        equation * new_target    = simplify_source_target(eq, target);
        if (new_target != nullptr) {
            process_simplified_target(to_insert, new_target, target, to_remove);
        }
        if (is_trivial(target))
            to_delete.push_back(target);
    }
    for (equation* eq : to_insert) 
        insert_to_superpose(eq);
    for (equation* eq : to_remove)
        m_to_superpose.erase(eq);
    for (equation* eq : to_delete) 
        del_equation(eq);
    return !canceled();
}

void  nla_grobner::simplify_to_process(equation* eq) {
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

// if e is the sum adds to r all children of e multiplied by beta, except the first one
// which corresponds to the highest monomial
void nla_grobner::add_mul_skip_first(nex_sum* r, const rational& beta, nex *e, nex_mul* c) {
     if (e->is_sum()) {
        nex_sum *es = to_sum(e);
        for (unsigned j = 1; j < es->size(); j++) {
            r->add_child(m_nex_creator.mk_mul(beta, (*es)[j], c));
        }
        TRACE("grobner", tout << "r = " << *r << "\n";);        
    }
}


// let e1: alpha*ab+q=0, and e2: beta*ac+e=0, then beta*qc - alpha*eb = 0
nex * nla_grobner::expr_superpose(nex* e1, nex* e2, nex_mul* ab, nex_mul* ac, nex_mul* b, nex_mul* c) {
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
    return ret;
}
// let eq1: ab+q=0, and eq2: ac+e=0, then qc - eb = 0
void nla_grobner::superpose(equation * eq1, equation * eq2) {
    TRACE("grobner", tout << "eq1="; display_equation(tout, *eq1) << "eq2="; display_equation(tout, *eq2););
    nex_mul * ab = get_highest_monomial(eq1->exp()); 
    nex_mul * ac = get_highest_monomial(eq2->exp());
    nex_mul *b, *c;
    TRACE("grobner", tout << "ab=" << *ab << " , " << " ac = " << *ac << "\n";);
    if (!find_b_c(ab, ac, b, c)) {
        return;
    }
    equation* eq = new equation(); // to do - need no remove !!!!!!!!!!!!!!!!!!!
    init_equation(eq, expr_superpose( eq1->exp(), eq2->exp(), ab, ac, b, c), m_dep_manager.mk_join(eq1->dep(), eq2->dep()));  
    insert_to_simplify(eq);
}

bool nla_grobner::find_b_c(nex_mul*ab, nex_mul* ac, nex_mul*& b, nex_mul*& c) {
    if (!find_b_c_check_only(ab, ac))
        return false;
    b = m_nex_creator.mk_mul(); c = m_nex_creator.mk_mul();
    nex_pow* bp = ab->begin();
    nex_pow* cp = ac->begin();
    for (;;) {
        if (m_nex_creator.lt(bp->e(), cp->e())) {
            b->add_child_in_power(*bp);
            if (++bp == ab->end())
                break;
        } else if (m_nex_creator.lt(cp->e(), bp->e())) {
            c->add_child_in_power(*cp);
            if (++cp == ac->end())
                break;
        } else {
            unsigned b_pow = bp->pow();
            unsigned c_pow = cp->pow();
            if (b_pow > c_pow) {
                b->add_child_in_power(bp->e(), b_pow - c_pow);
            } else if (c_pow > b_pow) {
                c->add_child_in_power(cp->e(), c_pow - b_pow);
            } // otherwise the power are equal and no child added to either b or c
            bp++; cp++;
           
            if (bp == ab->end() || cp == ac->end()) {
                break;
            }
        }
    }
    
    while (cp != ac->end()) {
        c->add_child_in_power(*cp);
        cp++;
    }
    while (bp != ab->end()) {
        b->add_child_in_power(*bp);
        bp++;
    }
    TRACE("nla_grobner", tout << "b=" << *b << ", c=" <<*c << "\n";);
    return true;
}

bool nla_grobner::find_b_c_check_only(const nex_mul*ab, const nex_mul* ac) const {
    SASSERT(m_nex_creator.is_simplified(ab) && m_nex_creator.is_simplified(ab));
    unsigned i = 0, j = 0; // i points to ab, j points to ac
    for (;;) {
        if (m_nex_creator.lt((*ab)[i].e(), (*ac)[j].e())) {
            i++;
            if (i == ab->size())
                return false;
        } else if (m_nex_creator.lt((*ac)[j].e(), (*ab)[i].e())) {
            j++;
            if (j == ac->size())
                return false;
        } else {
            TRACE("grobner", tout << "found common " << *(*ac)[j].e() << " in " << *ab << " and " << *ac << "\n";);
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
    if (!simplify_processed_with_eq(eq)) return false;
    superpose(eq);
    insert_to_superpose(eq);
    simplify_to_process(eq);
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

bool nla_grobner::compute_basis_loop(){
    while (m_num_of_equations < c().m_nla_settings.grobner_eqs_threshold()) {
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

// Scan the grobner basis eqs, and look for inconsistencies.

bool nla_grobner::find_conflict(ptr_vector<equation>& eqs){
    eqs.reset();
    get_equations(eqs);
    TRACE("grobner_bug", tout << "after gb\n";);
    for (equation* eq : eqs) {
        TRACE("grobner_bug", display_equation(tout, *eq););
        if (is_inconsistent(eq) || is_inconsistent2(eq))
            return true;
    }
    return false;
}

bool nla_grobner::is_inconsistent(equation*) {
    NOT_IMPLEMENTED_YET();
    return false;
}

bool nla_grobner::is_inconsistent2(equation*) {
    NOT_IMPLEMENTED_YET();
    return false;
}

template <typename T, typename V>
void copy_to(const T& source, V& target ) {
    for (auto e : source)
        target.push_back(e);
}

void nla_grobner::get_equations(ptr_vector<equation>& result) {
    copy_to(m_to_superpose, result);
    copy_to(m_to_simplify, result);
}


bool nla_grobner::push_calculation_forward(ptr_vector<equation>& eqs, unsigned & next_weight) {
    return scan_for_linear(eqs)
        &&
        (!m_nl_gb_exhausted) &&
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
        TRACE("nla_gb", tout << "before:\n"; display(tout););
        compute_basis();
        update_statistics();
        TRACE("nla_gb", tout << "after:\n"; display(tout););
        if (find_conflict(eqs))
            return;
    }
    while(push_calculation_forward(eqs, next_weight));
}
void nla_grobner:: del_equations(unsigned old_size) {
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
    NOT_IMPLEMENTED_YET();
}

std::ostream& nla_grobner::display_equation(std::ostream & out, const equation & eq) {
    out << "m_exp = " << *eq.exp() << "\n";
    out << "dep = "; display_dependency(out, eq.dep()) << "\n";
    return out;
}

void nla_grobner::display(std::ostream & out) const {
    NOT_IMPLEMENTED_YET();
}

void nla_grobner::assert_eq_0(nex* e, ci_dependency * dep) {
    TRACE("grobner", tout << "e = " << *e << "\n";);
    if (e == nullptr)
        return;
    equation * eq = new equation();
    init_equation(eq, e, dep);
    insert_to_simplify(eq);
}

void nla_grobner::init_equation(equation* eq, nex*e, ci_dependency * dep) {
    unsigned bidx   = m_equations_to_delete.size();
    eq->m_bidx      = bidx;
    eq->dep()       = dep;
    eq->m_lc        = true;
    eq->exp()       = e;
    m_equations_to_delete.push_back(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
}

std::ostream& nla_grobner::display_dependency(std::ostream& out, ci_dependency* dep) {
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
