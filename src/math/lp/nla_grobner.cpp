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
nla_grobner::nla_grobner(core *c) : common(c), m_nl_gb_exhausted(false) {}

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
    SASSERT(m_active_vars.contains(j) == false);
    const auto& matrix = c().m_lar_solver.A_r();
    m_active_vars.insert(j);
    for (auto & s : matrix.m_columns[j]) {
        unsigned row = s.var();
        if (m_rows.contains(row)) continue;
        m_rows.insert(row);
        for (auto& rc : matrix.m_rows[row]) {
            if (m_active_vars.contains(rc.var()))
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
            if (! m_active_vars.contains(j))
                add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
        }
    }            
}

var_weight nla_grobner::get_var_weight(lpvar j) const {
    var_weight k;
    switch (c().m_lar_solver.get_column_type(j)) {
        
    case lp::column_type::fixed:
        k = var_weight::FIXED;
        break;
    case lp::column_type::boxed:
        k = var_weight::BOUNDED;
        break;
    case lp::column_type::lower_bound:
    case lp::column_type::upper_bound:
        k = var_weight::NOT_FREE;
    case lp::column_type::free_column:
        k = var_weight::FREE;
        break;
    default:
        UNREACHABLE();
        break;
    }
    if (c().is_monic_var(j)) {
        return (var_weight)((int)k + 1);
    }
    return k;
}

void nla_grobner::set_active_vars_weights() {
    m_active_vars_weights.resize(c().m_lar_solver.column_count());
    for (lpvar j : m_active_vars) {
        m_active_vars_weights[j] = get_var_weight(j);
    }
}

void nla_grobner::find_nl_cluster() {
    prepare_rows_and_active_vars();
    std::queue<lpvar> q;
    for (lpvar j : c().m_to_refine) {        
        TRACE("nla_grobner", c().print_monic(c().emons()[j], tout) << "\n";);
        q.push(j);
    }

    while (!q.empty()) {
        unsigned j = q.front();        
        q.pop();
        if (m_active_vars.contains(j))
            continue;
        add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
    }
    set_active_vars_weights();
    TRACE("nla_grobner", display(tout););
}

void nla_grobner::prepare_rows_and_active_vars() {
    m_rows.clear();
    m_rows.resize(c().m_lar_solver.row_count());
    m_active_vars.clear();
    m_active_vars.resize(c().m_lar_solver.column_count());
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
void nla_grobner::add_row_to_gb(unsigned) {
    NOT_IMPLEMENTED_YET();
}
void nla_grobner::add_monomial_def(lpvar) {
    NOT_IMPLEMENTED_YET();
}
void nla_grobner::init() {
    find_nl_cluster();
    for (unsigned i : m_rows) {
        add_row_to_gb(i);
    }
    for (lpvar j : m_active_vars) {
        add_monomial_def(j);
    }
}

bool nla_grobner::is_trivial(equation* eq) const {
    return eq->m_monomials.empty();
}

bool nla_grobner:: is_better_choice(equation * eq1, equation * eq2) {
    if (!eq2)
        return true;
    if (is_trivial(eq1))
        return true;
    if (is_trivial(eq2))
        return false;
    if (eq1->m_monomials[0]->get_degree() < eq2->m_monomials[0]->get_degree())
        return true;
    if (eq1->m_monomials[0]->get_degree() > eq2->m_monomials[0]->get_degree())
        return false;
    return eq1->m_monomials.size() < eq2->m_monomials.size();

}

void nla_grobner::del_equation(equation * eq) {
    SASSERT(false);
    /*
    m_processed.erase(eq);
    m_to_process.erase(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
    m_equations_to_delete[eq->m_bidx] = 0;
    del_monomials(eq->m_monomials);
    dealloc(eq);
    */
}

nla_grobner::equation* nla_grobner::pick_next() {
    equation * r = nullptr;
    ptr_buffer<equation> to_delete;
    for (equation * curr : m_to_process) {
        if (is_trivial(curr))
            to_delete.push_back(curr);
        else if (is_better_choice(curr, r))
            r = curr;
    }
    for (equation * e : to_delete) 
        del_equation(e);
    if (r)
        m_to_process.erase(r);
    TRACE("grobner", tout << "selected equation: "; if (!r) tout << "<null>\n"; else display_equation(tout, *r););
    return r;
}

nla_grobner::equation* nla_grobner::simplify_using_processed(equation* eq) {
    NOT_IMPLEMENTED_YET();
    return nullptr;
}

nla_grobner::equation* nla_grobner::simplify_processed(equation* eq) {
    NOT_IMPLEMENTED_YET();
    return nullptr;
}

nla_grobner::equation*  nla_grobner::simplify_to_process(equation*) {
    NOT_IMPLEMENTED_YET();
    return nullptr;
}


void nla_grobner::superpose(equation * eq1, equation * eq2) {
    SASSERT(false);
}

void nla_grobner::superpose(equation * eq){
    SASSERT(false);
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
    if (!simplify_processed(eq)) return false;
    superpose(eq);
    m_processed.insert(eq);
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
    m_stats.m_gb_num_processed += gb.m_stats.m_num_processed;
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
    copy_to(m_processed, result);
    copy_to(m_to_process, result);
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
    NOT_IMPLEMENTED_YET();
}
void nla_grobner::display_equation(std::ostream & out, equation const & eq) const {
    NOT_IMPLEMENTED_YET();
}

void nla_grobner::display_monomial(std::ostream & out, monomial const & m) const {
    NOT_IMPLEMENTED_YET();
}

void nla_grobner::display(std::ostream & out) const {
    NOT_IMPLEMENTED_YET();
}

} // end of nla namespace
