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
    m_dep_manager(m_val_manager, m_alloc) {}

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


void nla_grobner::add_row(unsigned i) {    
    const auto& row = c().m_lar_solver.A_r().m_rows[i];    
    TRACE("nla_grobner", tout << "adding row to gb\n"; c().m_lar_solver.print_row(row, tout););
    nex_sum * ns = m_nex_creator.mk_sum();
    create_sum_from_row(row, m_nex_creator, *ns);
    TRACE("nla_grobner", tout << "ns = " << *ns << "\n";);
    ci_dependency * dep = nullptr;
    m_tmp_var_set.clear();
    assert_eq_0(ns, dep);
}

void nla_grobner::init() {
    find_nl_cluster();
    for (unsigned i : m_rows) {
        add_row(i);
    }
}

bool nla_grobner::is_trivial(equation* eq) const {
    return eq->m_exp->size() == 0;
}

bool nla_grobner::is_better_choice(equation * eq1, equation * eq2) {
    if (!eq2)
        return true;
    if (is_trivial(eq1))
        return true;
    if (is_trivial(eq2))
        return false;
    return m_nex_creator.lt(eq1->m_exp, eq2->m_exp);
}

void nla_grobner::del_equation(equation * eq) {
    NOT_IMPLEMENTED_YET();
    /*
    m_processed.erase(eq);
    m_to_process.erase(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
    m_equations_to_delete[eq->m_bidx] = 0;
    del_monomials(eq->m_exp);
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
    bool result = false;
    bool simplified;
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *eq); tout << "using already processed equalities\n";);
    do {
        simplified = false;
        for (equation const* p : m_processed) {
            equation * new_eq  = simplify(p, eq);
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


// void nla_grobner::simplify(ptr_vector<monomial> & monomials) {
//     NOT_IMPLEMENTED_YET();
//     // std::stable_sort(monomials.begin(), monomials.end(), m_monomial_lt);
//     // merge_monomials(monomials);
//     // normalize_coeff(monomials);
// }

nla_grobner::equation * nla_grobner::simplify(equation const * source, equation * target) {
    NOT_IMPLEMENTED_YET();
    /*
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *target); tout << "using: "; display_equation(tout, *source););
    if (source->get_num_monomials() == 0)
        return nullptr;
    m_stats.m_simplify++;
    bool result = false;
    bool simplified;
    do {
        simplified          = false;
        unsigned i          = 0;
        unsigned j          = 0;
        unsigned sz         = target->m_monomials.size();
        monomial const * LT = source->get_monomial(0); 
        ptr_vector<monomial> & new_monomials = m_tmp_monomials;
        new_monomials.reset();
        ptr_vector<expr>  & rest = m_tmp_vars1;
        for (; i < sz; i++) {
            monomial * curr = target->m_monomials[i];
            rest.reset();
            if (is_subset(LT, curr, rest)) {
                if (i == 0)
                    m_changed_leading_term = true;
                if (!result) {
                    // first time that source is being applied.
                    target->m_dep = m_dep_manager.mk_join(target->m_dep, source->m_dep);
                }
                simplified     = true;
                result         = true;
                rational coeff = curr->m_coeff;
                coeff         /= LT->m_coeff;
                coeff.neg();
                if (!rest.empty())
                    target->m_lc = false;
                mul_append(1, source, coeff, rest, new_monomials);
                del_monomial(curr);
                target->m_monomials[i] = 0;
            }
            else {
                target->m_monomials[j] = curr;
                j++;
            }
        }
        if (simplified) {
            target->m_monomials.shrink(j);
            target->m_monomials.append(new_monomials.size(), new_monomials.c_ptr());
            simplify(target);
        }
    }
    while (simplified && !m_manager.canceled());
    TRACE("grobner", tout << "result: "; display_equation(tout, *target););
    return result ? target : nullptr;*/
    return nullptr;
}

std::ostream& nla_grobner::display_equation(std::ostream & out, equation & eq) {
    tout << "m_exp = " << *eq.m_exp << "\n";
    tout << "dep = "; display_dependency(tout, eq.m_dep) << "\n";
    return tout;
}

void nla_grobner::display_monomial(std::ostream & out, monomial const & m) const {
    NOT_IMPLEMENTED_YET();
}

void nla_grobner::display(std::ostream & out) const {
    NOT_IMPLEMENTED_YET();
}

void nla_grobner::assert_eq_0(const nex* e, ci_dependency * dep) {
    TRACE("nla_grobner", tout << "e = " << *e << "\n";);
    if (e == nullptr)
        return;
    equation * eq = new equation();
    init_equation(eq, e, dep);
    m_to_process.insert(eq);
}

void nla_grobner::init_equation(equation* eq, const nex*e, ci_dependency * dep) {
    unsigned bidx   = m_equations_to_delete.size();
    eq->m_bidx      = bidx;
    eq->m_dep       = dep;
    eq->m_lc        = true;
    eq->m_exp =       e;
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
