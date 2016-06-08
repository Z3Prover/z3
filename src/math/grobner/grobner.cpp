/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    grobner.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-04.

Revision History:

--*/
#include"grobner.h"
#include"ast_pp.h"
#include"ref_util.h"

// #define PROFILE_GB

grobner::grobner(ast_manager & m, v_dependency_manager & d):
    m_manager(m),
    m_dep_manager(d),
    m_util(m),
    m_var_lt(m_var2weight),
    m_monomial_lt(m_var_lt),
    m_changed_leading_term(false),
    m_unsat(0) {
}

grobner::~grobner() {
    flush();
}

void grobner::flush() {
    dec_ref_map_keys(m_manager, m_var2weight);
    del_equations(0);
}

void grobner::del_equations(unsigned old_size) {
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

void grobner::del_equation(equation * eq) {
    m_processed.erase(eq);
    m_to_process.erase(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
    m_equations_to_delete[eq->m_bidx] = 0;
    del_monomials(eq->m_monomials);
    dealloc(eq);
}

void grobner::del_monomials(ptr_vector<monomial>& ms) {
    ptr_vector<monomial>::iterator it  = ms.begin();
    ptr_vector<monomial>::iterator end = ms.end();
    for (; it != end; ++it) {
        del_monomial(*it);
    }
    ms.reset();
}

void grobner::del_monomial(monomial * m) {
    ptr_vector<expr>::iterator it2  = m->m_vars.begin();
    ptr_vector<expr>::iterator end2 = m->m_vars.end();
    for (; it2 != end2; ++it2) {
        expr * v = *it2;
        m_manager.dec_ref(v);
    }
    dealloc(m);
}

void grobner::unfreeze_equations(unsigned old_size) {
    SASSERT(m_equations_to_unfreeze.size() >= old_size);
    equation_vector::iterator it  = m_equations_to_unfreeze.begin();
    equation_vector::iterator end = m_equations_to_unfreeze.end();
    it += old_size;
    for (; it != end; ++it) {
        equation * eq = *it;
        m_to_process.insert(eq);
    }
    m_equations_to_unfreeze.shrink(old_size);
}

void grobner::push_scope() {
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_equations_to_unfreeze_lim = m_equations_to_unfreeze.size();
    s.m_equations_to_delete_lim   = m_equations_to_delete.size();
}

void grobner::pop_scope(unsigned num_scopes) {
    SASSERT(num_scopes >= get_scope_level());
    unsigned new_lvl = get_scope_level() - num_scopes;
    scope & s        = m_scopes[new_lvl];
    unfreeze_equations(s.m_equations_to_unfreeze_lim);
    del_equations(s.m_equations_to_delete_lim);
    m_scopes.shrink(new_lvl);
}

void grobner::reset() {
    flush();
    m_processed.reset();
    m_to_process.reset();
    m_equations_to_unfreeze.reset();
    m_equations_to_delete.reset();
    m_unsat = 0;
}

void grobner::display_var(std::ostream & out, expr * var) const {
    if (is_app(var) && to_app(var)->get_num_args() > 0)
        out << "#" << var->get_id();
    else
        out << mk_pp(var, m_manager);
}

void grobner::display_vars(std::ostream & out, unsigned num_vars, expr * const * vars) const {
    for (unsigned i = 0; i < num_vars; i++) {
        display_var(out, vars[i]); 
        out << " ";
    }
}

void grobner::display_monomial(std::ostream & out, monomial const & m) const {
    if (!m.m_coeff.is_one() || m.m_vars.empty()) {
        out << m.m_coeff;
        if (!m.m_vars.empty())
            out << "*";
    }
    
    if (!m.m_vars.empty()) {
        ptr_vector<expr>::const_iterator it  = m.m_vars.begin();
        ptr_vector<expr>::const_iterator end = m.m_vars.end();
        unsigned power = 1;
        expr *   prev  = *it;
        it++;
        for (; it != end; ++it) {
            expr * curr = *it;
            if (curr == prev) {
                power++;
            }
            else {
                display_var(out, prev);
                if (power > 1)
                    out << "^" << power;
                power = 1;
                prev  = curr;
                out << "*";
            }
        }
        display_var(out, prev);
        if (power > 1)
            out << "^" << power;
    }
}

void grobner::display_monomials(std::ostream & out, unsigned num_monomials, monomial * const * monomials) const {
    bool first = true;
    for (unsigned i = 0; i < num_monomials; i++) {
        monomial const * m = monomials[i];
        if (first)
            first = false;
        else
            out << " + ";
        display_monomial(out, *m);
    }
}

void grobner::display_equation(std::ostream & out, equation const & eq) const {
    display_monomials(out, eq.m_monomials.size(), eq.m_monomials.c_ptr());
    out << " = 0\n";
}

void grobner::display_equations(std::ostream & out, equation_set const & v, char const * header) const {
    if (!v.empty()) {
        out << header << "\n";
        equation_set::iterator it  = v.begin();
        equation_set::iterator end = v.end();
        for (; it != end; ++it)
            display_equation(out, *(*it));
    }
}

void grobner::display(std::ostream & out) const {
    display_equations(out, m_processed, "processed:");
    display_equations(out, m_to_process, "to process:");
}

void grobner::set_weight(expr * n, int weight) {
    if (weight == 0)
        return;
    if (!m_var2weight.contains(n))
        m_manager.inc_ref(n);
    m_var2weight.insert(n, weight);
}

/**
   \brief Update equation using the new variable order.
   Return true if the leading term was modified.
*/
bool grobner::update_order(equation * eq) {
    if (eq->get_num_monomials() == 0)
        return false;
    monomial * first = eq->m_monomials[0];
    ptr_vector<monomial>::iterator it  = eq->m_monomials.begin();
    ptr_vector<monomial>::iterator end = eq->m_monomials.end();
    for (; it != end; ++it) {
        monomial * m = *it;
        std::stable_sort(m->m_vars.begin(), m->m_vars.end(), m_var_lt);
    }
    std::stable_sort(eq->m_monomials.begin(), eq->m_monomials.end(), m_monomial_lt);
    return eq->m_monomials[0] != first;
}

void grobner::update_order(equation_set & s, bool processed) {
    ptr_buffer<equation> to_remove;
    equation_set::iterator it  = s.begin();
    equation_set::iterator end = s.end();
    for (;it != end; ++it) {
        equation * eq = *it;
        if (update_order(eq)) {
            if (processed) {
                to_remove.push_back(eq);
                m_to_process.insert(eq);
            }
        }
    }
    ptr_buffer<equation>::iterator it2  = to_remove.begin();
    ptr_buffer<equation>::iterator end2 = to_remove.end();
    for (; it2 != end2; ++it2)
        s.erase(*it2);
}

void grobner::update_order() {
    update_order(m_to_process, false);
    update_order(m_processed, true);
}

bool grobner::var_lt::operator()(expr * v1, expr * v2) const {
    if (v1 == v2) return false;
    int w1 = 0;
    int w2 = 0;
    m_var2weight.find(v1, w1);
    m_var2weight.find(v2, w2);
    return (w1 > w2) || (w1 == w2 && v1->get_id() < v2->get_id());
}

bool grobner::monomial_lt::operator()(monomial * m1, monomial * m2) const {
    // Using graded lex order.
    if (m1->get_degree() > m2->get_degree())
        return true;
    if (m1->get_degree() < m2->get_degree())
        return false;
    ptr_vector<expr>::iterator it1  = m1->m_vars.begin();
    ptr_vector<expr>::iterator it2  = m2->m_vars.begin();
    ptr_vector<expr>::iterator end1 = m1->m_vars.end();
    for (; it1 != end1; ++it1, ++it2) {
        expr * v1 = *it1;
        expr * v2 = *it2;
        if (v1 == v2)
            continue;
        if (m_var_lt(v1, v2))
            return true;
        if (v1 != v2)
            return false;
    }
    return false;
}

inline void grobner::add_var(monomial * m, expr * v) {
    SASSERT(!m_util.is_numeral(v));
     m_manager.inc_ref(v);
     m->m_vars.push_back(v);
}

grobner::monomial * grobner::mk_monomial(rational const & coeff, unsigned num_vars, expr * const * vars) {
    monomial * r = alloc(monomial);
    r->m_coeff   = coeff;
    for (unsigned i = 0; i < num_vars; i++)
        add_var(r, vars[i]);
    std::stable_sort(r->m_vars.begin(), r->m_vars.end(), m_var_lt);
    return r;
}

grobner::monomial * grobner::mk_monomial(rational const & coeff, expr * m) {
    monomial * r = alloc(monomial);
    if (m_util.is_numeral(m, r->m_coeff)) {
        r->m_coeff *= coeff;
        return r;
    }
    if (m_util.is_mul(m)) {
        expr * body = m;
        SASSERT(!m_util.is_numeral(to_app(m)->get_arg(1))); // monomial is in normal form
        if (m_util.is_numeral(to_app(m)->get_arg(0), r->m_coeff)) {
            r->m_coeff *= coeff;
            body        = to_app(m)->get_arg(1);
        }
        else {
            r->m_coeff = coeff;
        }
        while (m_util.is_mul(body)) {
            add_var(r, to_app(body)->get_arg(0));
            body = to_app(body)->get_arg(1);
        }
        add_var(r, body);
        std::stable_sort(r->m_vars.begin(), r->m_vars.end(), m_var_lt);
    }
    else {
        r->m_coeff = coeff;
        r->m_vars.push_back(m);
        m_manager.inc_ref(m);
    }
    return r;
}

void grobner::init_equation(equation * eq, v_dependency * d) {
    eq->m_scope_lvl = get_scope_level();
    unsigned bidx   = m_equations_to_delete.size();
    eq->m_bidx      = bidx;
    eq->m_dep       = d;
    eq->m_lc        = true;
    m_equations_to_delete.push_back(eq);
    SASSERT(m_equations_to_delete[eq->m_bidx] == eq);
}

void grobner::assert_eq_0(unsigned num_monomials, monomial * const * monomials, v_dependency * ex) {
    ptr_vector<monomial> ms;
    ms.append(num_monomials, monomials);
    std::stable_sort(ms.begin(), ms.end(), m_monomial_lt);
    merge_monomials(ms);
    if (!ms.empty()) {
        normalize_coeff(ms);
        equation * eq       = alloc(equation); 
        eq->m_monomials.swap(ms);
        init_equation(eq, ex);                                                   
        m_to_process.insert(eq);
    }
}

void grobner::assert_eq_0(unsigned num_monomials, rational const * coeffs, expr * const * monomials, v_dependency * ex) {
#define MK_EQ(COEFF)                                    \
    ptr_vector<monomial> ms;                            \
    for (unsigned i = 0; i < num_monomials; i++)        \
        ms.push_back(mk_monomial(COEFF, monomials[i])); \
    std::stable_sort(ms.begin(), ms.end(), m_monomial_lt);     \
    merge_monomials(ms);                                \
    if (!ms.empty()) {                                  \
        equation * eq       = alloc(equation);          \
        normalize_coeff(ms);                            \
        eq->m_monomials.swap(ms);                       \
        init_equation(eq, ex);                          \
        m_to_process.insert(eq);                        \
    }

    MK_EQ(coeffs[i]);
}

void grobner::assert_eq_0(unsigned num_monomials, expr * const * monomials, v_dependency * ex) {
    rational one(1);
    MK_EQ(one);
}

void grobner::extract_monomials(expr * lhs, ptr_buffer<expr> & monomials) {
    while (m_util.is_add(lhs)) {
        SASSERT(!m_util.is_add(to_app(lhs)->get_arg(0)));
        monomials.push_back(to_app(lhs)->get_arg(0));
        lhs = to_app(lhs)->get_arg(1);
    }
    monomials.push_back(lhs);
}

void grobner::assert_eq(expr * eq, v_dependency * ex) {
    SASSERT(m_manager.is_eq(eq));
    expr * lhs = to_app(eq)->get_arg(0);
    expr * rhs = to_app(eq)->get_arg(1);
    SASSERT(m_util.is_numeral(rhs));
    ptr_buffer<expr> monomials;
    extract_monomials(lhs, monomials);
    rational c;
    bool is_int = false;
    m_util.is_numeral(rhs, c, is_int);
    expr_ref new_c(m_manager);
    if (!c.is_zero()) {
        c.neg();
        new_c = m_util.mk_numeral(c, is_int);
        monomials.push_back(new_c);
    }
    assert_eq_0(monomials.size(), monomials.c_ptr(), ex);
}

void grobner::assert_monomial_tautology(expr * m) {
    equation * eq   = alloc(equation);
    eq->m_monomials.push_back(mk_monomial(rational(1), m));
    // create (quote m)
    monomial * m1   = alloc(monomial);
    m1->m_coeff     = rational(-1);
    m_manager.inc_ref(m);
    m1->m_vars.push_back(m);
    eq->m_monomials.push_back(m1);
    normalize_coeff(eq->m_monomials);                                          
    init_equation(eq, static_cast<v_dependency*>(0));                                                          \
    m_to_process.insert(eq);
}

/**
   \brief Return true if the body of m1 and m2 are equal
*/
bool grobner::is_eq_monomial_body(monomial const * m1, monomial const * m2) {
    if (m1->get_degree() != m2->get_degree())
        return false;
    ptr_vector<expr>::const_iterator it1  = m1->m_vars.begin();
    ptr_vector<expr>::const_iterator it2  = m2->m_vars.begin();
    ptr_vector<expr>::const_iterator end1 = m1->m_vars.end();
    for (; it1 != end1; ++it1, ++it2) {
        expr * v1 = *it1;
        expr * v2 = *it2;
        if (v1 != v2)
            return false;
    }
    return true;
}

/**
   \brief Merge monomials (* c1 m) (* c2 m).
   
   \remark This method assumes the monomials are sorted.
*/
void grobner::merge_monomials(ptr_vector<monomial> & monomials) {
    TRACE("grobner", tout << "before merging monomials:\n"; display_monomials(tout, monomials.size(), monomials.c_ptr()); tout << "\n";);
    unsigned j  = 0;
    unsigned sz = monomials.size();
    if (sz == 0)
        return;
    SASSERT(&m_del_monomials != &monomials);
    ptr_vector<monomial>& to_delete = m_del_monomials;
    to_delete.reset();
    m_manager.limit().inc(sz);
    for (unsigned i = 1; i < sz; ++i) {
        monomial * m1 = monomials[j];
        monomial * m2 = monomials[i];
        if (is_eq_monomial_body(m1, m2)) {
            m1->m_coeff += m2->m_coeff;
            to_delete.push_back(m2);
        } 
        else {
            if (m1->m_coeff.is_zero())
                to_delete.push_back(m1);
            else
                j++;
            monomials[j] = m2;
        }
    }
    SASSERT(j < sz);
    monomial * m1 = monomials[j];
    if (m1->m_coeff.is_zero())
        to_delete.push_back(m1);
    else
        j++;
    monomials.shrink(j);
    del_monomials(to_delete);    
    TRACE("grobner", tout << "after merging monomials:\n"; display_monomials(tout, monomials.size(), monomials.c_ptr()); tout << "\n";);
}

/**
   \brief Divide the coefficients by the coefficient of the leading term.
*/
void grobner::normalize_coeff(ptr_vector<monomial> & monomials) {
    if (monomials.empty())
        return;
    rational c  = monomials[0]->m_coeff;
    if (c.is_one())
        return;
    unsigned sz = monomials.size();
    for (unsigned i = 0; i < sz; i++)
        monomials[i]->m_coeff /= c;
}

/**
   \brief Simplify the given monomials
*/
void grobner::simplify(ptr_vector<monomial> & monomials) {
    std::stable_sort(monomials.begin(), monomials.end(), m_monomial_lt);
    merge_monomials(monomials);
    normalize_coeff(monomials);
}

/**
   \brief Return true if the equation is of the form k = 0, where k is a numeral different from zero.
   
   \remark This method assumes the equation is simplified.
*/
inline bool grobner::is_inconsistent(equation * eq) const {
    SASSERT(!(eq->m_monomials.size() == 1 && eq->m_monomials[0]->get_degree() == 0) || !eq->m_monomials[0]->m_coeff.is_zero());
    return eq->m_monomials.size() == 1 && eq->m_monomials[0]->get_degree() == 0;
}

/**
   \brief Return true if the equation is of the form 0 = 0.
*/
inline bool grobner::is_trivial(equation * eq) const {
    return eq->m_monomials.empty();
}

/**
   \brief Sort monomials, and merge monomials with the same body.
*/
void grobner::simplify(equation * eq) {
    simplify(eq->m_monomials);
    if (is_inconsistent(eq) && !m_unsat)
        m_unsat = eq;
}

/**
   \brief Return true if monomial m1 is (* c1 M) and m2 is (* c2 M M').
   Store M' in rest.
   
   \remark This method assumes the variables of m1 and m2 are sorted.
*/
bool grobner::is_subset(monomial const * m1, monomial const * m2, ptr_vector<expr> & rest) const {
    unsigned i1  = 0;
    unsigned i2  = 0;
    unsigned sz1 = m1->m_vars.size();
    unsigned sz2 = m2->m_vars.size();
    if (sz1 <= sz2) {
        while (true) {
            if (i1 >= sz1) {
                for (; i2 < sz2; i2++) 
                    rest.push_back(m2->m_vars[i2]);
                TRACE("grobner", 
                      tout << "monomail: "; display_monomial(tout, *m1); tout << " is a subset of "; 
                      display_monomial(tout, *m2); tout << "\n";
                      tout << "rest: "; display_vars(tout, rest.size(), rest.c_ptr()); tout << "\n";);
                return true;
            }
            if (i2 >= sz2)
                break;
            expr * var1 = m1->m_vars[i1];
            expr * var2 = m2->m_vars[i2];
            if (var1 == var2) {
                i1++;
                i2++;
                continue;
            }
            if (m_var_lt(var2, var1)) {
                i2++;
                rest.push_back(var2);
                continue;
            }
            SASSERT(m_var_lt(var1, var2));
            break;
        }
    }
    // is not subset
    TRACE("grobner", tout << "monomail: "; display_monomial(tout, *m1); tout << " is not a subset of "; 
          display_monomial(tout, *m2); tout << "\n";);
    return false;
}

/**
   \brief Multiply the monomials of source starting at position start_idx by (coeff * vars), and store the resultant monomials
   at result.
*/
void grobner::mul_append(unsigned start_idx, equation const * source, rational const & coeff, ptr_vector<expr> const & vars, ptr_vector<monomial> & result) {
    unsigned sz = source->get_num_monomials();
    for (unsigned i = start_idx; i < sz; i++) {
        monomial const * m = source->get_monomial(i);
        monomial * new_m   = alloc(monomial);
        new_m->m_coeff     = m->m_coeff;
        new_m->m_coeff    *= coeff;
        new_m->m_vars.append(m->m_vars.size(), m->m_vars.c_ptr());
        new_m->m_vars.append(vars.size(), vars.c_ptr());
        ptr_vector<expr>::iterator it  = new_m->m_vars.begin();
        ptr_vector<expr>::iterator end = new_m->m_vars.end();
        for (; it != end; ++it)
            m_manager.inc_ref(*it);
        std::stable_sort(new_m->m_vars.begin(), new_m->m_vars.end(), m_var_lt);
        result.push_back(new_m);
    }
}

/**
   \brief Copy the given monomial.
*/
grobner::monomial * grobner::copy_monomial(monomial const * m) {
    monomial * r = alloc(monomial);
    r->m_coeff   = m->m_coeff;
    ptr_vector<expr>::const_iterator it  = m->m_vars.begin();
    ptr_vector<expr>::const_iterator end = m->m_vars.end();
    for (; it != end; ++it) 
        add_var(r, *it);
    return r;
}

/**
   \brief Copy the given equation.
*/
grobner::equation * grobner::copy_equation(equation const * eq) {
    equation * r   = alloc(equation);
    unsigned sz    = eq->get_num_monomials();
    for (unsigned i = 0; i < sz; i++) 
        r->m_monomials.push_back(copy_monomial(eq->get_monomial(i)));
    init_equation(r, eq->m_dep);
    r->m_lc        = eq->m_lc;
    return r;
}

/**
   \brief Simplify the target equation using the source as a rewrite rule.
   Return 0 if target was not simplified.
   Return target if target was simplified but source->m_scope_lvl <= target->m_scope_lvl.
   Return new_equation if source->m_scope_lvl > target->m_scope_lvl, moreover target is freezed, and new_equation contains the result.
*/
grobner::equation * grobner::simplify(equation const * source, equation * target) {
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *target); tout << "using: "; display_equation(tout, *source););
    if (source->get_num_monomials() == 0)
        return 0;
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
                if (source->m_scope_lvl > target->m_scope_lvl) {
                    target = copy_equation(target);
                    SASSERT(target->m_scope_lvl >= source->m_scope_lvl);
                }
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
    return result ? target : 0;
}

/**
   \brief Simplify given equation using processed equalities.
   Return 0, if the equation was not simplified.
   Return eq, if the equation was simplified using destructive updates.
   Return new_eq otherwise.
*/
grobner::equation * grobner::simplify_using_processed(equation * eq) {
    bool result = false;
    bool simplified;
    TRACE("grobner", tout << "simplifying: "; display_equation(tout, *eq); tout << "using already processed equalities\n";);
    do {
        simplified = false;
        equation_set::iterator it  = m_processed.begin();
        equation_set::iterator end = m_processed.end();
        for (; it != end; ++it) {
            equation const * p = *it;
            equation * new_eq  = simplify(p, eq);
            if (new_eq) {
                result     = true;
                simplified = true;
                eq         = new_eq;
            }
            if (m_manager.canceled()) {
                return 0;
            }
        }        
    }
    while (simplified);
    TRACE("grobner", tout << "simplification result: "; display_equation(tout, *eq););
    return result ? eq : 0;
}

/**
   \brief Return true if eq1 is a better than e2, for being the next equation to be processed.
*/
bool grobner::is_better_choice(equation * eq1, equation * eq2) {
    if (!eq2)
        return true;
    if (eq1->m_monomials.empty())
        return true;
    if (eq2->m_monomials.empty())
        return false;
    if (eq1->m_monomials[0]->get_degree() < eq2->m_monomials[0]->get_degree())
        return true;
    if (eq1->m_monomials[0]->get_degree() > eq2->m_monomials[0]->get_degree())
        return false;
    return eq1->m_monomials.size() < eq2->m_monomials.size();
}

/**
   \brief Pick next unprocessed equation
*/
grobner::equation * grobner::pick_next() {
    equation * r = 0;
    ptr_buffer<equation> to_delete;
    equation_set::iterator it  = m_to_process.begin();
    equation_set::iterator end = m_to_process.end();
    for (; it != end; ++it) {
        equation * curr     = *it;
        if (is_trivial(curr))
            to_delete.push_back(curr);
        else if (is_better_choice(curr, r))
            r = curr;
    }
    ptr_buffer<equation>::const_iterator it1  = to_delete.begin();
    ptr_buffer<equation>::const_iterator end1 = to_delete.end();
    for (; it1 != end1; ++it1)
        del_equation(*it1);
    if (r)
        m_to_process.erase(r);
    TRACE("grobner", tout << "selected equation: "; if (!r) tout << "<null>\n"; else display_equation(tout, *r););
    return r;
}

/**
   \brief Use the given equation to simplify processed terms.
*/
bool grobner::simplify_processed(equation * eq) {
    ptr_buffer<equation> to_insert;
    ptr_buffer<equation> to_remove;
    ptr_buffer<equation> to_delete;
    equation_set::iterator it  = m_processed.begin();
    equation_set::iterator end = m_processed.end();
    for (; it != end && !m_manager.canceled(); ++it) {
        equation * curr        = *it;
        m_changed_leading_term = false;
        // if the leading term is simplified, then the equation has to be moved to m_to_process
        equation * new_curr    = simplify(eq, curr);
        if (new_curr != 0) {
            if (new_curr != curr) {
                m_equations_to_unfreeze.push_back(curr);
                to_remove.push_back(curr);
                if (m_changed_leading_term) {
                    m_to_process.insert(new_curr);
                    to_remove.push_back(curr);
                }
                else {
                    to_insert.push_back(new_curr);
                }
                curr = new_curr;
            }
            else {
                if (m_changed_leading_term) {
                    m_to_process.insert(curr);
                    to_remove.push_back(curr);
                }
            }
        }
        if (is_trivial(curr))
            to_delete.push_back(curr);
    }
    ptr_buffer<equation>::const_iterator it1  = to_insert.begin();
    ptr_buffer<equation>::const_iterator end1 = to_insert.end();
    for (; it1 != end1; ++it1)
        m_processed.insert(*it1);
    it1  = to_remove.begin();
    end1 = to_remove.end();
    for (; it1 != end1; ++it1)
        m_processed.erase(*it1);
    it1  = to_delete.begin();
    end1 = to_delete.end();
    for (; it1 != end1; ++it1)
        del_equation(*it1);
    return !m_manager.canceled();
}

/**
   \brief Use the given equation to simplify to-process terms.
*/
void grobner::simplify_to_process(equation * eq) {
    equation_set::iterator it  = m_to_process.begin();
    equation_set::iterator end = m_to_process.end();
    ptr_buffer<equation> to_insert;
    ptr_buffer<equation> to_remove;
    ptr_buffer<equation> to_delete;
    for (; it != end; ++it) {
        equation * curr     = *it;
        equation * new_curr = simplify(eq, curr);
        if (new_curr != 0 && new_curr != curr) {
            m_equations_to_unfreeze.push_back(curr);
            to_insert.push_back(new_curr);
            to_remove.push_back(curr);
            curr = new_curr;
        }
        if (is_trivial(curr))
            to_delete.push_back(curr);
    }
    ptr_buffer<equation>::const_iterator it1  = to_insert.begin();
    ptr_buffer<equation>::const_iterator end1 = to_insert.end();
    for (; it1 != end1; ++it1)
        m_to_process.insert(*it1);
    it1  = to_remove.begin();
    end1 = to_remove.end();
    for (; it1 != end1; ++it1)
        m_to_process.erase(*it1);
    it1  = to_delete.begin();
    end1 = to_delete.end();
    for (; it1 != end1; ++it1)
        del_equation(*it1);
}

/**
   \brief If m1 = (* c M M1) and m2 = (* d M M2) and M is non empty, then return true and store M1 in rest1 and M2 in rest2.
*/
bool grobner::unify(monomial const * m1, monomial const * m2, ptr_vector<expr> & rest1, ptr_vector<expr> & rest2) {
    TRACE("grobner", tout << "unifying: "; display_monomial(tout, *m1); tout << " "; display_monomial(tout, *m2); tout << "\n";);
    bool found_M = false;
    unsigned i1  = 0;
    unsigned i2  = 0;
    unsigned sz1 = m1->m_vars.size();
    unsigned sz2 = m2->m_vars.size();
    while (true) {
        if (i1 >= sz1) {
            if (found_M) {
                for (; i2 < sz2; i2++) 
                    rest2.push_back(m2->m_vars[i2]);
                return true;
            }
            return false;
        }
        if (i2 >= sz2) {
            if (found_M) {
                for (; i1 < sz1; i1++) 
                    rest1.push_back(m1->m_vars[i1]);
                return true;
            }
            return false;
        }
        expr * var1 = m1->m_vars[i1];
        expr * var2 = m2->m_vars[i2];
        if (var1 == var2) {
            found_M = true;
            i1++;
            i2++;
        }
        else if (m_var_lt(var2, var1)) {
            i2++;
            rest2.push_back(var2);
        }
        else {
            i1++;
            rest1.push_back(var1);
        }
    }
}

/**
   \brief Superpose the given two equations.
*/
void grobner::superpose(equation * eq1, equation * eq2) {
    if (eq1->m_monomials.empty() || eq2->m_monomials.empty())
        return;
    m_stats.m_superpose++;
    ptr_vector<expr> & rest1 = m_tmp_vars1;
    rest1.reset();
    ptr_vector<expr> & rest2 = m_tmp_vars2;
    rest2.reset();
    if (unify(eq1->m_monomials[0], eq2->m_monomials[0], rest1, rest2)) {
        TRACE("grobner", tout << "superposing:\n"; display_equation(tout, *eq1); display_equation(tout, *eq2); 
              tout << "rest1: "; display_vars(tout, rest1.size(), rest1.c_ptr()); tout << "\n";
              tout << "rest2: "; display_vars(tout, rest2.size(), rest2.c_ptr()); tout << "\n";);
        ptr_vector<monomial> & new_monomials = m_tmp_monomials;
        new_monomials.reset();
        mul_append(1, eq1, eq2->m_monomials[0]->m_coeff, rest2, new_monomials);
        rational c = eq1->m_monomials[0]->m_coeff;
        c.neg();
        mul_append(1, eq2, c, rest1, new_monomials);
        simplify(new_monomials);
        TRACE("grobner", tout << "resulting monomials: "; display_monomials(tout, new_monomials.size(), new_monomials.c_ptr()); tout << "\n";);
        if (new_monomials.empty())
            return;
        m_num_new_equations++;
        equation * new_eq = alloc(equation);
        new_eq->m_monomials.swap(new_monomials);
        init_equation(new_eq, m_dep_manager.mk_join(eq1->m_dep, eq2->m_dep));
        new_eq->m_lc = false;
        m_to_process.insert(new_eq);
    }
}

/**
   \brief Superpose the given equations with the equations in m_processed.
*/
void grobner::superpose(equation * eq) {
    equation_set::iterator it  = m_processed.begin();
    equation_set::iterator end = m_processed.end();
    for (; it != end; ++it) {
        equation * curr        = *it;
        superpose(eq, curr);
    }
}

void grobner::compute_basis_init() {
    m_stats.m_compute_basis++;
    m_num_new_equations = 0;
}

bool grobner::compute_basis_step() {
    equation * eq = pick_next();
    if (!eq)
        return true;
    m_stats.m_num_processed++;
#ifdef PROFILE_GB
    if (m_stats.m_num_processed % 100 == 0) {
        verbose_stream() << "[grobner] " << m_processed.size() << " " << m_to_process.size() << "\n";
    }
#endif
    equation * new_eq = simplify_using_processed(eq);
    if (new_eq != 0 && eq != new_eq) {
        // equation was updated using non destructive updates
        m_equations_to_unfreeze.push_back(eq);
        eq = new_eq;
    }
    if (m_manager.canceled()) return false;
    if (!simplify_processed(eq)) return false;
    superpose(eq);
    m_processed.insert(eq);
    simplify_to_process(eq);
    TRACE("grobner", tout << "end of iteration:\n"; display(tout););
    return false;
}

bool grobner::compute_basis(unsigned threshold) {
    compute_basis_init();
    while (m_num_new_equations < threshold && !m_manager.canceled()) {
        if (compute_basis_step()) return true;
    }
    return false;
}

void grobner::copy_to(equation_set const & s, ptr_vector<equation> & result) const {
    equation_set::iterator it  = s.begin();
    equation_set::iterator end = s.end();
    for (; it != end; ++it)
        result.push_back(*it);
}

/**
   \brief Copy the equations in m_processed and m_to_process to result.
   
   \warning This equations can be deleted when compute_basis is invoked.
*/
void grobner::get_equations(ptr_vector<equation> & result) const {
    copy_to(m_processed, result);
    copy_to(m_to_process, result);
}

