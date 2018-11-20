#include "util/vector.h"
#include "util/lp/factorization.h"
namespace nla {

void const_iterator_mon::init_vars_by_the_mask(unsigned_vector & k_vars, unsigned_vector & j_vars) const {
    // the last element for m_factorization.m_rooted_vars goes to k_vars
    SASSERT(m_mask.size() + 1  == m_ff->m_cmon.vars().size());
    k_vars.push_back(m_ff->m_cmon.vars().back()); 
    for (unsigned j = 0; j < m_mask.size(); j++) {
        if (m_mask[j]) {
            k_vars.push_back(m_ff->m_cmon.vars()[j]);
        } else {
            j_vars.push_back(m_ff->m_cmon.vars()[j]);
        }
    }
}
            
bool const_iterator_mon::get_factors(unsigned& k, unsigned& j, rational& sign) const {
    unsigned_vector k_vars;
    unsigned_vector j_vars;
    init_vars_by_the_mask(k_vars, j_vars);
    SASSERT(!k_vars.empty() && !j_vars.empty());
    std::sort(k_vars.begin(), k_vars.end());
    std::sort(j_vars.begin(), j_vars.end());

    rational k_sign, j_sign;
    monomial m;
    if (k_vars.size() == 1) {
        k = k_vars[0];
        k_sign = 1;
    } else {
        if (!m_ff->find_monomial_of_vars(k_vars, m, k_sign)) {
            return false;
        }
        k = m.var();
    }
    if (j_vars.size() == 1) {
        j = j_vars[0];
        j_sign = 1;
    } else {
        if (!m_ff->find_monomial_of_vars(j_vars, m, j_sign)) {
            return false;
        }
        j = m.var();
    }
    sign = j_sign * k_sign;
    return true;
}

const_iterator_mon::reference const_iterator_mon::operator*() const {
    if (m_full_factorization_returned == false)  {
        return create_full_factorization();
    }
    unsigned j, k; rational sign;
    if (!get_factors(j, k, sign))
        return factorization();
    return create_binary_factorization(j, k, m_ff->m_cmon.coeff() * sign);
}
            
void const_iterator_mon::advance_mask() {
    if (!m_full_factorization_returned) {
        m_full_factorization_returned = true;
        return;
    }
    for (bool& m : m_mask) {
        if (m) {
            m = false;
        }
        else {
            m = true;
            break;
        }
    }
}

            
const_iterator_mon::self_type const_iterator_mon::operator++() {  self_type i = *this; operator++(1); return i;  }
const_iterator_mon::self_type const_iterator_mon::operator++(int) { advance_mask(); return *this; }

const_iterator_mon::const_iterator_mon(const svector<bool>& mask, const factorization_factory *f) : 
    m_mask(mask),
    m_ff(f) ,
    m_full_factorization_returned(false)
{}
            
bool const_iterator_mon::operator==(const const_iterator_mon::self_type &other) const {
    return
        m_full_factorization_returned == other.m_full_factorization_returned &&
        m_mask == other.m_mask;
}
bool const_iterator_mon::operator!=(const const_iterator_mon::self_type &other) const { return !(*this == other); }
            
factorization const_iterator_mon::create_binary_factorization(lpvar j, lpvar k, rational const& sign) const {
    // todo : the current explanation is an overkill
    // std::function<void (expl_set&)> explain = [&](expl_set& exp){
    //                                               const imp & impl = m_ff->m_impf;
    //                                               unsigned mon_index = 0;
    //                                               if (impl.m_var_to_its_monomial.find(k, mon_index)) {
    //                                                   impl.add_explanation_of_reducing_to_rooted_monomial(impl.m_monomials[mon_index], exp);
    //                                               }
    //                                               if (impl.m_var_to_its_monomial.find(j, mon_index)) {
    //                                                   impl.add_explanation_of_reducing_to_rooted_monomial(impl.m_monomials[mon_index], exp);
    //                                               }

    //                                               impl.add_explanation_of_reducing_to_rooted_monomial(m_ff->m_mon, exp);
    //                                           };
    factorization f;
    f.vars().push_back(j);
    f.vars().push_back(k);
    f.sign() = sign;
    return f;
}

factorization const_iterator_mon::create_full_factorization() const {
    factorization f;
    f.vars() = m_ff->m_mon.vars();
    f.sign() = rational(1);
    return f;
}
}

