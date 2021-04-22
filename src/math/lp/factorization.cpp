#include "util/vector.h"
#include "math/lp/factorization.h"
namespace nla {

void const_iterator_mon::init_vars_by_the_mask(unsigned_vector & k_vars, unsigned_vector & j_vars) const {
    // the last element for m_factorization.m_rooted_vars goes to k_vars
    SASSERT(m_mask.size() + 1  == m_ff->m_vars.size());
    k_vars.push_back(m_ff->m_vars.back()); 
    for (unsigned j = 0; j < m_mask.size(); j++) {
        if (m_mask[j]) {
            k_vars.push_back(m_ff->m_vars[j]);
        } else {
            j_vars.push_back(m_ff->m_vars[j]);
        }
    }
}
// todo : do we need the sign?
bool const_iterator_mon::get_factors(factor& k, factor& j, rational& sign) const {
    unsigned_vector k_vars;
    unsigned_vector j_vars;
    init_vars_by_the_mask(k_vars, j_vars);
    SASSERT(!k_vars.empty() && !j_vars.empty());
    std::sort(k_vars.begin(), k_vars.end());
    std::sort(j_vars.begin(), j_vars.end());

    if (false && m_num_failures > 10) {
        for (bool& m : m_mask) m = true;
        m_mask[0] = false;
        m_full_factorization_returned = true;
        return false;
    }
    if (k_vars.size() == 1) {
        k.set(k_vars[0], factor_type::VAR);
    } else {
        unsigned i;
        if (!m_ff->find_canonical_monic_of_vars(k_vars, i)) {
            ++m_num_failures;
            return false;
        }
        k.set(i, factor_type::MON);
    }
    m_num_failures = 0;

    if (j_vars.size() == 1) {
        j.set(j_vars[0], factor_type::VAR);
    } else {
        unsigned i;
        if (!m_ff->find_canonical_monic_of_vars(j_vars, i)) {
            ++m_num_failures;
            return false;
        }
        j.set(i, factor_type::MON);
    }
    return true;
}

factorization const_iterator_mon::operator*() const {
    if (!m_full_factorization_returned)  {
        return create_full_factorization(m_ff->m_monic);
    }
    factor j, k; rational sign;
    if (!get_factors(j, k, sign))
        return factorization(nullptr);
    return create_binary_factorization(j, k);
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

const_iterator_mon::const_iterator_mon(const bool_vector& mask, const factorization_factory *f) : 
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
            
factorization const_iterator_mon::create_binary_factorization(factor j, factor k) const {
    factorization f(nullptr);
    f.push_back(j);
    f.push_back(k);
    // Let m by *m_ff->m_monic, the monic we factorize
    // We have canonize_sign(m)*m.vars() = m.rvars()
    // Let s = canonize_sign(f). Then we have f[0]*f[1] = s*m.rvars()
    // s*canonize_sign(m)*val(m).
    // Therefore val(m) = sign*val((f[0])*val(f[1]), where sign = canonize_sign(f)*canonize_sign(m).
    // We apply this sign to the first factor.
    f[0].sign() ^= (m_ff->canonize_sign(f)^m_ff->canonize_sign(*m_ff->m_monic));
    return f;
}

factorization const_iterator_mon::create_full_factorization(const monic* m) const {
    if (m != nullptr)
        return factorization(m);
    factorization f(nullptr);
    for (lpvar j : m_ff->m_vars) {
        f.push_back(factor(j, factor_type::VAR));
    }
    return f;
}

}

