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
#pragma once
#include "math/lp/lp_types.h"
#include "math/lp/column_info.h"
#include "math/lp/explanation.h"

namespace nla {
typedef lp::constraint_index lpci;
typedef lp::lconstraint_kind llc;
typedef lp::constraint_index     lpci;
typedef lp::explanation          expl_set;
typedef lp::var_index            lpvar;

struct from_index_dummy{};
class signed_var {
    unsigned m_sv;
public:
    // constructor, sign = true means minus
    signed_var(lpvar v, bool sign): m_sv((v << 1) + (sign ? 1 : 0)) {}
    explicit signed_var(unsigned sv) : m_sv(sv) {}
    // constructor
    bool sign() const { return 0 != (m_sv & 0x1); }
    lpvar var() const { return m_sv >> 1; }
    unsigned index() const { return m_sv; }        
    void neg() { m_sv = m_sv ^ 1; }
    friend signed_var operator~(signed_var const& sv) {
        return signed_var(sv.var(), !sv.sign());
    }
    bool operator==(signed_var const& other) const {
        return m_sv == other.m_sv;
    }
    bool operator!=(signed_var const& other) const {
        return m_sv != other.m_sv;
    }
    rational rsign() const { return sign() ? rational::minus_one() : rational::one(); }

    std::ostream& display(std::ostream& out) const {
        return out << (sign()?"-":"") << var();
    }
};

inline std::ostream& operator<<(std::ostream& out, signed_var const& sv) { return sv.display(out); }

/*
 *  represents definition m_v = coeff* v1*v2*...*vn, 
 *  where m_vs = [v1, v2, .., vn]
 */
class monic_coeff  {
    svector<lp::var_index> m_vs;
    rational m_coeff;
public:
    monic_coeff(const svector<lp::var_index>& vs, rational const& coeff): m_vs(vs), m_coeff(coeff) {}
    rational const& coeff() const { return m_coeff; }
    const svector<lp::var_index> & vars() const { return m_vs; } 
};
template <typename T> bool has_zero(const T& product) {
    for (const rational & t : product) {
        if (t.is_zero())
            return true;
    }
    return false;
}
template <typename T>
bool uniform_le(const T& a, const T& b,  unsigned & strict_i) {
    SASSERT(a.size() == b.size());
    strict_i = -1;
    bool z_b = false;
        
    for (unsigned i = 0; i < a.size(); i++) {
        if (a[i] > b[i]){
            return false;
        }
            
        SASSERT(!a[i].is_neg());
        if (a[i] < b[i]){
            strict_i = i;
        } else if (b[i].is_zero()) {
            z_b = true;
        }
    }
    if (z_b) {strict_i = -1;}
    return true;
}
inline rational sign_to_rat(bool s) { return rational(s? -1 : 1); }
}
