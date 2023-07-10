/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
   Lev Nachmanson (levnach)
   Nikolaj Bjorner (nbjorner)

  --*/
#pragma once
#include "util/rational.h"
#include "math/lp/nla_defs.h"
#include "math/lp/lar_term.h"
#include "math/lp/monic.h"
#include "math/lp/emonics.h"
#include "math/lp/factorization.h"
#include "util/dependency.h"
#include "util/region.h"
#include "math/lp/nex_creator.h"
namespace nla {


inline llc negate(llc cmp) {
    switch(cmp) {
    case llc::LE: return llc::GT;
    case llc::LT: return llc::GE;
    case llc::GE: return llc::LT;
    case llc::GT: return llc::LE;
    case llc::EQ: return llc::NE;
    case llc::NE: return llc::EQ;
    default: SASSERT(false);
    };
    return cmp; // not reachable
}

inline llc swap_side(llc cmp) {
    switch(cmp) {
    case llc::LE: return llc::GE;
    case llc::LT: return llc::GT;
    case llc::GE: return llc::LE;
    case llc::GT: return llc::LT;
    case llc::EQ: return llc::EQ;
    case llc::NE: return llc::NE;
    default: SASSERT(false);
    };
    return cmp; // not reachable
}

class core;
class intervals;
struct common {
    core&                                        m_core;
    nex_creator                                  m_nex_creator;
    
    common(core* c): m_core(*c) {}
    core& c() { return m_core; }
    const core& c() const { return m_core; }
    core& _() { return m_core; }
    const core& _() const { return m_core; }

    template <typename T> rational val(T const& t) const;
    rational val(lpvar) const;
    rational var_val(monic const& m) const; // value obtained from variable representing monomial
    rational mul_val(monic const& m) const; // value obtained from multiplying variables of monomial
    template <typename T> lpvar var(T const& t) const;
    // this needed in can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based when iterating
    // over a monic
    lpvar var(lpvar j) const { return j; }
    bool done() const;
    template <typename T> bool canonize_sign(const T&) const;

    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const;

    std::ostream& print_factor(const factor &, std::ostream& out) const;
    std::ostream& print_var(lpvar, std::ostream& out) const;
    
    std::ostream& print_monic(const monic & m, std::ostream& out) const;
    std::ostream& print_rooted_monic(const monic &, std::ostream& out) const;
    std::ostream& print_rooted_monic_with_vars(const monic&, std::ostream& out) const;
    bool check_monic(const monic&) const;
    unsigned random();
    void add_deps_of_fixed(lpvar j, u_dependency*& dep);
    class ci_value_manager {
    public:
        void inc_ref(lp::constraint_index const & v) {
        }

        void dec_ref(lp::constraint_index const & v) {
        }
    };

    struct u_dependency_config {
        typedef ci_value_manager        value_manager;
        typedef region  allocator;
        static const bool ref_count = false;
        typedef lp::constraint_index value;
    };
        
    nex* nexvar(const rational& coeff, lpvar j, nex_creator&, u_dependency*&);
    template <typename T>
    void create_sum_from_row(const T&, nex_creator&, nex_creator::sum_factory&, u_dependency*&);
};
}
