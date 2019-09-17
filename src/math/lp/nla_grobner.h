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

#include "math/lp/nla_common.h"
#include "math/lp/nex.h"
#include "util/dependency.h"

namespace nla {
class core;

struct grobner_stats {
    long m_simplify;
    long m_superpose;
    long m_compute_basis;
    long m_num_processed;
    void reset() { memset(this, 0, sizeof(grobner_stats)); }
    grobner_stats() { reset(); }
};


class equation {
    unsigned             m_scope_lvl;     //!< scope level when this equation was created.
    unsigned             m_bidx:31;       //!< position at m_equations_to_delete
    unsigned             m_lc:1;          //!< true if equation if a linear combination of the input equations.
    ptr_vector<monomial> m_monomials;     //!< sorted monomials
    v_dependency *         m_dep;           //!< justification for the equality
    friend class grobner;
    equation() {}
public:
    unsigned get_num_monomials() const { return m_monomials.size(); }
    monomial const * get_monomial(unsigned idx) const { return m_monomials[idx]; }
    monomial * const * get_monomials() const { return m_monomials.c_ptr(); }
    v_dependency * get_dependency() const { return m_dep; }
    unsigned hash() const { return m_bidx; }
    bool is_linear_combination() const { return m_lc; }
};

enum class var_weight {
        FIXED = 0,
            QUOTED_FIXED =  1,
            BOUNDED    =    2,
            QUOTED_BOUNDED = 3,
            NOT_FREE      =  4,
            QUOTED_NOT_FREE = 5,
            FREE          =   6,
            QUOTED_FREE    = 7,
            MAX_DEFAULT_WEIGHT = 7
            };

class nla_grobner : common {
    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;
    equation_vector         m_equations_to_unfreeze;
    equation_vector         m_equations_to_delete;
    
    lp::int_set         m_rows;
    lp::int_set         m_active_vars;
    svector<var_weight> m_active_vars_weights;
    unsigned            m_num_of_equations;
    grobner_stats       m_stats;
    equation_set            m_processed;
    equation_set            m_to_process;
public:
    nla_grobner(core *core);
    void grobner_lemmas();
private:
    void find_nl_cluster();
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  std::queue<lpvar>& q);
    void display(std::ostream&);
    void set_active_vars_weights();
    void init();
    var_weight get_var_weight(lpvar) const;
    void compute_basis();
    void update_statistics();
    bool find_conflict();
    bool push_calculation_forward();
    void compute_basis_init();        
    bool compute_basis_loop();
    bool compute_basis_step();
    equation* simplify_using_processed(equation*);
    equation* simplify_processed(equation*);
    equation* simplify_to_process(equation*);
    equation* pick_next();
    void set_gb_exhausted();
    bool canceled() { return false; } // todo, implement
    void superpose(equation * eq1, equation * eq2);
    void superpose(equation * eq);
}; // end of grobner
}
