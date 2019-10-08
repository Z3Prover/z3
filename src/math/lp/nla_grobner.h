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
#include "math/lp/nex_creator.h"
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


class nla_grobner : common {

    struct monomial {
        rational         m_coeff;
        svector<lpvar>   m_vars;  //!< sorted variables
    
        friend class grobner;
        friend struct monomial_lt;
    
        monomial() {}
    public:
        rational const & get_coeff() const { return m_coeff; }
        unsigned get_degree() const { return m_vars.size(); }
        unsigned get_size() const { return get_degree(); }
        lpvar    get_var(unsigned idx) const { return m_vars[idx]; }
    };

    class equation {
        unsigned             m_scope_lvl;     //!< scope level when this equation was created.
        unsigned             m_bidx:31;       //!< position at m_equations_to_delete
        unsigned             m_lc:1;          //!< true if equation if a linear combination of the input equations.
        ptr_vector<monomial> m_monomials;     //!< sorted monomials
        v_dependency *       m_dep;           //!< justification for the equality
        friend class nla_grobner;
        equation() {}
    public:
        unsigned get_num_monomials() const { return m_monomials.size(); }
        monomial const * get_monomial(unsigned idx) const { return m_monomials[idx]; }
        monomial * const * get_monomials() const { return m_monomials.c_ptr(); }
        v_dependency * get_dependency() const { return m_dep; }
        unsigned hash() const { return m_bidx; }
        bool is_linear_combination() const { return m_lc; }
    };

    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;
    
    // fields
    equation_vector                              m_equations_to_unfreeze;
    equation_vector                              m_equations_to_delete;    
    lp::int_set                                  m_rows;
    lp::int_set                                  m_active_vars;
    unsigned                                     m_num_of_equations;
    grobner_stats                                m_stats;
    equation_set                                 m_processed;
    equation_set                                 m_to_process;
    bool                                         m_nl_gb_exhausted;
    ptr_vector<nex>                              m_allocated;
    lp::int_set                                  m_tmp_var_set;
    region                                       m_alloc;
    ci_value_manager                             m_val_manager;
    ci_dependency_manager                        m_dep_manager;
    nex_lt                                       m_lt;
public:
    nla_grobner(core *core);
    void grobner_lemmas();
private:
    bool scan_for_linear(ptr_vector<equation>& eqs);
    void find_nl_cluster();
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  std::queue<lpvar>& q);
    void display(std::ostream&);
    void init();
    void compute_basis();
    void update_statistics();
    bool find_conflict(ptr_vector<equation>& eqs);
    bool is_inconsistent(equation*);
    bool is_inconsistent2(equation*);
    bool push_calculation_forward(ptr_vector<equation>& eqs, unsigned&);
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
    bool is_trivial(equation* ) const; 
    bool is_better_choice(equation * eq1, equation * eq2);
    void del_equations(unsigned old_size);
    void del_equation(equation * eq);
    void display_equations(std::ostream & out, equation_set const & v, char const * header) const;
    void display_equation(std::ostream & out, equation const & eq) const;

    void display_monomial(std::ostream & out, monomial const & m) const;

    void display(std::ostream & out) const;
    void get_equations(ptr_vector<equation>& eqs);
    bool try_to_modify_eqs(ptr_vector<equation>& eqs, unsigned& next_weight);
    bool internalize_gb_eq(equation*);
    void add_row(unsigned);
    void assert_eq_0(const nex*, ci_dependency * dep);
    void process_var(nex_mul*, lpvar j, ci_dependency *& dep, rational&);

    nex* mk_monomial_in_row(rational, lpvar, ci_dependency*&);
    rational get_monomial_coeff(const nex_mul* m) {        
        const nex* a = m->children()[0].e();
        if (a->is_scalar())
            return static_cast<const nex_scalar*>(a)->value();
        return rational(1);
    }

    void init_equation(equation* eq, ci_dependency* d);
    
    // bool less_than_on_vars(lpvar a, lpvar b) const {
    //     const auto &aw = m_nex_creatorm_active_vars_weights[a];
    //     const auto &ab = m_active_vars_weights[b];
    //     if (aw < ab)
    //         return true;
    //     if (aw > ab)
    //         return false;
    //     // aw == ab
    //     return a < b;
    // }

    // bool less_than_on_expr(const nex* a, const nex* b) const {
    //     lt_on_vars lt = [this](lpvar j, lpvar k) {return less_than_on_vars(j, k);};
    //     return less_than_nex(a, b, lt);
    // }
    
    
}; // end of grobner
}
