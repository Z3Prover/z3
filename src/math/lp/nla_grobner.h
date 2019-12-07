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
//#include "util/dependency.h"

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
    class equation {
        unsigned                   m_bidx;       //!< position at m_equations_to_delete

        nex *                      m_expr;           //  simplified expressionted monomials
        ci_dependency *            m_dep;           //!< justification for the equality
    public:
        unsigned get_num_monomials() const {
            switch(m_expr->type()) {
            case expr_type::VAR: return 1;
            case expr_type::SCALAR: return 0;
            case expr_type::MUL: return 1;
            case expr_type::SUM: return m_expr->size();
            default: return 0;
            }
        }
        // can return not a nex_mul
        nex* get_monomial(unsigned idx) const {
            switch(m_expr->type()) {
            case expr_type::VAR:
            case expr_type::SCALAR: UNREACHABLE();;
            case expr_type::MUL:
                SASSERT(idx == 0);
                return m_expr;
            case expr_type::SUM:
                return (*to_sum(m_expr))[idx];
            default: return 0;
            }
        }
        nex* & exp() { return m_expr; }
        const nex*  exp() const { return m_expr; }
        ci_dependency * dep() const { return m_dep; }
        ci_dependency *& dep() { return m_dep; }
        unsigned hash() const { return m_bidx; }
        friend class nla_grobner;
    };

    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;
    
    // fields
    equation_vector                              m_equations_to_delete;    
    lp::int_set                                  m_rows;
    unsigned                                     m_num_of_equations;
    grobner_stats                                m_stats;
    equation_set                                 m_to_superpose;
    equation_set                                 m_to_simplify;
    bool                                         m_nl_gb_exhausted;
    ptr_vector<nex>                              m_allocated;
    lp::int_set                                  m_tmp_var_set;
    region                                       m_alloc;
    ci_value_manager                             m_val_manager;
    mutable ci_dependency_manager                m_dep_manager;
    nex_lt                                       m_lt;
    bool                                         m_changed_leading_term;
    unsigned                                     m_reported;
    bool                                         m_conflict;
    bool                                         m_look_for_fixed_vars_in_rows;
public:
    nla_grobner(core *core, intervals *);
    void grobner_lemmas();
    ~nla_grobner();
private:
    void find_nl_cluster();
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  std::queue<lpvar>& q);
    void init();
    void compute_basis();
    void update_statistics();
    bool find_conflict(ptr_vector<equation>& eqs);
    bool is_inconsistent(equation*);
    bool push_calculation_forward(ptr_vector<equation>& eqs, unsigned&);
    void compute_basis_init();        
    bool compute_basis_loop();
    bool compute_basis_step();
    bool simplify_source_target(equation * source, equation * target);
    equation* simplify_using_to_superpose(equation*);
    bool simplify_target_monomials(equation * source, equation * target);
    void process_simplified_target(equation* target, ptr_buffer<equation>& to_remove);    
    bool simplify_to_superpose_with_eq(equation*);
    void simplify_m_to_simplify(equation*);
    equation* pick_next();
    void set_gb_exhausted();
    bool canceled() const;
    void superpose(equation * eq1, equation * eq2);
    void superpose(equation * eq);
    bool find_b_c(const nex *ab, const nex* ac, nex_mul*& b, nex_mul*& c);
    bool find_b_c_check_only(const nex* ab, const nex* ac) const;
    bool is_trivial(equation* ) const; 
    bool is_better_choice(equation * eq1, equation * eq2);
    void del_equations(unsigned old_size);
    void del_equation(equation * eq);
    void display_equations(std::ostream & out, equation_set const & v, char const * header) const;
    std::ostream& display_equation(std::ostream & out, const equation & eq) const;

    void display_matrix(std::ostream & out) const;
    std::ostream& display(std::ostream & out) const;
    void get_equations(ptr_vector<equation>& eqs);
    bool try_to_modify_eqs(ptr_vector<equation>& eqs, unsigned& next_weight);
    bool internalize_gb_eq(equation*);
    void add_row(unsigned);
    void assert_eq_0(nex*, ci_dependency * dep);
    void init_equation(equation* eq, nex*, ci_dependency* d);
    
    std::ostream& display_dependency(std::ostream& out, ci_dependency*) const;
    void insert_to_simplify(equation *eq) {
        TRACE("nla_grobner", display_equation(tout, *eq););
        m_to_simplify.insert(eq);
    }
    void insert_to_superpose(equation *eq) {
        SASSERT(m_nex_creator.is_simplified(eq->exp()));
        TRACE("nla_grobner", display_equation(tout, *eq););
        m_to_superpose.insert(eq);
    }
    void simplify_equations_in_m_to_simplify();
    const nex * get_highest_monomial(const nex * e) const;
    ci_dependency* dep_from_vector( svector<lp::constraint_index> & fixed_vars_constraints);
    bool simplify_target_monomials_sum(equation *, equation *, nex_sum*, const nex*);    
    unsigned find_divisible(nex_sum*, const nex*) const;    
    void simplify_target_monomials_sum_j(equation *, equation *, nex_sum*, const nex*, unsigned);
    nex_mul * divide_ignore_coeffs(nex* ej, const nex*);
    bool divide_ignore_coeffs_check_only(nex* , const nex*) const;
    bool divide_ignore_coeffs_check_only_nex_mul(nex_mul* , const nex*) const;
    nex_mul * divide_ignore_coeffs_perform(nex* , const nex*);
    nex_mul * divide_ignore_coeffs_perform_nex_mul(nex_mul* , const nex*);
    nex * expr_superpose(nex* e1, nex* e2, const nex* ab, const nex* ac, nex_mul* b, nex_mul* c);
    void add_mul_skip_first(nex_sum* r, const rational& beta, nex *e, nex_mul* c);
    bool done() const;
    void check_eq(equation*);
    void register_report();
    std::unordered_set<lpvar> get_vars_of_expr_with_opening_terms(const nex *e );
}; // end of grobner
}
