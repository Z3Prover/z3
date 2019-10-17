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
        unsigned                   m_bidx:31;       //!< position at m_equations_to_delete
        unsigned                   m_lc:1;          //!< true if equation if a linear combination of the input equations.
        nex *                      m_expr;           //  simplified expressionted monomials
        ci_dependency *            m_dep;           //!< justification for the equality
        friend class nla_grobner;
        equation() {}
    public:
        unsigned get_num_monomials() const {
            switch(m_expr->type()) {
            case expr_type::VAR:
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
        ci_dependency * get_dependency() const { return m_dep; }
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
    bool                                         m_changed_leading_term;
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
    equation * simplify_source_target(equation const * source, equation * target);
    equation* simplify_using_processed(equation*);
    unsigned simplify_loop_on_target_monomials(equation const * source, equation * target, bool & result);
    void process_simplified_target(ptr_buffer<equation>& to_insert, equation* new_target, equation*& target, ptr_buffer<equation>& to_remove);
bool simplify_processed_with_eq(equation*);
    void simplify_to_process(equation*);
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
    std::ostream& display_equation(std::ostream & out, const equation & eq);

    void display(std::ostream & out) const;
    void get_equations(ptr_vector<equation>& eqs);
    bool try_to_modify_eqs(ptr_vector<equation>& eqs, unsigned& next_weight);
    bool internalize_gb_eq(equation*);
    void add_row(unsigned);
    void assert_eq_0(nex*, ci_dependency * dep);
    void process_var(nex_mul*, lpvar j, ci_dependency *& dep, rational&);

    nex* mk_monomial_in_row(rational, lpvar, ci_dependency*&);

    
    void init_equation(equation* eq, nex*, ci_dependency* d);
    equation * simplify(equation const * source, equation * target);    
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
    
    std::ostream& display_dependency(std::ostream& out, ci_dependency*);
    void insert_to_process(equation *eq) { m_to_process.insert(eq); }
    void simplify_equations_to_process();
}; // end of grobner
}
