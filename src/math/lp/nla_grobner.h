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

namespace nla {
class core;

struct grobner_stats {
    long m_simplified;
    long m_superposed;
    long m_compute_steps;
    unsigned m_max_expr_size;
    unsigned m_max_expr_degree;
    void reset() { memset(this, 0, sizeof(grobner_stats)); }
    grobner_stats() { reset(); }
};

template <typename A, typename B, typename C>
class concat {    
    const A& m_a; // the first container
    const B& m_b; // the second container    
public:
    class iterator {
        const concat& m_c;
        typename A::iterator m_a_it;
        typename B::iterator m_b_it;
    public:
        iterator(const concat& c, bool begin):
            m_c(c), m_a_it(begin? m_c.m_a.begin() : m_c.m_a.end()), m_b_it(begin? m_c.m_b.begin() : m_c.m_b.end()) {}
        const C operator*() { return m_a_it != m_c.m_a.end() ? *m_a_it : *m_b_it; }
        iterator& operator++() {
            if (m_a_it != m_c.m_a.end())
                m_a_it++;
            else
                m_b_it++;
            return *this;
        }
        iterator operator++(int) { iterator tmp = *this; ++*this; return tmp; }
        bool operator==(iterator const& other) const { return m_a_it == other.m_a_it && m_b_it == other.m_b_it; }
        bool operator!=(iterator const& other) const { return m_a_it != other.m_a_it || m_b_it != other.m_b_it; }
    };

    concat(const A& a, const B& b) : m_a(a), m_b(b) {}
    iterator begin() { return iterator(*this, true); }
    iterator end() { return iterator(*this, false); }

};

class grobner_core {
public:
    struct params {
        unsigned                                 m_grobner_eqs_threshold;
        unsigned                                 m_expr_size_limit;
    };

    class equation {
        unsigned                   m_bidx;       //!< position at m_equations_to_delete
        nex *                      m_expr;       //   simplified expressionted monomials
        u_dependency *    m_dep;        //!< justification for the equality
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
        // not guaranteed to return a nex_mul
        nex const* get_monomial(unsigned idx) const {
            switch(m_expr->type()) {
            case expr_type::VAR:
            case expr_type::SCALAR: UNREACHABLE();;
            case expr_type::MUL:
                SASSERT(idx == 0);
                return m_expr;
            case expr_type::SUM:
                return m_expr->to_sum()[idx];
            default: return nullptr;
            }
        }
        const nex* expr() const { return m_expr; }
        u_dependency * dep() const { return m_dep; }
        unsigned hash() const { return m_bidx; }
        friend class grobner_core;
    };
private:
    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;
    typedef std::function<void (lp::explanation const& e, std::ostream& out)> print_expl_t;
    // fields
    nex_creator&                                 m_nex_creator;
    reslimit&                                    m_limit;
    print_expl_t                                 m_print_explanation;
    equation_vector                              m_equations_to_delete;    
    grobner_stats                                m_stats;
    equation_set                                 m_to_superpose;
    equation_set                                 m_to_simplify;
    region                                       m_alloc;
    mutable u_dependency_manager                 m_dep_manager;
    nex_lt                                       m_lt;
    bool                                         m_changed_leading_term;
    params                                       m_params;

public:
    grobner_core(nex_creator& nc, reslimit& lim) : 
        m_nex_creator(nc), 
        m_limit(lim), 
        m_dep_manager(),
        m_changed_leading_term(false)
    {}

    ~grobner_core();
    void reset();
    bool compute_basis_loop();
    void assert_eq_0(nex*, u_dependency * dep);
    concat<equation_set, equation_set, equation*> equations();
    u_dependency_manager& dep() const { return m_dep_manager;  }

    void display_equations_no_deps(std::ostream& out, equation_set const& v, char const* header) const;
    void display_equations(std::ostream& out, equation_set const& v, char const* header) const;
    std::ostream& display_equation(std::ostream& out, const equation& eq) const;
    std::ostream& display(std::ostream& out) const;

    void operator=(print_expl_t& pe) { m_print_explanation = pe; }
    void operator=(params const& p) { m_params = p; }

private:
    bool compute_basis_step();

    bool simplify_source_target(equation const& source, equation& target);
    void simplify_eq_by_using_to_superpose(equation &);
    bool simplify_target_monomials(equation const& source, equation& target);
    void process_simplified_target(equation* target, ptr_buffer<equation>& to_remove);    
    bool simplify_to_superpose_with_eq(equation*);
    void simplify_m_to_simplify(equation*);
    equation* pick_next();
    bool canceled();
    void superpose(equation * eq1, equation * eq2);
    void superpose(equation * eq);
    bool find_b_c(const nex *ab, const nex* ac, nex_mul*& b, nex_mul*& c);
    bool find_b_c_check_only(const nex* ab, const nex* ac) const;
    bool is_trivial(equation* ) const; 
    bool is_simpler(equation * eq1, equation * eq2);
    void del_equations(unsigned old_size);
    void del_equation(equation * eq);
    void init_equation(equation* eq, nex*, u_dependency* d);
    
    void insert_to_simplify(equation *eq) {
        TRACE("grobner", display_equation(tout, *eq););
        m_to_simplify.insert(eq);
    }
    void insert_to_superpose(equation *eq) {
        SASSERT(m_nex_creator.is_simplified(*eq->expr()));
        TRACE("grobner", display_equation(tout, *eq););
        m_to_superpose.insert(eq);
    }
    const nex * get_highest_monomial(const nex * e) const;
    bool simplify_target_monomials_sum(equation const&, equation&, nex_sum&, const nex&);    
    unsigned find_divisible(nex_sum const&, const nex&) const;
    void simplify_target_monomials_sum_j(equation const&, equation&, nex_sum&, const nex&, unsigned, bool);
    bool divide_ignore_coeffs_check_only(nex const& , const nex&) const;
    bool divide_ignore_coeffs_check_only_nex_mul(nex_mul const&, nex const&) const;
    nex_mul * divide_ignore_coeffs_perform(nex* , const nex&);
    nex_mul * divide_ignore_coeffs_perform_nex_mul(nex_mul const& , const nex&);
    nex * expr_superpose(nex const* e1, nex const* e2, const nex* ab, const nex* ac, nex_mul* b, nex_mul* c);
    void add_mul_skip_first(nex_creator::sum_factory& sf, const rational& beta, nex const*e, nex_mul* c);
    bool done();
    unsigned num_of_equations() const { return m_to_simplify.size() + m_to_superpose.size(); }
    void update_stats_max_degree_and_size(const equation*);

    std::ostream& print_stats(std::ostream&) const;
    std::ostream& display_dependency(std::ostream& out, u_dependency*) const;
    bool equation_is_too_complex(const equation* eq) const {
        return eq->expr()->size() > m_params.m_expr_size_limit;
    }
#ifdef Z3DEBUG
    bool test_find_b_c(const nex* ab, const nex* ac, const nex_mul* b, const nex_mul* c);
    bool test_find_b(const nex* ab, const nex_mul* b);
#endif
};

class grobner : common {
    grobner_core m_gc;
    unsigned     m_reported;
public:
    grobner(core *, intervals *);
    void grobner_lemmas();
    ~grobner() {}
private:
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  svector<lpvar>& q);
    std::unordered_set<lpvar> get_vars_of_expr_with_opening_terms(const nex* e);
    void display_matrix(std::ostream & out) const;
    std::ostream& display(std::ostream& out) const { return m_gc.display(out); }
public:
    void add_row(const vector<lp::row_cell<rational>> & row);
    void check_eq(grobner_core::equation*);
    void init();
    nex_creator& get_nex_creator() { return m_nex_creator; }
}; // end of grobner
}
