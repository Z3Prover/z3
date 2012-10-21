/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    grobner.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-04.

Revision History:

--*/
#ifndef _GROBNER_H_
#define _GROBNER_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"heap.h"
#include"obj_hashtable.h"
#include"region.h"
#include"dependency.h"


struct grobner_stats {
    long m_simplify; long m_superpose; long m_compute_basis; long m_num_processed;
    void reset() { memset(this, 0, sizeof(grobner_stats)); }
    grobner_stats() { reset(); }
};


/**
   \brief Simple Grobner basis implementation with no indexing.
*/
class grobner {
protected:
    struct monomial_lt;
public:
    grobner_stats m_stats;
    class monomial {
        rational         m_coeff;
        ptr_vector<expr> m_vars;  //!< sorted variables
        
        friend class grobner;
        friend struct monomial_lt;

        monomial() {}
    public:
        rational const & get_coeff() const { return m_coeff; }
        unsigned get_degree() const { return m_vars.size(); }
        unsigned get_size() const { return get_degree(); }
        expr * get_var(unsigned idx) const { return m_vars[idx]; }
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

protected:
    static bool is_eq_monomial_body(monomial const * m1, monomial const * m2);

    struct var_lt {
        obj_map<expr, int> & m_var2weight;
        var_lt(obj_map<expr, int> & m):m_var2weight(m) {}
        bool operator()(expr * v1, expr * v2) const;
    };

    struct monomial_lt {
        var_lt & m_var_lt;
        monomial_lt(var_lt & lt):m_var_lt(lt) {}
        bool operator()(monomial * m1, monomial * m2) const;
    };

    typedef obj_hashtable<equation> equation_set;
    typedef ptr_vector<equation> equation_vector;

    ast_manager &           m_manager;
    v_dependency_manager &    m_dep_manager;
    arith_util              m_util;
    obj_map<expr, int>      m_var2weight;
    var_lt                  m_var_lt;
    monomial_lt             m_monomial_lt;
    equation_set            m_processed;
    equation_set            m_to_process;
    equation_vector         m_equations_to_unfreeze;
    equation_vector         m_equations_to_delete;
    bool                    m_changed_leading_term; // set to true, if the leading term was simplified.
    equation *              m_unsat; 
    struct scope {
        unsigned m_equations_to_unfreeze_lim;
        unsigned m_equations_to_delete_lim;
    };
    svector<scope>          m_scopes;
    ptr_vector<monomial>    m_tmp_monomials;
    ptr_vector<expr>        m_tmp_vars1;
    ptr_vector<expr>        m_tmp_vars2;
    unsigned                m_num_new_equations; // temporary variable

    bool is_monomial_lt(monomial const & m1, monomial const & m2) const;

    void display_vars(std::ostream & out, unsigned num_vars, expr * const * vars) const;

    void display_var(std::ostream & out, expr * var) const;

    void display_monomials(std::ostream & out, unsigned num_monomials, monomial * const * monomials) const;

    void display_equations(std::ostream & out, equation_set const & v, char const * header) const;

    void del_equations(unsigned old_size);

    void unfreeze_equations(unsigned old_size);

    void del_equation(equation * eq);

    void flush();

    bool update_order(equation * eq);

    void update_order(equation_set & s, bool processed);

    void add_var(monomial * m, expr * v);

    monomial * mk_monomial(rational const & coeff, expr * m);

    void init_equation(equation * eq, v_dependency * d);

    void extract_monomials(expr * lhs, ptr_buffer<expr> & monomials);

    void merge_monomials(ptr_vector<monomial> & monomials);

    bool is_inconsistent(equation * eq) const;

    bool is_trivial(equation * eq) const;
    
    void normalize_coeff(ptr_vector<monomial> & monomials);

    void simplify(ptr_vector<monomial> & monomials);

    void simplify(equation * eq);

    bool is_subset(monomial const * m1, monomial const * m2, ptr_vector<expr> & rest) const;

    void mul_append(unsigned start_idx, equation const * source, rational const & coeff, ptr_vector<expr> const & vars, ptr_vector<monomial> & result);

    monomial * copy_monomial(monomial const * m);

    equation * copy_equation(equation const * eq);

    equation * simplify(equation const * source, equation * target);

    equation * simplify_using_processed(equation * eq);

    bool is_better_choice(equation * eq1, equation * eq2);

    equation * pick_next();

    void simplify_processed(equation * eq);

    void simplify_to_process(equation * eq);

    bool unify(monomial const * m1, monomial const * m2, ptr_vector<expr> & rest1, ptr_vector<expr> & rest2);

    void superpose(equation * eq1, equation * eq2);

    void superpose(equation * eq);

    void copy_to(equation_set const & s, ptr_vector<equation> & result) const;

public:
    grobner(ast_manager & m, v_dependency_manager & dep_m);

    ~grobner();

    unsigned get_scope_level() const { return m_scopes.size(); }

    /**
       \brief Set the weight of a term that is viewed as a variable by this module.
       The weight is used to order monomials. If the weight is not set for a term t, then the
       weight of t is assumed to be 0.
    */
    void set_weight(expr * n, int weight);

    int get_weight(expr * n) const { int w = 0; m_var2weight.find(n, w); return w; }

    /**
       \brief Update equations after set_weight was invoked once or more.
    */
    void update_order();

    /**
       \brief Create a new monomial. The caller owns the monomial until it invokes assert_eq_0.
       A monomial cannot be use to create several equations.
    */
    monomial * mk_monomial(rational const & coeff, unsigned num_vars, expr * const * vars);

    void del_monomial(monomial * m);

    /**
       \brief Assert the given equality.
       This method assumes eq is simplified.
    */
    void assert_eq(expr * eq, v_dependency * ex = 0);

    /**
       \brief Assert the equality monomials[0] + ... + monomials[num_monomials - 1] = 0.
       This method assumes the monomials were simplified.
    */
    void assert_eq_0(unsigned num_monomials, expr * const * monomials, v_dependency * ex = 0);

    /**
       \brief Assert the equality monomials[0] + ... + monomials[num_monomials - 1] = 0.
       This method assumes the monomials were simplified.
    */
    void assert_eq_0(unsigned num_monomials, monomial * const * monomials, v_dependency * ex = 0);

    /**
       \brief Assert the equality coeffs[0] * monomials[0] + ... + coeffs[num_monomials-1] * monomials[num_monomials - 1] = 0.
       This method assumes the monomials were simplified.
    */
    void assert_eq_0(unsigned num_monomials, rational const * coeffs, expr * const * monomials, v_dependency * ex = 0);

    /**
       \brief Assert the monomial tautology (quote (x_1 * ... * x_n)) - x_1 * ... * x_n = 0
    */
    void assert_monomial_tautology(expr * m);

    /**
       \brief Compute Grobner basis.
       Return true if the threshold was not reached.
    */
    bool compute_basis(unsigned threshold);

    /**
       \brief Return true if an inconsistency was detected.
    */
    bool inconsistent() const { return m_unsat != 0; }

    /**
       \brief Simplify the given expression using the equalities asserted 
       using assert_eq. Store the result in 'result'. 
    */
    void simplify(expr * n, expr_ref & result);

    /**
       \brief Reset state. Remove all equalities asserted with assert_eq.
    */
    void reset();

    void get_equations(ptr_vector<equation> & result) const;
    
    void push_scope();

    void pop_scope(unsigned num_scopes);

    void display_equation(std::ostream & out, equation const & eq) const;

    void display_monomial(std::ostream & out, monomial const & m) const;

    void display(std::ostream & out) const;
};

#endif /* _GROBNER_H_ */

