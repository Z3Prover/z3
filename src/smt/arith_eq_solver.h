/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    arith_eq_solver.h

Abstract:

    Solver for linear arithmetic equalities.

Author:

    Nikolaj Bjorner (nbjorner) 2012-02-25

--*/
#ifndef ARITH_EQ_SOLVER_H_
#define ARITH_EQ_SOLVER_H_

#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/arith_rewriter.h"

/**
   \brief Simplifier for the arith family.
*/
class arith_eq_solver {
    typedef rational numeral;

    ast_manager&              m;
    params_ref                m_params;
    arith_util                m_util;
    arith_rewriter            m_arith_rewriter;

    bool is_neg_poly(expr * t) const;

    void prop_mod_const(expr * e, unsigned depth, numeral const& k, expr_ref& result);

    bool gcd_test(vector<numeral>& values);
    unsigned find_abs_min(vector<numeral>& values);
    void gcd_normalize(vector<numeral>& values);
    void substitute(vector<numeral>& r, vector<numeral> const& s, unsigned   index);
    bool solve_integer_equations_units(
        vector<vector<numeral> > & rows,
        vector<numeral>&          unsat_row
        );

    bool solve_integer_equations_omega(
        vector<vector<numeral> > & rows,
        vector<numeral>&        unsat_row
        );

    void compute_hnf(vector<vector<numeral> >& A);

    bool solve_integer_equations_hermite(
        vector<vector<numeral> > & rows,
        vector<numeral>&         unsat_row
        );

    bool solve_integer_equations_gcd(
        vector<vector<numeral> > & rows,
        vector<numeral>&        unsat_row
        );

public:
    arith_eq_solver(ast_manager & m, params_ref const& p = params_ref());
    ~arith_eq_solver() = default;

    // Integer linear solver for a single equation.
    // The array values contains integer coefficients
    //
    // Determine integer solutions to:
    //
    // a+k = 0
    //
    // where a = sum_i a_i*k_i
    //

    typedef vector<numeral> row;
    typedef vector<row>     matrix;

    bool solve_integer_equation(
        row&             values,
        unsigned&        index,
        bool&            is_fresh
        );

    // Integer linear solver.
    // Determine integer solutions to:
    //
    // a+k = 0
    //
    // where a = sum_i a_i*k_i
    //
    // Solution, if there is any, is returned as a substitution.
    // The return value is "true".
    // If there is no solution, then return "false".
    // together with equality "eq_unsat", such that
    //
    //   eq_unsat = 0
    //
    // is implied and is unsatisfiable over the integers.
    //

    bool solve_integer_equations(vector<row>& rows, row& unsat_row);

};

#endif /* ARITH_EQ_SOLVER_H_ */
