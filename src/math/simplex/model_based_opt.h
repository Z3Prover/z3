/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    model_based_opt.h

Abstract:

    Model-based optimization for linear real arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-27-4

Revision History:


--*/

#ifndef __MODEL_BASED_OPT_H__
#define __MODEL_BASED_OPT_H__

#include "util.h"
#include "rational.h"
#include"inf_eps_rational.h"

namespace opt {
   
    enum ineq_type {
        t_eq,
        t_lt,
        t_le,
        t_mod
    };


    typedef inf_eps_rational<inf_rational> inf_eps;
    
    class model_based_opt {
    public:
        struct var {
            unsigned m_id;
            rational m_coeff;
            var(unsigned id, rational const& c): m_id(id), m_coeff(c) {}
            struct compare {
                bool operator()(var x, var y) {
                    return x.m_id < y.m_id;
                }
            };
        };
        struct row {
            row(): m_type(t_le), m_value(0), m_alive(false) {}
            vector<var> m_vars;         // variables with coefficients
            rational    m_coeff;        // constant in inequality
            rational    m_mod;          // value the term divide
            ineq_type   m_type;         // inequality type
            rational    m_value;        // value of m_vars + m_coeff under interpretation of m_var2value.
            bool        m_alive;        // rows can be marked dead if they have been processed.
            void reset() { m_vars.reset(); m_coeff.reset(); m_value.reset(); }
        };

    private:

        vector<row>             m_rows;
        static const unsigned   m_objective_id = 0;
        vector<unsigned_vector> m_var2row_ids;
        vector<rational>        m_var2value;
        svector<bool>           m_var2is_int;
        vector<var>             m_new_vars;
        unsigned_vector         m_lub, m_glb, m_mod;
        unsigned_vector         m_above, m_below;
        unsigned_vector         m_retired_rows;
        
        bool invariant();
        bool invariant(unsigned index, row const& r);

        row& objective() { return m_rows[0]; }        

        bool find_bound(unsigned x, unsigned& bound_index, rational& bound_coeff, bool is_pos);
        
        rational get_coefficient(unsigned row_id, unsigned var_id) const;

        rational get_row_value(row const& r) const;

        void resolve(unsigned row_src, rational const& a1, unsigned row_dst, unsigned x);

        void mul_add(bool same_sign, unsigned row_id1, rational const& c, unsigned row_id2);

        void mul_add(unsigned x, rational const& a1, unsigned row_src, rational const& a2, unsigned row_dst);

        void mul(unsigned dst, rational const& c);

        void add(unsigned dst, rational const& c);

        void sub(unsigned dst, rational const& c);

        void set_row(unsigned row_id, vector<var> const& coeffs, rational const& c, rational const& m, ineq_type rel);       

        void add_constraint(vector<var> const& coeffs, rational const& c, rational const& m, ineq_type r);

        void replace_var(unsigned row_id, unsigned x, rational const& A, unsigned y, rational const& B);

        void replace_var(unsigned row_id, unsigned x, rational const& C);

        void normalize(unsigned row_id);

        void mk_coeffs_without(vector<var>& dst, vector<var> const src, unsigned x);

        unsigned new_row();

        unsigned copy_row(unsigned row_id);

        rational n_sign(rational const& b) const;

        void update_values(unsigned_vector const& bound_vars, unsigned_vector const& bound_trail);

        void update_value(unsigned x, rational const& val);

        void project(unsigned var);

        void solve_for(unsigned row_id, unsigned x);

        void solve_mod(unsigned x, unsigned_vector const& mod_rows);

        bool is_int(unsigned x) const { return m_var2is_int[x]; }

        void retire_row(unsigned row_id);

    public:

        model_based_opt();

        // add a fresh variable with value 'value'.
        unsigned add_var(rational const& value, bool is_int = false);

        // retrieve updated value of variable.
        rational get_value(unsigned var_id);

        // add a constraint. We assume that the constraint is 
        // satisfied under the values provided to the variables.
        void add_constraint(vector<var> const& coeffs, rational const& c, ineq_type r);

        // add a divisibility constraint. The row should divide m.
        void add_divides(vector<var> const& coeffs, rational const& c, rational const& m);

        // Set the objective function (linear).
        void set_objective(vector<var> const& coeffs, rational const& c);

        //
        // find a maximal value for the objective function over the current values.
        // in other words, the returned maximal value may not be globally optimal,
        // but the current evaluation of variables are used to select a local
        // optimal.
        //
        inf_eps maximize();


        // 
        // Project set of variables from inequalities.
        //
        void project(unsigned num_vars, unsigned const* vars);

        //
        // Extract current rows (after projection).
        // 
        void get_live_rows(vector<row>& rows);

        void display(std::ostream& out) const;
        void display(std::ostream& out, row const& r) const;

    };

}

std::ostream& operator<<(std::ostream& out, opt::ineq_type ie);

inline std::ostream& operator<<(std::ostream& out, opt::model_based_opt::var const v) { return out << "v" << v.m_id; }

#endif 
