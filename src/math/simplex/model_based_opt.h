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

#pragma once

#include "util/util.h"
#include "util/rational.h"
#include "util/inf_eps_rational.h"
#include <variant>

namespace opt {
   
    enum ineq_type {
        t_eq,
        t_lt,
        t_le,
        t_divides,
        t_mod,
        t_div
    };


    typedef inf_eps_rational<inf_rational> inf_eps;
    
    class model_based_opt {
    public:
        struct var {
            unsigned m_id { 0 };
            rational m_coeff;
            var() = default;
            var(unsigned id, rational const& c): m_id(id), m_coeff(c) {}
            struct compare {
                bool operator()(var x, var y) {
                    return x.m_id < y.m_id;
                }
            };

            bool operator==(var const& other) const {
                return m_id == other.m_id && m_coeff == other.m_coeff;
            }

            bool operator!=(var const& other) const {
                return !(*this == other);
            }
            var operator*(rational const& c) const { return var(m_id, m_coeff * c); }
        };
        struct row {
            vector<var> m_vars;               // variables with coefficients
            rational    m_coeff = rational::zero();          // constant in inequality
            rational    m_mod = rational::zero();            // value the term divide
            ineq_type   m_type = t_le;        // inequality type
            rational    m_value = rational::zero();          // value of m_vars + m_coeff under interpretation of m_var2value.
            bool        m_alive = false;      // rows can be marked dead if they have been processed.
            unsigned    m_id = UINT_MAX;      // variable defined by row (used for mod_t and div_t)
            void reset() { m_vars.reset(); m_coeff.reset(); m_value.reset(); }

            row& normalize();
            void neg() { for (var & v : m_vars) v.m_coeff.neg(); m_coeff.neg(); m_value.neg(); }
            rational get_coefficient(unsigned x) const;
        };

        // A definition is a linear term of the form (vars + coeff) / div
        struct add_def;
        struct mul_def;
        struct div_def;
        struct const_def;
        struct var_def;
        enum def_t { add_t, mul_t, div_t, const_t, var_t};
        struct def {
            def() = default;
            static def* from_row(row const& r, unsigned x);           
            def_t m_type;
            unsigned m_ref_count = 0;
            bool is_add() const { return m_type == add_t; }
            bool is_mul() const { return m_type == mul_t; }
            bool is_div() const { return m_type == div_t; }
            bool is_const() const { return m_type == const_t; }
            bool is_var() const { return m_type == var_t; }
            void inc_ref() { ++m_ref_count; }
            void dec_ref();
            add_def& to_add();
            mul_def& to_mul();
            div_def& to_div();
            const_def& to_const();
            var_def& to_var();
            add_def const& to_add() const;
            mul_def const& to_mul() const;
            div_def const& to_div() const;
            const_def const& to_const() const;
            var_def const& to_var() const;
            def* operator+(def& other);
            def* operator*(def& other);
            def* operator/(unsigned n) { return *this / rational(n); }
            def* operator/(rational const& n);
            def* operator*(rational const& n);
            def* operator+(rational const& n);
            def* substitute(unsigned v, def& other);
        };
        class def_ref {
            def* m_def = nullptr;
        public:
            def_ref(def* d) {
                if (d) d->inc_ref();
                m_def = d;
            }
            def_ref& operator=(def* d) {
                if (d) d->inc_ref();
                if (m_def) m_def->dec_ref();
                m_def = d;
                return *this;
            }

            def_ref& operator=(def_ref const& d) {
                if (&d == this) 
                    return *this;
                if (d.m_def) d.m_def->inc_ref();
                if (m_def) m_def->dec_ref();
                m_def = d.m_def;
                return *this;
            }

            def& operator*() { return *m_def; }
            def* operator->() { return m_def; }
            def const& operator*() const { return *m_def; }
            operator bool() const { return !!m_def; }

            ~def_ref() { if (m_def) m_def->dec_ref(); };
        };
        struct add_def : public def {
            def* x, *y;
            add_def(def* x, def* y) : x(x), y(y) { m_type = add_t;  x->inc_ref(); y->inc_ref(); }
        };
        struct mul_def : public def {
            def* x, *y;
            mul_def(def* x, def* y) : x(x), y(y) { m_type = mul_t;  x->inc_ref(); y->inc_ref(); }
        };
        struct div_def : public def {
            def* x;
            rational m_div{ 1 };
            div_def(def* x, rational const& d) : x(x), m_div(d) { m_type = div_t; x->inc_ref(); }
        };
        struct var_def : public def {
            var v;
            var_def(var const& v) : v(v) { m_type = var_t; }
        };
        struct const_def : public def {
            rational c;
            const_def(rational const& c) : c(c) { m_type = const_t; }
        };

    private:

        vector<row>             m_rows;
        static const unsigned   m_objective_id = 0;
        vector<unsigned_vector> m_var2row_ids;
        vector<rational>        m_var2value;
        bool_vector             m_var2is_int;
        vector<var>             m_new_vars;
        unsigned_vector         m_lub, m_glb, m_divides, m_mod, m_div;
        unsigned_vector         m_above, m_below;
        unsigned_vector         m_retired_rows;
        vector<model_based_opt::def_ref> m_result;

        void eliminate(unsigned v, def& d);
        
        bool invariant();
        bool invariant(unsigned index, row const& r);

        row& objective() { return m_rows[0]; }        

        bool find_bound(unsigned x, unsigned& bound_index, rational& bound_coeff, bool is_pos);
        
        rational get_coefficient(unsigned row_id, unsigned var_id) const;

        rational eval(row const& r) const;

        rational eval(unsigned x) const;
        
        rational eval(def const& d) const;
        
        rational eval(vector<var> const& coeffs) const;

        void resolve(unsigned row_src, rational const& a1, unsigned row_dst, unsigned x);

        void solve(unsigned row_src, rational const& a1, unsigned row_dst, unsigned x);

        void mul_add(bool same_sign, unsigned row_id1, rational const& c, unsigned row_id2);

        void mul_add(unsigned x, rational a1, unsigned row_src, rational a2, unsigned row_dst);

        void mul(unsigned dst, rational const& c);

        void add(unsigned dst, rational const& c);

        void sub(unsigned dst, rational const& c);

        void set_row(unsigned row_id, vector<var> const& coeffs, rational const& c, rational const& m, ineq_type rel);

        void add_lower_bound(unsigned x, rational const& lo);

        void add_upper_bound(unsigned x, rational const& hi);

        unsigned add_constraint(vector<var> const& coeffs, rational const& c, rational const& m, ineq_type r, unsigned id);

        void replace_var(unsigned row_id, unsigned x, rational const& A, unsigned y, rational const& B);

        void replace_var(unsigned row_id, unsigned x, rational const& A, unsigned y, rational const& B, unsigned z);

        void replace_var(unsigned row_id, unsigned x, rational const& C);

        void normalize(unsigned row_id);

        void mk_coeffs_without(vector<var>& dst, vector<var> const& src, unsigned x);

        unsigned new_row();

        unsigned copy_row(unsigned row_id, unsigned excl = UINT_MAX);

        rational n_sign(rational const& b) const;

        void update_values(unsigned_vector const& bound_vars, unsigned_vector const& bound_trail);

        void update_value(unsigned x, rational const& val);

        def_ref project(unsigned var, bool compute_def);

        def_ref solve_for(unsigned row_id, unsigned x, bool compute_def);

        def_ref solve_divides(unsigned x, unsigned_vector const& divide_rows, bool compute_def);

        def_ref solve_mod_div(unsigned x, unsigned_vector const& mod_rows, unsigned_vector const& divide_rows, bool compute_def);

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


        // add sub-expression for modulus
        // v = add_mod(coeffs, m) means
        // v = coeffs mod m
        unsigned add_mod(vector<var> const& coeffs, rational const& c, rational const& m);

        // add sub-expression for div
        // v = add_div(coeffs, m) means
        // v = coeffs div m
        unsigned add_div(vector<var> const& coeffs, rational const& c, rational const& m);

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
        vector<def_ref> project(unsigned num_vars, unsigned const* vars, bool compute_def);

        //
        // Extract current rows (after projection).
        // 
        void get_live_rows(vector<row>& rows);

        void display(std::ostream& out) const;
        static std::ostream& display(std::ostream& out, row const& r);
        static std::ostream& display(std::ostream& out, def const& r);
        static void display(std::ostream& out, vector<var> const& vars, rational const& coeff);

    };

}

std::ostream& operator<<(std::ostream& out, opt::ineq_type ie);
inline std::ostream& operator<<(std::ostream& out, opt::model_based_opt::def const& d) { return opt::model_based_opt::display(out, d); }
inline std::ostream& operator<<(std::ostream& out, opt::model_based_opt::row const& r) { return opt::model_based_opt::display(out, r); }

inline std::ostream& operator<<(std::ostream& out, opt::model_based_opt::var const v) { return out << "v" << v.m_id; }

