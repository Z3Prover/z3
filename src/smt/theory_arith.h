
/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-04-21.

Revision History:

--*/
#ifndef _THEORY_ARITH_H_
#define _THEORY_ARITH_H_

#include"smt_theory.h"
#include"map.h"
#include"heap.h"
#include"nat_set.h"
#include"inf_rational.h"
#include"s_integer.h"
#include"inf_s_integer.h"
#include"arith_decl_plugin.h"
#include"theory_arith_params.h"
#include"arith_eq_adapter.h"
#include"numeral_factory.h"
#include"obj_pair_hashtable.h"
#include"old_interval.h"
#include"grobner.h"
#include"arith_simplifier_plugin.h"
#include"arith_eq_solver.h"
#include"theory_opt.h"
#include"uint_set.h"

namespace smt {
    
    struct theory_arith_stats {
        unsigned m_conflicts, m_add_rows, m_pivots, m_diseq_cs, m_gomory_cuts, m_branches, m_gcd_tests;
        unsigned m_assert_lower, m_assert_upper, m_assert_diseq, m_core2th_eqs, m_core2th_diseqs;
        unsigned m_th2core_eqs, m_th2core_diseqs, m_bound_props, m_offset_eqs, m_fixed_eqs, m_offline_eqs;
        unsigned m_max_min; 
        unsigned m_gb_simplify, m_gb_superpose, m_gb_compute_basis, m_gb_num_processed;
        unsigned m_nl_branching, m_nl_linear, m_nl_bounds, m_nl_cross_nested;

        void reset() { memset(this, 0, sizeof(theory_arith_stats)); }
        theory_arith_stats() { reset(); }
    };


    /**
       - There are 3 kinds of variables in the tableau: base, quasi-base,
       and non-base
       
       - Each base var and quasi-base var v owns a row R(v). 
       
       - If v is a base var, then R(v) contains v and other non-base variables.
       
       - If v is a quasi-base var, then R(v) contains v and other base and
       non-base variables.
       
       - Each quasi-base var occurs only once in the tableau (i.e., it
       occurs in R(v)).
       
       - A quasi-base var does not have upper&lower bounds and distinct set.
       
       - A quasi-base var v can be transformed into a base var by
       eliminating the base vars v' in R(v).  This can be accomplished by
       adding -c * R(v') where c is the coefficient of v' in R(v).
       
       - A column is used to store the occurrences of a non-base var v' in
       rows R(v), where v is a base variable.
       
       - An implied bound stores the linear equation that implied it.
       
    */

    template<typename Ext>
    class theory_arith : public theory, public theory_opt, private Ext {
    public:
        typedef typename Ext::numeral     numeral;
        typedef typename Ext::inf_numeral inf_numeral;
        typedef vector<numeral> numeral_vector; 
        typedef map<rational, theory_var, obj_hash<rational>, default_eq<rational> > rational2var;

        static const int    dead_row_id = -1;
    protected:
        bool proofs_enabled() const { return get_manager().proofs_enabled(); }
        bool coeffs_enabled() const { return proofs_enabled() || m_bound_watch != null_bool_var; }
        
        struct linear_monomial {
            numeral     m_coeff;
            theory_var  m_var;
            linear_monomial():m_var(null_theory_var) {}
            linear_monomial(numeral const & c, theory_var v):m_coeff(c), m_var(v) {}
        };

        /**
           \brief A row_entry is:  m_var*m_coeff

           m_col_idx points to the place in the
           column where the variable occurs.
        */
        struct row_entry {
            numeral     m_coeff;
            theory_var  m_var;
            union {
                int       m_col_idx;
                int       m_next_free_row_entry_idx;
            };
            
            row_entry():m_var(0), m_col_idx(0) {}
            row_entry(numeral const & c, theory_var v): m_coeff(c), m_var(v), m_col_idx(0) {}
            bool is_dead() const { return m_var == null_theory_var; }
        };

        /**
           \brief A column entry points to the row and the row_entry within the row 
           that has a non-zero coefficient on the variable associated
           with the column entry.
        */
        struct col_entry {
            int m_row_id;
            union {
                int m_row_idx;
                int m_next_free_row_entry_idx;
            };
            
            col_entry(int r, int i): m_row_id(r), m_row_idx(i) {}
            col_entry(): m_row_id(0), m_row_idx(0) {}
            bool is_dead() const { return m_row_id == dead_row_id; }
        };
     
        struct column;

        /**
           \brief A row contains a base variable and set of
           row_entries. The base variable must occur in the set of
           row_entries with coefficient 1.
        */
        struct row {
            vector<row_entry> m_entries;
            unsigned          m_size;      // the real size, m_entries contains dead row_entries.
            int               m_base_var;
            int               m_first_free_idx; // first available position.
            row();
            unsigned size() const { return m_size; }
            unsigned num_entries() const { return m_entries.size(); }
            void reset();
            row_entry & operator[](unsigned idx) { return m_entries[idx]; }
            row_entry const & operator[](unsigned idx) const { return m_entries[idx]; }
            typename vector<row_entry>::iterator begin_entries() { return m_entries.begin(); }
            const typename vector<row_entry>::const_iterator begin_entries() const { return m_entries.begin(); }
            typename vector<row_entry>::iterator end_entries() { return m_entries.end(); }
            const typename vector<row_entry>::const_iterator end_entries() const { return m_entries.end(); }
            row_entry & add_row_entry(int & pos_idx);
            void del_row_entry(unsigned idx);
            void compress(vector<column> & cols); 
            void compress_if_needed(vector<column> & cols);
            void save_var_pos(svector<int> & result_map) const;
            void reset_var_pos(svector<int> & result_map) const;
            theory_var get_base_var() const { return m_base_var; }
#ifdef Z3DEBUG
            bool is_coeff_of(theory_var v, numeral const & expected) const;
#endif
            void display(std::ostream & out) const;
            numeral get_denominators_lcm() const;
            int get_idx_of(theory_var v) const;
        };
        
        /**
           \brief A column stores in which rows a variable occurs.
           The column may have free/dead entries. The field m_first_free_idx
           is a reference to the first free/dead entry.
        */
        struct column {
            svector<col_entry> m_entries;
            unsigned           m_size; 
            int                m_first_free_idx;
            
            column():m_size(0), m_first_free_idx(-1) {}
            unsigned size() const { return m_size; }
            unsigned num_entries() const { return m_entries.size(); }
            void reset();
            void compress(vector<row> & rows);
            void compress_if_needed(vector<row> & rows);
            void compress_singleton(vector<row> & rows, unsigned singleton_pos);
            col_entry const * get_first_col_entry() const;
            col_entry & operator[](unsigned idx) { return m_entries[idx]; }
            col_entry const & operator[](unsigned idx) const { return m_entries[idx]; }
            typename svector<col_entry>::iterator begin_entries() { return m_entries.begin(); }
            const typename svector<col_entry>::const_iterator begin_entries() const { return m_entries.begin(); }
            typename svector<col_entry>::iterator end_entries() { return m_entries.end(); }
            const typename svector<col_entry>::const_iterator end_entries() const { return m_entries.end(); }
            col_entry & add_col_entry(int & pos_idx);
            void del_col_entry(unsigned idx);
        };
        
        enum bound_kind {
            B_LOWER,
            B_UPPER
        };

        friend std::ostream & operator<<(std::ostream & out, bound_kind k) {
            switch (k) {
            case B_LOWER: out << ">="; break;
            case B_UPPER: out << "<="; break;
            }
            return out;
        }

        typedef svector<enode_pair> eq_vector;

        // keep track of coefficients used for bounds for proof generation.
        class antecedents {
            literal_vector    m_lits;
            eq_vector         m_eqs;
            vector<numeral>   m_lit_coeffs;
            vector<numeral>   m_eq_coeffs;
            vector<parameter> m_params;
            bool m_init;

            bool empty() const { 
                return m_eq_coeffs.empty() && m_lit_coeffs.empty(); 
            }

            void init();

        public:
            antecedents(): m_init(false) {}
            void reset();
            literal_vector& lits() { return m_lits; }
            eq_vector& eqs() { return m_eqs; }
            void push_lit(literal l, numeral const& r, bool proofs_enabled);
            void push_eq(enode_pair const& p, numeral const& r, bool proofs_enabled);
            unsigned num_params() const { return empty()?0:m_eq_coeffs.size() + m_lit_coeffs.size() + 1; }
            numeral const* lit_coeffs() const { return m_lit_coeffs.c_ptr(); }
            numeral const* eq_coeffs() const { return m_eq_coeffs.c_ptr(); }
            parameter* params(char const* name);
        };

        class gomory_cut_justification;

        class bound { 
        protected:
            theory_var  m_var;
            inf_numeral m_value;
            unsigned    m_bound_kind:1; 
            unsigned    m_atom:1;
        public:
            bound(theory_var v, inf_numeral const & val, bound_kind k, bool a):
                m_var(v),
                m_value(val),
                m_bound_kind(k),
                m_atom(a) {
            }
            virtual ~bound() {}
            theory_var get_var() const { return m_var; }
            bound_kind get_bound_kind() const { return static_cast<bound_kind>(m_bound_kind); }
            bool is_atom() const { return m_atom; }
            inf_numeral const & get_value() const { return m_value; }
            virtual bool has_justification() const { return false; }
            virtual void push_justification(antecedents& antecedents, numeral const& coeff, bool proofs_enabled) {}
            virtual void display(theory_arith const& th, std::ostream& out) const;
        };


        enum atom_kind {
            A_LOWER,
            A_UPPER
        };

        class atom : public bound {
        protected:
            bool_var    m_bvar;
            inf_numeral m_k;
            unsigned    m_atom_kind:2;   // atom kind
            unsigned    m_is_true:1;     // cache: true if the atom was assigned to true.
        public:
            atom(bool_var bv, theory_var v, inf_numeral const & k, atom_kind kind);
            atom_kind get_atom_kind() const { return static_cast<atom_kind>(m_atom_kind); }
            virtual ~atom() {}
            inline inf_numeral const & get_k() const { return m_k; }
            bool_var get_bool_var() const { return m_bvar; }
            bool is_true() const { return m_is_true; }
            void assign_eh(bool is_true, inf_numeral const & epsilon);
            virtual bool has_justification() const { return true; }
            virtual void push_justification(antecedents& a, numeral const& coeff, bool proofs_enabled) { 
                a.push_lit(literal(get_bool_var(), !m_is_true), coeff, proofs_enabled); 
            }
            virtual void display(theory_arith const& th, std::ostream& out) const;
        };

        class eq_bound : public bound { 
            enode * m_lhs;
            enode * m_rhs;
        public:
            eq_bound(theory_var v, inf_numeral const & val, bound_kind k, enode * lhs, enode * rhs):
                bound(v, val, k, false),
                m_lhs(lhs),
                m_rhs(rhs) {
                SASSERT(m_lhs->get_root() == m_rhs->get_root());
            }
            virtual ~eq_bound() {}
            virtual bool has_justification() const { return true; }
            virtual void push_justification(antecedents& a, numeral const& coeff, bool proofs_enabled) {
                SASSERT(m_lhs->get_root() == m_rhs->get_root());
                a.push_eq(enode_pair(m_lhs, m_rhs), coeff, proofs_enabled); 
            }
            virtual void display(theory_arith const& th, std::ostream& out) const;
        };

        class derived_bound : public bound {
        protected:
            literal_vector m_lits;
            eq_vector      m_eqs;
            friend class theory_arith;
        public:
            derived_bound(theory_var v, inf_numeral const & val, bound_kind k):bound(v, val, k, false) {}
            virtual ~derived_bound() {}
            virtual bool has_justification() const { return true; }
            virtual void push_justification(antecedents& a, numeral const& coeff, bool proofs_enabled); 
            virtual void push_lit(literal l, numeral const&) { m_lits.push_back(l); }
            virtual void push_eq(enode_pair const& p, numeral const&) { m_eqs.push_back(p); }
            virtual void display(theory_arith const& th, std::ostream& out) const;
        };
    
        class justified_derived_bound : public derived_bound {
            vector<numeral>  m_lit_coeffs;
            vector<numeral>  m_eq_coeffs;
            friend class theory_arith;
        public:
            justified_derived_bound(theory_var v, inf_numeral const & val, bound_kind k):derived_bound(v, val, k) {}
            virtual ~justified_derived_bound() {}
            virtual bool has_justification() const { return true; }
            virtual void push_justification(antecedents& a, numeral const& coeff, bool proofs_enabled);
            virtual void push_lit(literal l, numeral const& coeff);               

            virtual void push_eq(enode_pair const& p, numeral const& coeff);
        };
   
        typedef int_hashtable<int_hash, default_eq<int> > literal_idx_set;
        typedef obj_pair_hashtable<enode, enode> eq_set;
        literal_vector   m_tmp_acc_lits;
        eq_vector        m_tmp_acc_eqs;
        literal_idx_set  m_tmp_lit_set;
        eq_set           m_tmp_eq_set;
        void accumulate_justification(bound & b, derived_bound & target, numeral const& coeff, literal_idx_set & lits, eq_set & eqs);
        inf_numeral normalize_bound(theory_var v, inf_numeral const & k, bound_kind kind);
        void mk_bound_from_row(theory_var v, inf_numeral const & coeff, bound_kind k, row const & r);

        typedef ptr_vector<atom> atoms;
// #define SPARSE_MAP

#ifdef SPARSE_MAP
        typedef u_map<atom *>    bool_var2atom;
#else
        typedef ptr_vector<atom> bool_var2atom;
#endif 
        struct theory_var_lt {
            bool operator()(theory_var v1, theory_var v2) const { return v1 < v2; }
        };

        typedef heap<theory_var_lt> var_heap;
        
        enum var_kind {
            NON_BASE,
            BASE,
            QUASI_BASE
        };

        struct var_data {
            unsigned     m_row_id:28; // row owned by the variable, irrelevant if kind() == NON_BASE
            unsigned     m_kind:2; 
            unsigned     m_is_int:1;
            unsigned     m_nl_propagated:1;
            var_data(bool is_int = false):m_row_id(0), m_kind(NON_BASE), m_is_int(is_int), m_nl_propagated(false) {}
            var_kind kind() const { return static_cast<var_kind>(m_kind); }
        };

        class bound_trail {
            theory_var  m_var;
            bound *     m_old_bound;
        public:
            bound_trail(theory_var v, bound * b, bool is_upper):
                m_var(v << 1 | static_cast<int>(is_upper)),
                m_old_bound(b) {
            }

            bool is_upper() const { return (m_var & 1) == 1; }
            theory_var get_var() const { return m_var >> 1; }
            bound * get_old_bound() const { return m_old_bound; }
        };


        theory_arith_stats      m_stats;
        theory_arith_params &   m_params;
        arith_util              m_util;
        arith_eq_solver         m_arith_eq_solver;
        bool                    m_found_unsupported_op;
        arith_eq_adapter        m_arith_eq_adapter;
        vector<row>             m_rows;
        svector<unsigned>       m_dead_rows;
        vector<column>          m_columns;          // per var
        svector<var_data>       m_data;             // per var
        vector<inf_numeral>     m_value;            // per var, the current assignment for the variable.
        vector<inf_numeral>     m_old_value;        // per var, the old assignment for the variable.
        ptr_vector<bound>       m_bounds[2];        // per var, lower bound & upper_bound
        vector<atoms>           m_var_occs;         // per var, atoms that contain a variable
        svector<unsigned>       m_unassigned_atoms; // per var, the number of unassigned atoms that contain a variable.
        bool_var2atom           m_bool_var2atom;    // map bool_var -> atom
        svector<int>            m_var_pos;          // temporary array used in add_rows
        atoms                   m_atoms;            // set of theory atoms
        ptr_vector<bound>       m_asserted_bounds;  // set of asserted bounds
        unsigned                m_asserted_qhead;   
        ptr_vector<atom>        m_new_atoms;        // new bound atoms that have yet to be internalized.
        svector<theory_var>     m_nl_monomials;     // non linear monomials
        svector<theory_var>     m_nl_propagated;    // non linear monomials that became linear
        v_dependency_manager    m_dep_manager;      // for tracking bounds during non-linear reasoning

        var_heap                m_to_patch;         // heap containing all variables v s.t. m_value[v] does not satisfy bounds of v.
        nat_set                 m_left_basis;       // temporary: set of variables that already left the basis in make_feasible
        bool                    m_blands_rule;

        svector<unsigned>       m_update_trail_stack;    // temporary trail stack used to restore the last feasible assignment.
        nat_set                 m_in_update_trail_stack; // set of variables in m_update_trail_stack

        svector<unsigned>       m_to_check;    // rows that should be checked for theory propagation
        nat_set                 m_in_to_check; // set of rows in m_to_check. 
        
        inf_numeral             m_tmp;
        random_gen              m_random;
        unsigned                m_num_conflicts;

        unsigned                m_branch_cut_counter;
        bool                    m_eager_gcd; // true if gcd should be applied at every add_row
        unsigned                m_final_check_idx;


        // backtracking
        svector<bound_trail>    m_bound_trail;
        svector<unsigned>       m_unassigned_atoms_trail;
        ptr_vector<bound>       m_bounds_to_delete;
        struct scope {
            unsigned      m_atoms_lim;
            unsigned      m_bound_trail_lim;
            unsigned      m_unassigned_atoms_trail_lim;
            unsigned      m_asserted_bounds_lim;
            unsigned      m_asserted_qhead_old;
            unsigned      m_bounds_to_delete_lim;
            unsigned      m_nl_monomials_lim;
            unsigned      m_nl_propagated_lim;
        };

        svector<scope>          m_scopes;
        literal_vector          m_tmp_literal_vector2;
        antecedents             m_tmp_antecedents;
        antecedents             m_tmp_antecedents2;

        struct var_value_hash;
        friend struct var_value_hash;
        struct var_value_hash {
            theory_arith & m_th;
            var_value_hash(theory_arith & th):m_th(th) {}
            unsigned operator()(theory_var v) const { return m_th.get_value(v).hash(); }
        };

        struct var_value_eq;
        friend struct var_value_eq;
        struct var_value_eq {
            theory_arith & m_th;
            var_value_eq(theory_arith & th):m_th(th) {}
            bool operator()(theory_var v1, theory_var v2) const { return m_th.get_value(v1) == m_th.get_value(v2) && m_th.is_int(v1) == m_th.is_int(v2); }
        };

        typedef int_hashtable<var_value_hash, var_value_eq> var_value_table;
        var_value_table             m_var_value_table;

        virtual theory_var mk_var(enode * n);

        void found_unsupported_op(app * n);

        bool has_var(expr * v) const { return get_context().e_internalized(v) && get_context().get_enode(v)->get_th_var(get_id()) != null_theory_var; }
        theory_var expr2var(expr * v) const { SASSERT(get_context().e_internalized(v)); return get_context().get_enode(v)->get_th_var(get_id()); }
        expr * var2expr(theory_var v) const { return get_enode(v)->get_owner(); }
        bool reflection_enabled() const;
        bool reflect(app * n) const;
        unsigned lazy_pivoting_lvl() const { return m_params.m_arith_lazy_pivoting_lvl; }
        bool propagate_eqs() const { return m_params.m_arith_propagate_eqs && m_num_conflicts < m_params.m_arith_propagation_threshold; }
        bool propagate_diseqs() const { return false; }
        bool random_initial_value() const { return m_params.m_arith_random_initial_value; }
        int random_lower() const { return m_params.m_arith_random_lower; }
        int random_upper() const { return m_params.m_arith_random_upper; }
        unsigned blands_rule_threshold() const { return m_params.m_arith_blands_rule_threshold; }
        bound_prop_mode propagation_mode() const { return m_num_conflicts < m_params.m_arith_propagation_threshold ? m_params.m_arith_bound_prop : BP_NONE; }
        bool adaptive() const { return m_params.m_arith_adaptive; }
        double adaptive_assertion_threshold() const { return m_params.m_arith_adaptive_assertion_threshold; }
        unsigned max_lemma_size() const { return m_params.m_arith_max_lemma_size; }
        unsigned small_lemma_size() const { return m_params.m_arith_small_lemma_size; }
        bool relax_bounds() const { return m_params.m_arith_stronger_lemmas; }
        bool skip_big_coeffs() const { return m_params.m_arith_skip_rows_with_big_coeffs; }
        bool dump_lemmas() const { return m_params.m_arith_dump_lemmas; }
        bool process_atoms() const;
        unsigned get_num_conflicts() const { return m_num_conflicts; }
        var_kind get_var_kind(theory_var v) const { return m_data[v].kind(); }
        bool is_base(theory_var v) const { return get_var_kind(v) == BASE; }
        bool is_quasi_base(theory_var v) const { return get_var_kind(v) == QUASI_BASE; }
        bool is_non_base(theory_var v) const { return get_var_kind(v) == NON_BASE; }
        void set_var_kind(theory_var v, var_kind k) { m_data[v].m_kind = k; }
        unsigned get_var_row(theory_var v) const { SASSERT(!is_non_base(v)); return m_data[v].m_row_id; }
        void set_var_row(theory_var v, unsigned r_id) { m_data[v].m_row_id = r_id; }
        bool is_int(theory_var v) const { return m_data[v].m_is_int; }
        bool is_real(theory_var v) const { return !is_int(v); }
        bool get_implied_old_value(theory_var v, inf_numeral & r) const;
        inf_numeral const & get_implied_value(theory_var v) const;
        inf_numeral const & get_quasi_base_value(theory_var v) const { return get_implied_value(v); }
        inf_numeral const & get_value(theory_var v) const { return is_quasi_base(v) ? get_quasi_base_value(v) : m_value[v]; }
        bound * get_bound(theory_var v, bool upper) const { return m_bounds[static_cast<unsigned>(upper)][v]; }
        bound * lower(theory_var v) const { return m_bounds[0][v]; }
        bound * upper(theory_var v) const { return m_bounds[1][v]; }
        inf_numeral const & lower_bound(theory_var v) const { SASSERT(lower(v) != 0); return lower(v)->get_value(); }
        inf_numeral const & upper_bound(theory_var v) const { SASSERT(upper(v) != 0); return upper(v)->get_value(); }
        bool below_lower(theory_var v) const { bound * l = lower(v); return l != 0 && get_value(v) < l->get_value(); }
        bool above_upper(theory_var v) const { bound * u = upper(v); return u != 0 && get_value(v) > u->get_value(); }
        bool below_upper(theory_var v) const { bound * u = upper(v); return u == 0 || get_value(v) < u->get_value(); }
        bool above_lower(theory_var v) const { bound * l = lower(v); return l == 0 || get_value(v) > l->get_value(); }
        bool at_bound(theory_var v) const;
        bool at_lower(theory_var v) const { bound * l = lower(v); return l != 0 && get_value(v) == l->get_value(); }
        bool at_upper(theory_var v) const { bound * u = upper(v); return u != 0 && get_value(v) == u->get_value(); }
        bool is_free(theory_var v) const { return lower(v) == 0 && upper(v) == 0; }
        bool is_non_free(theory_var v) const { return lower(v) != 0 || upper(v) != 0; }
        bool is_bounded(theory_var v) const { return lower(v) != 0 && upper(v) != 0; }
        bool is_free(expr * n) const { 
            SASSERT(get_context().e_internalized(n) && get_context().get_enode(n)->get_th_var(get_id()) != null_theory_var);
            return is_free(get_context().get_enode(n)->get_th_var(get_id())); 
        }
        bool is_fixed(theory_var v) const;
        void set_bound_core(theory_var v, bound * new_bound, bool upper) { m_bounds[static_cast<unsigned>(upper)][v] = new_bound; }
        void restore_bound(theory_var v, bound * new_bound, bool upper) { set_bound_core(v, new_bound, upper); }
        void restore_nl_propagated_flag(unsigned old_trail_size);
        void set_bound(bound * new_bound, bool upper);
        inf_numeral const & get_epsilon(theory_var v) const { return is_real(v) ? this->m_real_epsilon : this->m_int_epsilon; }
        bool enable_cgc_for(app * n) const;
        enode * mk_enode(app * n);
        void mk_enode_if_reflect(app * n);
        template<bool invert>
        void add_row_entry(unsigned r_id, numeral const & coeff, theory_var v);
        void internalize_internal_monomial(app * m, unsigned r_id);
        theory_var internalize_add(app * n);
        theory_var internalize_mul_core(app * m);
        theory_var internalize_mul(app * m);
        theory_var internalize_div(app * n);
        theory_var mk_binary_op(app * n);
        theory_var internalize_idiv(app * n);
        theory_var internalize_mod(app * n);
        theory_var internalize_rem(app * n);
        theory_var internalize_to_real(app * n);
        theory_var internalize_to_int(app * n);
        void internalize_is_int(app * n);
        theory_var internalize_numeral(app * n);
        theory_var internalize_term_core(app * n);
        void mk_axiom(expr * n1, expr * n2);
        void mk_idiv_mod_axioms(expr * dividend, expr * divisor);
        void mk_div_axiom(expr * dividend, expr * divisor);
        void mk_rem_axiom(expr * dividend, expr * divisor);
        void mk_to_int_axiom(app* to_int);
        void mk_is_int_axiom(app* is_int);

        unsigned mk_row();
        void init_row(unsigned r_id);
        void collect_vars(unsigned r_id, var_kind k, buffer<linear_monomial> & result);
        void normalize_quasi_base_row(unsigned r_id);
        void quasi_base_row2base_row(unsigned r_id);
        void normalize_base_row(unsigned r_id);
        void mk_clause(literal l1, literal l2, unsigned num_params, parameter * params);
        void mk_clause(literal l1, literal l2, literal l3, unsigned num_params, parameter * params);
        void mk_bound_axioms(atom * a);
        void mk_bound_axiom(atom* a1, atom* a2);
        void flush_bound_axioms();
        typename atoms::iterator next_sup(atom* a1, atom_kind kind, 
                                          typename atoms::iterator it, 
                                          typename atoms::iterator end,
                                          bool& found_compatible);
        typename atoms::iterator next_inf(atom* a1, atom_kind kind, 
                                          typename atoms::iterator it, 
                                          typename atoms::iterator end,
                                          bool& found_compatible);
        typename atoms::iterator first(atom_kind kind, 
                                       typename atoms::iterator it, 
                                       typename atoms::iterator end);
        struct compare_atoms {
            bool operator()(atom* a1, atom* a2) const { return a1->get_k() < a2->get_k(); }
        };
        virtual bool default_internalizer() const { return false; }
        virtual bool internalize_atom(app * n, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual void internalize_eq_eh(app * atom, bool_var v);
        virtual void apply_sort_cnstr(enode * n, sort * s);
        
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual bool use_diseqs() const;
        virtual void new_diseq_eh(theory_var v1, theory_var v2);

        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);

        virtual void relevant_eh(app * n);
        
        virtual void restart_eh();
        virtual void init_search_eh();
        /**
           \brief True if the assignment may be changed during final
           check.  assume_eqs, check_int_feasibility,
           process_non_linear may change the current assignment to
           satisfy their respective constraints.  However, when they
           do that the may create inconsistencies in the other
           modules. I use m_liberal_final_check to avoid infinite
           loops where the modules keep changing the assigment and no
           progress is made. If m_liberal_final_check is set to false,
           these modules will avoid mutating the assignment to satisfy
           constraints.

           See also m_changed_assignment flag.
        */
        bool    m_liberal_final_check; 
        final_check_status final_check_core();
        virtual final_check_status final_check_eh();
        
        virtual bool can_propagate();
        virtual void propagate();
        bool propagate_core();
        void failed();

        
        virtual void flush_eh();
        virtual void reset_eh();
        
        virtual bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const;

        // -----------------------------------
        //
        // bool_var -> atom mapping
        //
        // -----------------------------------
        void insert_bv2a(bool_var bv, atom * a) {
#ifdef SPARSE_MAP
            m_bool_var2atom.insert(bv, a);
#else
            m_bool_var2atom.setx(bv, a, 0);
#endif
        }
        
        void erase_bv2a(bool_var bv) {
#ifdef SPARSE_MAP
            m_bool_var2atom.erase(bv);
#else
            m_bool_var2atom[bv] = 0;
#endif
        }

        atom * get_bv2a(bool_var bv) {
#ifdef SPARSE_MAP
            atom * a;
            m_bool_var2atom.find(bv, a);
            return a;
#else
            return m_bool_var2atom.get(bv, 0);
#endif
        }


        // -----------------------------------
        //
        // Add Row
        //
        // -----------------------------------
        void add_row(unsigned r1, const numeral & coeff, unsigned r2, bool apply_gcd_test);
        void add_rows(unsigned r1, unsigned sz, linear_monomial * a_xs);

        // -----------------------------------
        //
        // Assignment management
        //
        // -----------------------------------
        bool m_changed_assignment; //!< auxiliary variable set to true when the assignment is changed.
        void save_value(theory_var v);
        void discard_update_trail();
        void restore_assignment();
        void update_value_core(theory_var v, inf_numeral const & delta);
        void update_value(theory_var v, inf_numeral const & delta);
        void set_value(theory_var v, const inf_numeral & new_val) { update_value(v, new_val - m_value[v]); }

        // -----------------------------------
        //
        // Pivoting
        //
        // -----------------------------------
        template<bool Lazy>
        void pivot(theory_var x_i, theory_var x_j, numeral const & a_ij, bool apply_gcd_test);
        template<bool Lazy>
        void eliminate(theory_var x_i, bool apply_gcd_test);
        void update_and_pivot(theory_var x_i, theory_var x_j, numeral const & a_ij, inf_numeral const & x_i_new_val);
        int get_num_non_free_dep_vars(theory_var v, int best_so_far);
        theory_var select_blands_pivot_core(theory_var x_i, bool is_below, numeral & out_a_ij);
        template<bool is_below>
        theory_var select_pivot_core(theory_var x_i, numeral & out_a_ij);
        theory_var select_pivot(theory_var x_i, bool is_below, numeral & out_a_ij);

        // -----------------------------------
        //
        // Make feasible
        //
        // -----------------------------------
        bool make_var_feasible(theory_var x_i);
        theory_var select_var_to_fix();
        theory_var select_lg_error_var(bool least);
        theory_var select_greatest_error_var() { return select_lg_error_var(false); }
        theory_var select_least_error_var() { return select_lg_error_var(true); }
        theory_var select_smallest_var();
        bool make_feasible();
        void sign_row_conflict(theory_var x_i, bool is_below);

        // -----------------------------------
        //
        // Assert bound
        //
        // -----------------------------------
        bool assert_lower(bound * b);
        bool assert_upper(bound * b);
        bool assert_bound(bound * b);
        void sign_bound_conflict(bound * b1, bound * b2);

        // -----------------------------------
        //
        // Bound propagation
        //
        // -----------------------------------
        void mark_row_for_bound_prop(unsigned r1);
        void mark_rows_for_bound_prop(theory_var v);
        void is_row_useful_for_bound_prop(row const & r, int & lower_idx, int & upper_idx) const;
        void imply_bound_for_monomial(row const & r, int idx, bool lower);
        void imply_bound_for_all_monomials(row const & r, bool lower);
        void explain_bound(row const & r, int idx, bool lower, inf_numeral & delta, 
                           antecedents & antecedents);
        void mk_implied_bound(row const & r, unsigned idx, bool lower, theory_var v, bound_kind kind, inf_numeral const & k);
        void assign_bound_literal(literal l, row const & r, unsigned idx, bool lower, inf_numeral & delta, antecedents& antecedents);
        void propagate_bounds();

        // -----------------------------------
        //
        // Freedom intervals
        //
        // -----------------------------------
        bool get_freedom_interval(theory_var x_j, bool & inf_l, inf_numeral & l, bool & inf_u, inf_numeral & u, numeral & m);

        // -----------------------------------
        //
        // Implied eqs
        //
        // -----------------------------------
        bool try_to_imply_eq(theory_var v1, theory_var v2);

        // -----------------------------------
        //
        // Assume eqs with randomization
        //
        // -----------------------------------
        typedef int_hashtable<int_hash, default_eq<int> > var_set;
        var_set         m_tmp_var_set;
        var_set         m_tmp_var_set2;
        svector<std::pair<theory_var, theory_var> >       m_assume_eq_candidates;
        unsigned                                          m_assume_eq_head;
        bool random_update(theory_var v);
        void mutate_assignment();
        bool assume_eqs_core();
        bool delayed_assume_eqs();

        // -----------------------------------
        //
        // Integrality
        //
        // -----------------------------------
        void move_non_base_vars_to_bounds();
        bool has_infeasible_int_var();
        theory_var find_infeasible_int_base_var();
        theory_var find_bounded_infeasible_int_base_var();
        void branch_infeasible_int_var(theory_var v);
        bool branch_infeasible_int_equality();
        bool constrain_free_vars(row const & r);
        bool is_gomory_cut_target(row const & r);
        bool mk_gomory_cut(row const & r);
        bool gcd_test(row const & r);
        bool ext_gcd_test(row const & r, numeral const & least_coeff, numeral const & lcm_den, numeral const & consts);
        bool gcd_test();
        void mk_polynomial_ge(unsigned num_args, row_entry const * args, rational const& k, expr_ref & result);
        bool max_min_infeasible_int_vars();
        void patch_int_infeasible_vars();
        void fix_non_base_vars();
        unsynch_mpq_manager m_es_num_manager; // manager for euclidean solver.
        struct euclidean_solver_bridge;
        bool apply_euclidean_solver();
        final_check_status check_int_feasibility();

        // -----------------------------------
        //
        // Eq propagation
        //
        // -----------------------------------
        typedef std::pair<numeral, bool> value_sort_pair;
        typedef pair_hash<obj_hash<numeral>, bool_hash> value_sort_pair_hash;
        typedef map<value_sort_pair, theory_var, value_sort_pair_hash, default_eq<value_sort_pair> > value2var;
        value2var               m_fixed_var_table;
        
        typedef std::pair<theory_var, numeral> var_offset;
        typedef pair_hash<int_hash, obj_hash<numeral> > var_offset_hash;
        typedef map<var_offset, int, var_offset_hash, default_eq<var_offset> > var_offset2row_id;
        var_offset2row_id       m_var_offset2row_id;

        bool is_equal(theory_var x, theory_var y) const { return get_enode(x)->get_root() == get_enode(y)->get_root(); }
        void fixed_var_eh(theory_var v);
        bool is_offset_row(row const & r, theory_var & x, theory_var & y, numeral & k) const;
        void propagate_cheap_eq(unsigned rid);
        void propagate_eq_to_core(theory_var x, theory_var y, antecedents& antecedents);

        virtual bool is_shared(theory_var v) const;

        // -----------------------------------
        //
        // Justification
        //
        // -----------------------------------
        void set_conflict(unsigned num_literals, literal const * lits, unsigned num_eqs, enode_pair const * eqs, antecedents& antecedents, bool is_lia, char const* proof_rule);
        void collect_fixed_var_justifications(row const & r, antecedents& antecedents) const;
        
        // -----------------------------------
        //
        // Backtracking
        //
        // -----------------------------------
        void push_bound_trail(theory_var v, bound * old_bound, bool is_upper) { m_bound_trail.push_back(bound_trail(v, old_bound, is_upper)); }
        void push_dec_unassigned_atoms_trail(theory_var v) { m_unassigned_atoms_trail.push_back(v); }
        void restore_bounds(unsigned old_trail_size);
        void restore_unassigned_atoms(unsigned old_trail_size);
        void del_atoms(unsigned old_size);
        void del_bounds(unsigned old_size);
        void del_vars(unsigned old_num_vars);
        void del_row(unsigned r_id);

        // -----------------------------------
        //
        // Auxiliary methods
        //
        // -----------------------------------
        col_entry const * get_a_base_row_that_contains(theory_var v);
        bool all_coeff_int(row const & r) const;
        col_entry const * get_row_for_eliminating(theory_var v) const;
        void move_unconstrained_to_base();
        void elim_quasi_base_rows();
        void remove_fixed_vars_from_base();
        void try_to_minimize_rational_coeffs();

        /**
           \brief See comment in theory::mk_eq_atom
        */
        virtual app * mk_eq_atom(expr * lhs, expr * rhs) { return m_util.mk_eq(lhs, rhs); }

        // -----------------------------------
        //
        // Maximization/Minimization 
        //
        // -----------------------------------
        row               m_tmp_row;

        void add_tmp_row(row & r1, numeral const & coeff, row const & r2);
        bool is_safe_to_leave(theory_var x, bool inc, bool& has_int, bool& is_shared);
        template<bool invert>
        void add_tmp_row_entry(row & r, numeral const & coeff, theory_var v);
        enum max_min_t { UNBOUNDED, AT_BOUND, OPTIMIZED, BEST_EFFORT};
        max_min_t max_min(theory_var v, bool max, bool maintain_integrality, bool& has_shared);
        bool has_interface_equality(theory_var v);
        bool max_min(svector<theory_var> const & vars);

        max_min_t max_min(row& r, bool max, bool maintain_integrality, bool& has_shared);
        bool unbounded_gain(inf_numeral const & max_gain) const;
        bool safe_gain(inf_numeral const& min_gain, inf_numeral const & max_gain) const;
        void normalize_gain(numeral const& divisor, inf_numeral & max_gain) const;
        void init_gains(theory_var x, bool inc, inf_numeral& min_gain, inf_numeral& max_gain);
        bool update_gains(bool inc, theory_var x_i, numeral const& a_ij, 
                          inf_numeral& min_gain, inf_numeral& max_gain);
        bool move_to_bound(theory_var x_i, bool inc, unsigned& best_efforts, bool& has_shared);
        bool pick_var_to_leave(
            theory_var x_j, bool inc, numeral & a_ij, 
            inf_numeral& min_gain, inf_numeral& max_gain, 
            bool& shared, theory_var& x_i);

        // -----------------------------------
        //
        // Non linear
        //
        // -----------------------------------
        typedef int_hashtable<int_hash, default_eq<int> > row_set;
        unsigned        m_nl_rounds;
        bool            m_nl_gb_exhausted;
        unsigned        m_nl_strategy_idx; // for fairness
        expr_ref_vector m_nl_new_exprs;
        typedef obj_map<expr, unsigned> var2num_occs;
        var2num_occs m_var2num_occs;
        typedef std::pair<expr *, unsigned> var_num_occs;
        struct var_num_occs_lt { bool operator()(var_num_occs const & vn1, var_num_occs const & vn2) const { return vn1.second > vn2.second; } };

        /**
           \brief A monomial is 'pure' if does not have a numeric coefficient.
        */
        bool is_pure_monomial(expr * m) const { return m_util.is_mul(m) && !m_util.is_numeral(to_app(m)->get_arg(0)); }
        bool is_pure_monomial(theory_var v) const { return is_pure_monomial(get_enode(v)->get_owner()); }
        void mark_var(theory_var v, svector<theory_var> & vars, var_set & already_found);
        void mark_dependents(theory_var v, svector<theory_var> & vars, var_set & already_found, row_set & already_visited_rows);
        void get_non_linear_cluster(svector<theory_var> & vars);
        std::pair<unsigned, int> analyze_monomial(expr * m) const;
        expr * get_monomial_body(expr * m) const;
        rational get_monomial_coeff(expr * m) const;
        unsigned get_num_vars_in_monomial(expr * m) const;
        typedef std::pair<expr *, unsigned> var_power_pair;
        var_power_pair get_var_and_degree(expr * m, unsigned i) const;
        void display_monomial(std::ostream & out, expr * m) const;
        bool propagate_nl_upward(expr * m);
        bool propagate_nl_downward(expr * m, unsigned i);
        interval mk_interval_for(theory_var v);
        interval mk_interval_for(expr * n);
        void mul_bound_of(expr * var, unsigned power, interval & target);
        interval evaluate_as_interval(expr * n);
        void dependency2new_bound(v_dependency * dep, derived_bound& new_bound);
        void mk_derived_nl_bound(theory_var v, inf_numeral const & coeff, bound_kind k, v_dependency * dep);
        bool update_bounds_using_interval(theory_var v, interval const & i);
        bool update_bounds_using_interval(expr * n, interval const & i);
        bool propagate_nl_bounds(expr * m);
        bool propagate_nl_bound(expr * m, int i);
        bool propagate_nl_bounds();
        bool is_problematic_non_linear_row(row const & r);
        bool is_mixed_real_integer(row const & r) const;
        bool is_integer(row const & r) const;
        typedef std::pair<rational, expr *> coeff_expr; 
        void get_polynomial_info(sbuffer<coeff_expr> const & p, sbuffer<var_num_occs> & vars);
        expr * p2expr(sbuffer<coeff_expr> & p);
        expr * power(expr * var, unsigned power);
        expr * mk_nary_mul(unsigned sz, expr * const * args, bool is_int);
        expr * mk_nary_add(unsigned sz, expr * const * args, bool is_int);
        expr * mk_nary_add(unsigned sz, expr * const * args);
        void display_nested_form(std::ostream & out, expr * p);
        unsigned get_degree_of(expr * m, expr * var);
        unsigned get_min_degree(sbuffer<coeff_expr> & p, expr * var);
        expr * factor(expr * m, expr * var, unsigned d);
        bool in_monovariate_monomials(sbuffer<coeff_expr> & p, expr * var, unsigned & i1, rational & c1, unsigned & n1, unsigned & i2, rational & c2, unsigned & n2);
        expr * horner(sbuffer<coeff_expr> & p, expr * var);
        expr * cross_nested(sbuffer<coeff_expr> & p, expr * var);
        bool is_cross_nested_consistent(sbuffer<coeff_expr> & p);
        bool is_cross_nested_consistent(row const & r);
        bool is_cross_nested_consistent(svector<theory_var> const & nl_cluster);
        rational get_value(theory_var v, bool & computed_epsilon);
        bool check_monomial_assignment(theory_var v, bool & computed_epsilon);
        bool check_monomial_assignments();
        theory_var find_nl_var_for_branching();
        bool branch_nl_int_var(theory_var v);
        bool is_monomial_linear(expr * m) const;
        numeral get_monomial_fixed_var_product(expr * m) const;
        expr * get_monomial_non_fixed_var(expr * m) const;
        bool propagate_linear_monomial(theory_var v);
        bool propagate_linear_monomials();
        grobner::monomial * mk_gb_monomial(rational const & coeff, expr * m, grobner & gb, v_dependency * & dep, var_set & already_found);
        void add_monomial_def_to_gb(theory_var v, grobner & gb);
        void add_row_to_gb(row const & r, grobner & gb);
        void init_grobner_var_order(svector<theory_var> const & nl_cluster, grobner & gb);
        void init_grobner(svector<theory_var> const & nl_cluster, grobner & gb);
        interval mk_interval_for(grobner::monomial const * m);
        void set_conflict(v_dependency * d);
        bool is_inconsistent(interval const & I, unsigned num_monomials, grobner::monomial * const * monomials, v_dependency * dep);
        bool is_inconsistent(grobner::equation const * eq, grobner & gb);
        bool is_inconsistent2(grobner::equation const * eq, grobner & gb);
        expr * monomial2expr(grobner::monomial const * m, bool is_int);
        bool internalize_gb_eq(grobner::equation const * eq);
        enum gb_result { GB_PROGRESS, GB_NEW_EQ, GB_FAIL };
        gb_result compute_grobner(svector<theory_var> const & nl_cluster);
        bool max_min_nl_vars();
        final_check_status process_non_linear();
        antecedents&            get_antecedents();

        // -----------------------------------
        //
        // Constructor 
        //
        // -----------------------------------
    public:
        theory_arith(ast_manager & m, theory_arith_params & params);
        virtual ~theory_arith();
        
        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_arith, get_manager(), m_params); }

        virtual void setup();

        virtual char const * get_name() const { return "arithmetic"; }

        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------
        arith_factory *    m_factory;
        numeral            m_epsilon;
        void update_epsilon(const inf_numeral & l, const inf_numeral & u);
        void compute_epsilon();
        void refine_epsilon();

        virtual void init_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

        // -----------------------------------
        //
        // Model checker
        //
        // -----------------------------------
        virtual bool get_value(enode * n, expr_ref & r);


        // -----------------------------------
        //
        // Optimization
        //
        // -----------------------------------
        virtual inf_eps_rational<inf_rational> maximize(theory_var v, expr_ref& blocker, bool& has_shared);
        virtual inf_eps_rational<inf_rational> value(theory_var v);
        virtual theory_var add_objective(app* term);
        virtual expr_ref mk_ge(filter_model_converter& fm, theory_var v, inf_numeral const& val);
        void enable_record_conflict(expr* bound);
        void record_conflict(unsigned num_lits, literal const * lits, 
                          unsigned num_eqs, enode_pair const * eqs,
                          unsigned num_params, parameter* params);
        inf_eps_rational<inf_rational> conflict_minimize();
    private:
        virtual expr_ref mk_gt(theory_var v);

        bool_var m_bound_watch;
        inf_eps_rational<inf_rational> m_upper_bound;
        bool get_theory_vars(expr * n, uint_set & vars);
    public:
        // -----------------------------------
        //
        // Pretty Printing
        //
        // -----------------------------------
    public:
        virtual void collect_statistics(::statistics & st) const;
        virtual void display(std::ostream & out) const;
    protected:
        void display_row(std::ostream & out, unsigned r_id, bool compact = true) const;
        void display_row(std::ostream & out, row const & r, bool compact = true) const;
        void display_rows(std::ostream & out, bool compact = true) const;
        void display_row_info(std::ostream & out, unsigned r_id) const;
        void display_row_info(std::ostream & out, row const & r) const;
        bool is_one_minus_one_row(row const & r) const;
        void display_row_shape(std::ostream & out, row const & r) const;
        void display_rows_shape(std::ostream & out) const;
        void display_rows_stats(std::ostream & out) const;
        void display_rows_bignums(std::ostream & out) const;
        void display_simplified_row(std::ostream & out, row const & r) const;
        void display_var(std::ostream & out, theory_var v) const;
        void display_vars(std::ostream & out) const;
        void display_bound(std::ostream & out, bound * b, unsigned indent = 0) const;
        void display_atoms(std::ostream & out) const;
        void display_asserted_atoms(std::ostream & out) const;
        void display_atom(std::ostream & out, atom * a, bool show_sign) const;
        void display_bounds_in_smtlib(std::ostream & out) const;
        void display_bounds_in_smtlib() const;
        void display_nl_monomials(std::ostream & out) const;
        void display_coeff_exprs(std::ostream & out, sbuffer<coeff_expr> const & p) const;
        void display_interval(std::ostream& out, interval const& i);
        void display_deps(std::ostream& out, v_dependency* dep);

    protected:
        // -----------------------------------
        //
        // Debugging
        //
        // -----------------------------------
#ifdef Z3DEBUG
        bool check_vector_sizes() const;
        bool check_null_var_pos() const;
        bool has_var_kind(unsigned r_id, var_kind k) const;
        bool wf_row(unsigned r_id) const;
        bool wf_rows() const;
        bool wf_column(theory_var v) const;
        bool wf_columns() const;
        bool valid_assignment() const;
        bool valid_row_assignment() const;
        bool valid_row_assignment(row const & r) const;
        bool satisfy_bounds() const;
        bool satisfy_integrality() const;
#endif
    };
    
    class mi_ext {
    public:
        typedef rational     numeral;
        typedef inf_rational inf_numeral;
        inf_numeral   m_int_epsilon;
        inf_numeral   m_real_epsilon;
        numeral fractional_part(inf_numeral const& n) {
            SASSERT(n.is_rational());
            return n.get_rational() - floor(n);
        }
        static numeral fractional_part(numeral const & n) {
            return n - floor(n);
        }
        static inf_numeral mk_inf_numeral(numeral const & n, numeral const & r) {
            return inf_numeral(n, r);
        }
        static bool is_infinite(inf_numeral const& ) { return false; }
        mi_ext() : m_int_epsilon(rational(1)), m_real_epsilon(rational(0), true) {}
    };

    class i_ext {
    public:
        typedef rational     numeral;
        typedef rational inf_numeral;
        numeral m_int_epsilon;
        numeral m_real_epsilon;
        static numeral fractional_part(numeral const & n) {
            return n - floor(n);
        }
        static inf_numeral mk_inf_numeral(numeral const& n, numeral const& i) {
            UNREACHABLE();
            return inf_numeral(n);
        }
        static bool is_infinite(inf_numeral const& ) { return false; }

        i_ext() : m_int_epsilon(1), m_real_epsilon(1) {}
    };

    class si_ext {
    public:
        typedef s_integer  numeral;
        typedef s_integer  inf_numeral;
        numeral m_int_epsilon;
        numeral m_real_epsilon;
        static numeral fractional_part(inf_numeral const & n) {
            return n - floor(n);
        }
        static inf_numeral mk_inf_numeral(numeral const& n, numeral const& i) {
            UNREACHABLE();
            return inf_numeral(n);
        }
        static bool is_infinite(inf_numeral const& ) { return false; }

        si_ext(): m_int_epsilon(s_integer(1)), m_real_epsilon(s_integer(1)) {}
    };
    
    class smi_ext {
    public:
        typedef s_integer      numeral;
        typedef inf_s_integer  inf_numeral;
        inf_numeral m_int_epsilon;
        inf_numeral m_real_epsilon;
        static numeral fractional_part(const numeral & n) {
            UNREACHABLE();
            return numeral(0);
        }
        static numeral fractional_part(const inf_numeral & n) {
            UNREACHABLE();
            return numeral(0);
        }
        static inf_numeral mk_inf_numeral(numeral const& n, numeral const& i) {
            return inf_numeral(n, i);
        }
        static bool is_infinite(inf_numeral const& ) { return false; }

        smi_ext() : m_int_epsilon(s_integer(1)), m_real_epsilon(s_integer(0), true) {}
    };

    class inf_ext {
    public:
        typedef rational     numeral;
        typedef inf_eps_rational<inf_rational>      inf_numeral;
        inf_numeral   m_int_epsilon;
        inf_numeral   m_real_epsilon;
        numeral fractional_part(inf_numeral const& n) {
            SASSERT(n.is_rational());
            return n.get_rational() - floor(n);
        }
        static numeral fractional_part(numeral const & n) {
            return n - floor(n);
        }
        static inf_numeral mk_inf_numeral(numeral const & n, numeral const & r) {
            return inf_numeral(inf_rational(n, r));
        }
        static bool is_infinite(inf_numeral const& n) { 
            return !n.get_infinity().is_zero(); 
        }

        inf_ext() : m_int_epsilon(inf_rational(rational(1))), m_real_epsilon(inf_rational(rational(0), true)) {}
    };

    
    typedef theory_arith<mi_ext> theory_mi_arith;
    typedef theory_arith<i_ext> theory_i_arith;
    typedef smt::theory_arith<inf_ext> theory_inf_arith;
    // typedef theory_arith<si_ext> theory_si_arith;
    // typedef theory_arith<smi_ext> theory_smi_arith;

    
};

#endif /* _THEORY_ARITH_H_ */

