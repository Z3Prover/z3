/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_dense_diff_logic.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-16.

Revision History:

TODO: eager equality propagation

--*/
#ifndef THEORY_DENSE_DIFF_LOGIC_H_
#define THEORY_DENSE_DIFF_LOGIC_H_

#include"theory_arith.h"
#include"theory_arith_params.h"
#include"arith_decl_plugin.h"
#include"arith_eq_adapter.h"
#include"theory_opt.h"


namespace smt {

    struct theory_dense_diff_logic_statistics {
        unsigned  m_num_assertions;
        unsigned  m_num_propagations;
        void reset() {
            m_num_assertions         = 0;
            m_num_propagations       = 0;
        }
        theory_dense_diff_logic_statistics() {
            reset();
        }
    };
    
    template<typename Ext>
    class theory_dense_diff_logic : public theory, public theory_opt, private Ext {
    public:
        theory_dense_diff_logic_statistics      m_stats;

    private:
        typedef typename Ext::inf_numeral numeral;

        class atom {
            typedef typename Ext::inf_numeral numeral;
            bool_var                  m_bvar;
            theory_var                m_source;
            theory_var                m_target;
            numeral                   m_offset;
            
        public:
            atom(bool_var bv, theory_var source, theory_var target, numeral const & offset):
                m_bvar(bv),
                m_source(source),
                m_target(target),
                m_offset(offset) {
            }
            
            bool_var get_bool_var() const { return m_bvar; }
            theory_var get_source() const { return m_source; }
            theory_var get_target() const { return m_target; }
            numeral const & get_offset() const { return m_offset; }
        };

        typedef ptr_vector<atom> atoms;
        typedef ptr_vector<atom> bool_var2atom;
        
        struct edge {
            theory_var  m_source;
            theory_var  m_target;
            numeral     m_offset;
            literal     m_justification;
            edge():m_source(null_theory_var), m_target(null_theory_var), m_justification(null_literal) {}
            edge(theory_var s, theory_var t, numeral const & offset, literal js):
                m_source(s), m_target(t), m_offset(offset), m_justification(js) {
            }
        };
        
        typedef int edge_id;
        typedef vector<edge> edges;
        static const edge_id null_edge_id = -1;
        static const edge_id self_edge_id = 0;
        
        struct cell {
            edge_id   m_edge_id;
            numeral   m_distance;
            atoms     m_occs;   
            cell():
                m_edge_id(null_edge_id) {
            }
        };
        
        struct cell_trail {
            unsigned short m_source;
            unsigned short m_target;
            edge_id        m_old_edge_id;
            numeral        m_old_distance;
            cell_trail(unsigned short s, unsigned short t, edge_id old_edge_id, numeral const & old_distance):
                m_source(s), m_target(t), m_old_edge_id(old_edge_id), m_old_distance(old_distance) {}
        };
        
        typedef vector<cell> row;
        typedef vector<row>  matrix;
        
        struct scope {
            unsigned  m_atoms_lim;
            unsigned  m_edges_lim;
            unsigned  m_cell_trail_lim;
        };
        
        theory_arith_params & m_params;
        arith_util            m_autil;
        arith_eq_adapter      m_arith_eq_adapter;
        atoms                 m_atoms;
        atoms                 m_bv2atoms;
        edges                 m_edges;  // list of asserted edges
        matrix                m_matrix;
        svector<bool>         m_is_int;
        vector<cell_trail>    m_cell_trail;
        svector<scope>        m_scopes;
        bool                  m_non_diff_logic_exprs;

        // For optimization purpose
        typedef vector <std::pair<theory_var, rational> > objective_term;
        vector<objective_term>         m_objectives;
        vector<rational>               m_objective_consts;
        vector<expr_ref_vector>        m_objective_assignments;

        struct f_target {
            theory_var m_target;
            numeral    m_new_distance;
        };

        typedef std::pair<theory_var, theory_var> var_pair;
        typedef vector<f_target>                  f_targets;

        literal_vector        m_tmp_literals;
        svector<var_pair>     m_tmp_pairs;
        f_targets             m_f_targets;
    
        vector<numeral>       m_assignment;

        struct var_value_hash;
        friend struct var_value_hash;
        struct var_value_hash {
            theory_dense_diff_logic & m_th;
            var_value_hash(theory_dense_diff_logic & th):m_th(th) {}
            unsigned operator()(theory_var v) const { return m_th.m_assignment[v].hash(); }
        };

        struct var_value_eq;
        friend struct var_value_eq;
        struct var_value_eq {
            theory_dense_diff_logic & m_th;
            var_value_eq(theory_dense_diff_logic & th):m_th(th) {}
            bool operator()(theory_var v1, theory_var v2) const { return m_th.m_assignment[v1] == m_th.m_assignment[v2] && m_th.is_int(v1) == m_th.is_int(v2); }
        };

        typedef int_hashtable<var_value_hash, var_value_eq> var_value_table;
        var_value_table             m_var_value_table;
    
        // -----------------------------------
        //
        // Auxiliary
        //
        // -----------------------------------
        bool is_int(theory_var v) const { return m_is_int[v]; }
        bool is_real(theory_var v) const { return !is_int(v); }
        numeral const & get_epsilon(theory_var v) const { return is_real(v) ? this->m_real_epsilon : this->m_int_epsilon; }
        bool is_times_minus_one(expr * n, app * & r) const { 
            expr * _r;
            if (m_autil.is_times_minus_one(n, _r)) { r = to_app(_r); return true; }
            return false; 
        }
        app * mk_zero_for(expr * n);
        theory_var mk_var(enode * n);
        theory_var internalize_term_core(app * n);
        void found_non_diff_logic_expr(expr * n);
        bool is_connected(theory_var source, theory_var target) const { return m_matrix[source][target].m_edge_id != null_edge_id; }
        void mk_clause(literal l1, literal l2);
        void mk_clause(literal l1, literal l2, literal l3);
        void add_edge(theory_var source, theory_var target, numeral const & offset, literal l);
        void update_cells();
        void propagate_using_cell(theory_var source, theory_var target);
        void get_antecedents(theory_var source, theory_var target, literal_vector & result);
        void assign_literal(literal l, theory_var source, theory_var target);
        void restore_cells(unsigned old_size);
        void del_atoms(unsigned old_size);
        void del_vars(unsigned old_num_vars);
        void init_model();
        bool internalize_objective(expr * n, rational const& m, rational& r, objective_term & objective);
        expr_ref mk_ineq(theory_var v, inf_rational const& val, bool is_strict);
#ifdef Z3DEBUG
        bool check_vector_sizes() const;
        bool check_matrix() const;
#endif        
    public:
        numeral const & get_distance(theory_var source, theory_var target) const {
            SASSERT(is_connected(source, target));
            return m_matrix[source][target].m_distance;
        }

        // -----------------------------------
        //
        // Internalization
        //
        // -----------------------------------
        virtual bool internalize_atom(app * n, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual void internalize_eq_eh(app * atom, bool_var v);
        virtual void apply_sort_cnstr(enode * n, sort * s);
        
        virtual void assign_eh(bool_var v, bool is_true);
        virtual void new_eq_eh(theory_var v1, theory_var v2);
        virtual bool use_diseqs() const;
        virtual void new_diseq_eh(theory_var v1, theory_var v2);

        virtual void conflict_resolution_eh(app * atom, bool_var v);

        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        
        virtual void restart_eh();
        virtual void init_search_eh();
        virtual final_check_status final_check_eh();
        
        virtual bool can_propagate();
        virtual void propagate();
        
        virtual void flush_eh();
        virtual void reset_eh();
        
        bool dump_lemmas() const { return m_params.m_arith_dump_lemmas; }

        virtual bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const;

        virtual void display(std::ostream & out) const;
        virtual void display_atom(std::ostream & out, atom * a) const;
        virtual void collect_statistics(::statistics & st) const;

        // -----------------------------------
        //
        // Model generation
        //
        // -----------------------------------
        arith_factory *    m_factory;
        rational           m_epsilon;
        // void update_epsilon(const inf_numeral & l, const inf_numeral & u);
        void compute_epsilon();
        void fix_zero();

        virtual void init_model(model_generator & m);
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

        // -----------------------------------
        //
        // Optimization
        //
        // -----------------------------------

        virtual inf_eps_rational<inf_rational> maximize(theory_var v, expr_ref& blocker, bool& has_shared);
        virtual inf_eps_rational<inf_rational> value(theory_var v);
        virtual theory_var add_objective(app* term);
        virtual expr_ref mk_gt(theory_var v, inf_rational const& val);
        virtual expr_ref mk_ge(filter_model_converter& fm, theory_var v, inf_rational const& val);
        
        // -----------------------------------
        //
        // Main
        //
        // -----------------------------------
    public:
        theory_dense_diff_logic(ast_manager & m, theory_arith_params & p);
        virtual ~theory_dense_diff_logic() { reset_eh(); }
        
        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_dense_diff_logic, get_manager(), m_params); }

        virtual char const * get_name() const { return "difference-logic"; }

        /**
           \brief See comment in theory::mk_eq_atom
        */
        virtual app * mk_eq_atom(expr * lhs, expr * rhs) { return m_autil.mk_eq(lhs, rhs); }
    };

    typedef theory_dense_diff_logic<mi_ext>  theory_dense_mi;
    typedef theory_dense_diff_logic<i_ext>   theory_dense_i;
    typedef theory_dense_diff_logic<smi_ext> theory_dense_smi;
    typedef theory_dense_diff_logic<si_ext>  theory_dense_si;
};

#endif /* THEORY_DENSE_DIFF_LOGIC_H_ */

