/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_utvpi.h

Abstract:

    use Bellman Ford traversal algorithm for UTVPI.    

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-26

Revision History:

    The implementaton is derived from theory_diff_logic.

--*/

#pragma once

#include "smt/theory_diff_logic.h"

namespace smt {

    class utvpi_tester {
        ast_manager&      m;
        arith_util        a;
        ptr_vector<expr>  m_todo;
        ast_mark          m_mark;
        obj_map<expr, rational>           m_coeff_map;
        rational                          m_weight;
        vector<std::pair<expr*, rational> >   m_terms;

    public:
        utvpi_tester(ast_manager& m);

        // test if formula is in the Horn inequality fragment:
        bool operator()(expr* fml);
        bool operator()(unsigned num_fmls, expr* const* fmls);

        // linearize inequality/equality
        bool linearize(expr* e);
        bool linearize(expr* e1, expr* e2);

        // retrieve linearization        
        vector<std::pair<expr*, rational> > const& get_linearization() const;        
        rational const& get_weight() const { return m_weight; }
    private:
        bool linearize();
    };

    template<typename Ext>
    class theory_utvpi : public theory, private Ext {
        
        typedef typename Ext::numeral numeral;
        typedef theory_var th_var;
        typedef svector<th_var> th_var_vector;
        typedef vector<std::pair<th_var, rational> >  coeffs;

        class assignment_trail;
        class parent_trail;

        struct GExt : public Ext {
            typedef std::pair<literal,unsigned> explanation;
        };

        class atom {
        protected:
            bool_var m_bvar;
            bool     m_true;
            int      m_pos;
            int      m_neg;
        public:
            atom(bool_var bv, int pos, int neg) : 
                m_bvar(bv), m_true(false),
                m_pos(pos), m_neg(neg) {}
            bool_var get_bool_var() const { return m_bvar; }
            void assign_eh(bool is_true) { m_true = is_true; }
            int get_asserted_edge() const { return this->m_true?m_pos:m_neg; }
            int get_pos() const { return m_pos; }
            int get_neg() const { return m_neg; }
            std::ostream& display(theory_utvpi const& th, std::ostream& out) const;
        };
        typedef svector<atom> atoms;
        
        struct scope {
            unsigned   m_atoms_lim;
            unsigned   m_asserted_atoms_lim;
            unsigned   m_asserted_qhead_old;
        };

        struct stats {
            unsigned   m_num_conflicts;
            unsigned   m_num_assertions;
            unsigned   m_num_core2th_eqs;
            unsigned   m_num_core2th_diseqs;

            void reset() {
                memset(this, 0, sizeof(*this));
            }

            stats() {
                reset();
            }
        };

        // Functor used to collect the proofs for a conflict due to 
        // a negative cycle.
        class nc_functor {
            literal_vector m_antecedents;
            unsigned_vector m_coeffs;
            theory_utvpi& m_super;
        public:
            nc_functor(theory_utvpi& s) : m_super(s) {}
            void reset() { m_antecedents.reset(); m_coeffs.reset(); }
            literal_vector const& get_lits() const { return m_antecedents; }
            unsigned_vector const& get_coeffs() const { return m_coeffs; }

            void operator()(std::pair<literal,unsigned> const & ex) {
                if (ex.first != null_literal) {
                    m_antecedents.push_back(ex.first);
                    m_coeffs.push_back(ex.second);
                }
            }

            void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {
                m_super.new_edge(src, dst, num_edges, edges);
            }
        };


        stats                   m_stats;        
        smt_params              m_params;
        arith_util              a;
        arith_eq_adapter        m_arith_eq_adapter;
        bool                    m_consistent;
        th_var                  m_izero, m_rzero; //cache the variable representing the zero variable.

        dl_graph<GExt>          m_graph;
        nc_functor              m_nc_functor;
        atoms                   m_atoms;
        unsigned_vector         m_asserted_atoms;   // set of asserted atoms
        unsigned                m_asserted_qhead;   
        u_map<unsigned>         m_bool_var2atom;
        svector<scope>          m_scopes;

        double                  m_agility;
        bool                    m_lia;
        bool                    m_lra;
        bool                    m_non_utvpi_exprs;

        utvpi_tester            m_test;


        arith_factory *         m_factory;
        rational                m_delta;
        
        struct var_value_hash;
        friend struct var_value_hash;
        struct var_value_hash {
            theory_utvpi & m_th;
            var_value_hash(theory_utvpi & th):m_th(th) {}
            unsigned operator()(theory_var v) const { return m_th.mk_value(v, false).hash(); }
        };

        struct var_value_eq;
        friend struct var_value_eq;
        struct var_value_eq {
            theory_utvpi & m_th;
            var_value_eq(theory_utvpi & th):m_th(th) {}
            bool operator()(theory_var v1, theory_var v2) const { return m_th.mk_value(v1, false) == m_th.mk_value(v2, false) && m_th.is_int(v1) == m_th.is_int(v2); }
        };

        typedef int_hashtable<var_value_hash, var_value_eq> var_value_table;
        var_value_table             m_var_value_table;


        // Set a conflict due to a negative cycle.
        void set_conflict();
               
        void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {}

        // Create a new theory variable.
        th_var mk_var(enode* n) override;

        virtual th_var mk_var(expr* n);
                                
        void compute_delta();

        void found_non_utvpi_expr(expr * n);

        bool is_interpreted(app* n) const {
            return n->get_family_id() == get_family_id();
        }

    public:    
        theory_utvpi(context& ctx);

        ~theory_utvpi() override;

        theory * mk_fresh(context * new_ctx) override;

        char const * get_name() const override { return "utvpi-logic"; }
        
        void init() override {  init_zero(); }

        /**
           \brief See comment in theory::mk_eq_atom
        */
        app * mk_eq_atom(expr * lhs, expr * rhs) override { return a.mk_eq(lhs, rhs); }

        bool internalize_atom(app * atom, bool gate_ctx) override;
                                                     
        bool internalize_term(app * term) override;

        void internalize_eq_eh(app * atom, bool_var v) override;

        void assign_eh(bool_var v, bool is_true) override;

        void new_eq_eh(th_var v1, th_var v2) override {
            m_stats.m_num_core2th_eqs++;
            m_arith_eq_adapter.new_eq_eh(v1, v2);
        }

        bool use_diseqs() const override { return true; }

        void new_diseq_eh(th_var v1, th_var v2) override {
            m_arith_eq_adapter.new_diseq_eh(v1, v2);
        }

        void push_scope_eh() override;

        void pop_scope_eh(unsigned num_scopes) override;

        void restart_eh() override {
            m_arith_eq_adapter.restart_eh();
        }

        void relevant_eh(app* e) override {}

        void init_search_eh() override {
            m_arith_eq_adapter.init_search_eh();
        }

        final_check_status final_check_eh() override;

        bool is_shared(th_var v) const override {
            return false;
        }
    
        bool can_propagate() override {
            SASSERT(m_asserted_qhead <= m_asserted_atoms.size());
            return m_asserted_qhead != m_asserted_atoms.size();
        }
        
        void propagate() override;
        
        justification * why_is_diseq(th_var v1, th_var v2) override {
            UNREACHABLE();
            return nullptr;
        }

        void reset_eh() override;

        void init_model(model_generator & m) override;
        
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
                
        void display(std::ostream & out) const override;
        
        void collect_statistics(::statistics & st) const override;

    private:        

        void init_model();

        bool assume_eqs_core();

        rational mk_value(theory_var v, bool is_int);

        bool is_parity_ok(unsigned v) const;

        void enforce_parity();

        bool eval(expr* e);

        void model_validate();

        rational eval_num(expr* e);

        bool check_z_consistency();

        bool has_shared();

        virtual void new_eq_eh(th_var v1, th_var v2, justification& j) {
            m_stats.m_num_core2th_eqs++;
            new_eq_or_diseq(true, v1, v2, j);
        }

        virtual void new_diseq_eh(th_var v1, th_var v2, justification& j) {
            m_stats.m_num_core2th_diseqs++;
            new_eq_or_diseq(false, v1, v2, j);    
        }

        void negate(coeffs& coeffs, rational& weight);
        numeral mk_weight(bool is_real, bool is_strict, rational const& w) const;
        void mk_coeffs(vector<std::pair<expr*,rational> >const& terms, coeffs& coeffs, rational& w);

        void del_atoms(unsigned old_size);

        bool propagate_atom(atom const& a);

        th_var mk_term(app* n);

        th_var mk_num(app* n, rational const& r);

        bool is_consistent() const;

        th_var expand(bool pos, th_var v, rational & k);

        void new_eq_or_diseq(bool is_eq, th_var v1, th_var v2, justification& eq_just);
        
        bool is_int(theory_var v) const { return a.is_int(get_enode(v)->get_expr()); }

        th_var get_zero(sort* s) { return a.is_int(s) ? m_izero : m_rzero; }

        th_var get_zero(expr* e) { return get_zero(e->get_sort()); }

        void init_zero();

        void inc_conflicts();

        edge_id add_ineq(vector<std::pair<th_var, rational> > const& terms, numeral const& weight, literal l);

        bool enable_edge(edge_id id);

        th_var to_var(th_var v) const { 
            return 2*v;
        }
        
        th_var from_var(th_var v) const {
            return v/2;
        }

        th_var pos(th_var v) const {
            return v & 0xFFFFFFFE;
        }

        th_var neg(th_var v) const {
            return v | 0x1;
        }

    };


    typedef theory_utvpi<rdl_ext>  theory_rutvpi;
    typedef theory_utvpi<idl_ext>  theory_iutvpi;
};




