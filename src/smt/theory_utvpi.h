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

#ifndef THEORY_UTVPI_H_
#define THEORY_UTVPI_H_

#include"theory_diff_logic.h"

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
            ~atom() {}
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
        th_var                  m_zero; //cache the variable representing the zero variable.

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
        

        // Set a conflict due to a negative cycle.
        void set_conflict();
               
        void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {}

        // Create a new theory variable.
        virtual th_var mk_var(enode* n);

        virtual th_var mk_var(expr* n);
                                
        void compute_delta();

        void found_non_utvpi_expr(expr * n);

        bool is_interpreted(app* n) const {
            return n->get_family_id() == get_family_id();
        }

    public:    
        theory_utvpi(ast_manager& m);

        virtual ~theory_utvpi();

        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_utvpi, get_manager()); }

        virtual char const * get_name() const { return "utvpi-logic"; }

        /**
           \brief See comment in theory::mk_eq_atom
        */
        virtual app * mk_eq_atom(expr * lhs, expr * rhs) { return a.mk_eq(lhs, rhs); }

        virtual void init(context * ctx);

        virtual bool internalize_atom(app * atom, bool gate_ctx);
                                                     
        virtual bool internalize_term(app * term);

        virtual void internalize_eq_eh(app * atom, bool_var v);

        virtual void assign_eh(bool_var v, bool is_true);

        virtual void new_eq_eh(th_var v1, th_var v2) {
            m_stats.m_num_core2th_eqs++;
            m_arith_eq_adapter.new_eq_eh(v1, v2);
        }

        virtual bool use_diseqs() const { return true; }

        virtual void new_diseq_eh(th_var v1, th_var v2) {
            m_arith_eq_adapter.new_diseq_eh(v1, v2);
        }

        virtual void push_scope_eh();

        virtual void pop_scope_eh(unsigned num_scopes);

        virtual void restart_eh() {
            m_arith_eq_adapter.restart_eh();
        }

        virtual void relevant_eh(app* e) {}

        virtual void init_search_eh() {
            m_arith_eq_adapter.init_search_eh();
        }

        virtual final_check_status final_check_eh();

        virtual bool is_shared(th_var v) const {
            return false;
        }
    
        virtual bool can_propagate() {
            SASSERT(m_asserted_qhead <= m_asserted_atoms.size());
            return m_asserted_qhead != m_asserted_atoms.size();
        }
        
        virtual void propagate();
        
        virtual justification * why_is_diseq(th_var v1, th_var v2) {
            UNREACHABLE();
            return 0;
        }

        virtual void reset_eh();

        virtual void init_model(model_generator & m);
        
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

        virtual bool validate_eq_in_model(th_var v1, th_var v2, bool is_true) const {
            return true;
        }
                
        virtual void display(std::ostream & out) const;
        
        virtual void collect_statistics(::statistics & st) const;

    private:        

        rational mk_value(theory_var v, bool is_int);

        bool is_parity_ok(unsigned v) const;

        void enforce_parity();

        void validate_model();

        bool eval(expr* e);

        rational eval_num(expr* e);

        bool check_z_consistency();

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
        
        th_var get_zero(sort* s) const { return m_zero; }

        th_var get_zero(expr* e) const { return get_zero(get_manager().get_sort(e)); }

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




#endif /* THEORY_UTVPI_H_ */
