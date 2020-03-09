/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    theory_diff_logic.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-04-21.
    Nikolaj Bjorner (nbjorner) 2008-05-05

Revision History:


--*/

#ifndef THEORY_DIFF_LOGIC_H_
#define THEORY_DIFF_LOGIC_H_

#include "util/rational.h"
#include "util/inf_rational.h"
#include "util/inf_int_rational.h"
#include "util/s_integer.h"
#include "util/inf_s_integer.h"
#include "util/map.h"
#include "ast/arith_decl_plugin.h"
#include "model/numeral_factory.h"
#include "smt/smt_theory.h"
#include "smt/diff_logic.h"
#include "smt/smt_justification.h"
#include "smt/params/smt_params.h"
#include "smt/arith_eq_adapter.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_clause.h"
#include "smt/theory_opt.h"
#include "math/simplex/simplex.h"
#include "math/simplex/simplex_def.h"

// The DL theory can represent term such as n + k, where n is an enode and k is a numeral.
namespace smt {

    struct theory_diff_logic_statistics {
        unsigned   m_num_conflicts;
        unsigned   m_num_assertions;
        unsigned   m_num_th2core_eqs;

        unsigned   m_num_core2th_eqs;
        unsigned   m_num_core2th_diseqs;
        unsigned   m_num_core2th_new_diseqs;
        void reset() {
            memset(this, 0, sizeof(*this));
        }
        theory_diff_logic_statistics() {
            reset();
        }
    };

    template<typename Ext>
    class theory_diff_logic : public theory, public theory_opt, private Ext {
        
        typedef typename Ext::numeral numeral;
        typedef simplex::simplex<simplex::mpq_ext> Simplex;
        typedef inf_eps_rational<inf_rational> inf_eps;

        class atom {
            bool_var  m_bvar;
            bool      m_true;
            int       m_pos;
            int       m_neg;
        public:
            atom(bool_var bv, int pos, int neg):
                m_bvar(bv), m_true(false),
                m_pos(pos),
                m_neg(neg) {
            }
            ~atom() {}
            bool_var get_bool_var() const { return m_bvar; }
            bool is_true() const { return m_true; }
            void assign_eh(bool is_true) { m_true = is_true; }
            int get_asserted_edge() const { return this->m_true?m_pos:m_neg; }
            int get_pos() const { return m_pos; }
            int get_neg() const { return m_neg; }
            std::ostream& display(theory_diff_logic const& th, std::ostream& out) const;
        };

        typedef ptr_vector<atom> atoms;
        typedef u_map<atom*>     bool_var2atom;
              

        // Auxiliary info for propagating cheap equalities
        class eq_prop_info {
            int        m_scc_id;
            numeral    m_delta;
            theory_var m_root;
        public:
            eq_prop_info(int scc_id, const numeral & d, theory_var r = null_theory_var):
                m_scc_id(scc_id),
                m_delta(d),
                m_root(r) {
            }

            theory_var get_root() const {
                return m_root;
            }

            unsigned hash() const { return mk_mix(static_cast<unsigned>(m_scc_id), m_delta.hash(), 0x9e3779b9); }

            bool operator==(const eq_prop_info & info) const {
                return m_scc_id == info.m_scc_id && m_delta == info.m_delta;
            }
        };
        
        struct eq_prop_info_hash_proc {
            unsigned operator()(eq_prop_info * info) const { 
                return info->hash();
            }
        };
        
        struct eq_prop_info_eq_proc {
            bool operator()(eq_prop_info * info1, eq_prop_info * info2) const {
                return *info1 == *info2;
            }
        };
        typedef ptr_hashtable<eq_prop_info, eq_prop_info_hash_proc, eq_prop_info_eq_proc> eq_prop_info_set;



        // Extension for diff_logic core.
  
        struct GExt : public Ext {
            typedef literal explanation;
        };
        
        // Functor used to collect the proofs for a conflict due to 
        // a negative cycle.
        class nc_functor {
            literal_vector m_antecedents;
            theory_diff_logic& m_super;
        public:
            nc_functor(theory_diff_logic& s) : m_super(s) {}
            void reset();
            literal_vector const& get_lits() const { return m_antecedents; }

            void operator()(literal const & ex) {
                if (ex != null_literal) {
                    m_antecedents.push_back(ex);
                }
            }

            void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges) {
                m_super.new_edge(src, dst, num_edges, edges);
            }
        };

        struct scope {
            unsigned      m_atoms_lim;
            unsigned      m_asserted_atoms_lim;
            unsigned      m_asserted_qhead_old;
        };
        typedef dl_graph<GExt> Graph;

        smt_params &                   m_params;
        arith_util                     m_util;
        arith_eq_adapter               m_arith_eq_adapter;
        theory_diff_logic_statistics   m_stats;
        Graph                          m_graph;
        theory_var                     m_izero, m_rzero; // cache the variable representing the zero variable.
        int_vector                     m_scc_id;                  // Cheap equality propagation
        eq_prop_info_set               m_eq_prop_info_set;        // set of existing equality prop infos
        ptr_vector<eq_prop_info>       m_eq_prop_infos;

        app_ref_vector                 m_terms;
        svector<bool>                  m_signs;

        ptr_vector<atom>               m_atoms;
        ptr_vector<atom>               m_asserted_atoms;   // set of asserted atoms
        unsigned                       m_asserted_qhead;   
        bool_var2atom                  m_bool_var2atom;
        svector<scope>                 m_scopes;

        unsigned                       m_num_core_conflicts;
        unsigned                       m_num_propagation_calls;
        double                         m_agility;
        bool                           m_is_lia;
        bool                           m_non_diff_logic_exprs;

        arith_factory *                m_factory;
        rational                       m_delta;
        nc_functor                     m_nc_functor;   

        // For optimization purpose
        typedef vector <std::pair<theory_var, rational> > objective_term;
        vector<objective_term>         m_objectives;
        vector<rational>               m_objective_consts;
        vector<expr_ref_vector>        m_objective_assignments;
        vector<Simplex::row>           m_objective_rows;
        Simplex                        m_S;
        unsigned                       m_num_simplex_edges;

        // Set a conflict due to a negative cycle.
        void set_neg_cycle_conflict();
               
        void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges);

        // Create a new theory variable.
        theory_var mk_var(enode* n) override;

        virtual theory_var mk_var(app* n);
                        
        void compute_delta();

        void found_non_diff_logic_expr(expr * n);

        bool is_interpreted(app* n) const {
            return get_family_id() == n->get_family_id();
        }

    public:    
        theory_diff_logic(ast_manager& m, smt_params & params):
            theory(m.mk_family_id("arith")),
            m_params(params),
            m_util(m),
            m_arith_eq_adapter(*this, params, m_util),
            m_izero(null_theory_var),
            m_rzero(null_theory_var),
            m_terms(m),
            m_asserted_qhead(0),
            m_num_core_conflicts(0),
            m_num_propagation_calls(0),
            m_agility(0.5),
            m_is_lia(true),
            m_non_diff_logic_exprs(false),
            m_factory(nullptr),
            m_nc_functor(*this),
            m_S(m.limit()),
            m_num_simplex_edges(0) {
        }            

        ~theory_diff_logic() override {
            reset_eh();
        }

        theory * mk_fresh(context * new_ctx) override;

        char const * get_name() const override { return "difference-logic"; }

        /**
           \brief See comment in theory::mk_eq_atom
        */
        app * mk_eq_atom(expr * lhs, expr * rhs) override { return m_util.mk_eq(lhs, rhs); }

        void init(context * ctx) override;

        bool internalize_atom(app * atom, bool gate_ctx) override;
                                                     
        bool internalize_term(app * term) override;

        void internalize_eq_eh(app * atom, bool_var v) override;

        void assign_eh(bool_var v, bool is_true) override;

        void new_eq_eh(theory_var v1, theory_var v2) override;

        bool use_diseqs() const override { return true; }

        void new_diseq_eh(theory_var v1, theory_var v2) override;

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

        bool is_shared(theory_var v) const override {
            return false;
        }
    
        bool can_propagate() override {
            return m_asserted_qhead != m_asserted_atoms.size();
        }
        
        void propagate() override;
        
        justification * why_is_diseq(theory_var v1, theory_var v2) override {
            NOT_IMPLEMENTED_YET();
            return nullptr;
        }

        // virtual void flush_eh();

        void reset_eh() override;

        void init_model(model_generator & m) override;
        
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
                
        void display(std::ostream & out) const override;
        
        void collect_statistics(::statistics & st) const override;

        
        // -----------------------------------
        //
        // Optimization
        //
        // -----------------------------------

        expr_ref mk_ge(generic_model_converter& fm, theory_var v, inf_eps const& val);
        inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared) override;
        inf_eps value(theory_var v) override;
        theory_var add_objective(app* term) override;

        bool internalize_objective(expr * n, rational const& m, rational& r, objective_term & objective);

    private:     

        expr_ref mk_gt(theory_var v, inf_eps const& val);

        expr_ref mk_ineq(theory_var v, inf_eps const& val, bool is_strict);

        virtual void new_eq_eh(theory_var v1, theory_var v2, justification& j);

        virtual void new_diseq_eh(theory_var v1, theory_var v2, justification& j);

        bool decompose_linear(app_ref_vector& args, svector<bool>& signs);

        bool is_sign(expr* n, bool& sign);

        bool is_negative(app* n, app*& m);

        void del_atoms(unsigned old_size);

        void propagate_core();

        bool propagate_atom(atom* a);

        theory_var mk_term(app* n);

        theory_var mk_num(app* n, rational const& r);

        bool is_offset(app* n, app*& v, app*& offset, rational& r);

        bool is_consistent() const;

        bool reflect() const { return m_params.m_arith_reflect; }

        bool theory_resolve() const { return m_params.m_theory_resolve; }

        unsigned lazy_pivoting_lvl() const { return m_params.m_arith_lazy_pivoting_lvl; }

        bool propagate_eqs() const { return m_params.m_arith_propagate_eqs; }

        bool dump_lemmas() const { return m_params.m_arith_dump_lemmas; }

        theory_var expand(bool pos, theory_var v, rational & k);

        void new_eq_or_diseq(bool is_eq, theory_var v1, theory_var v2, justification& eq_just);

        void get_eq_antecedents(theory_var v1, theory_var v2, unsigned timestamp, conflict_resolution & cr);

        void get_implied_bound_antecedents(edge_id bridge_edge, edge_id subsumed_edge, conflict_resolution & cr);

        void init_zero();

        theory_var get_zero(bool is_int) { return is_int ? m_izero : m_rzero; }

        void inc_conflicts();

        // Optimization:
        // convert variables, edges and objectives to simplex.
        unsigned node2simplex(unsigned v);
        unsigned edge2simplex(unsigned e);
        unsigned obj2simplex(unsigned v);
        unsigned num_simplex_vars();
        bool is_simplex_edge(unsigned e);
        unsigned simplex2edge(unsigned e);
        void update_simplex(Simplex& S);
    };

    struct idl_ext {
        // TODO: It doesn't need to be a rational, but a bignum integer.
        static const bool m_int_theory = true;
        typedef rational numeral;
        typedef rational fin_numeral;
        numeral     m_epsilon;
        idl_ext() : m_epsilon(1) {}
    };

    struct sidl_ext {
        static const bool m_int_theory = true;
        typedef s_integer numeral;
        typedef s_integer fin_numeral;
        numeral m_epsilon;
        sidl_ext() : m_epsilon(1) {}
    };

    struct rdl_ext {
        static const bool m_int_theory = false;
        typedef inf_int_rational numeral;
        typedef rational fin_numeral;
        numeral      m_epsilon;        
        rdl_ext() : m_epsilon(rational(), true) {}
    };

    //
    // there is no s_rational class, so 
    // instead we use multi-precision rationals.
    //
    struct srdl_ext : public rdl_ext {};

    typedef theory_diff_logic<idl_ext>  theory_idl;
    typedef theory_diff_logic<sidl_ext> theory_fidl;
    typedef theory_diff_logic<rdl_ext> theory_rdl;
    typedef theory_diff_logic<srdl_ext> theory_frdl;
};




#endif /* THEORY_DIFF_LOGIC_H_ */
