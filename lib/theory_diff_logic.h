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

#ifndef _THEORY_DIFF_LOGIC_H_
#define _THEORY_DIFF_LOGIC_H_

#include"rational.h"
#include"inf_rational.h"
#include"inf_int_rational.h"
#include"s_integer.h"
#include"inf_s_integer.h"
#include"smt_theory.h"
#include"diff_logic.h"
#include"arith_decl_plugin.h"
#include"smt_justification.h"
#include"map.h"
#include"front_end_params.h"
#include"arith_eq_adapter.h"
#include"smt_model_generator.h"
#include"numeral_factory.h"
#include"smt_clause.h"


// The DL theory can represent term such as n + k, where n is an enode and k is a numeral.
namespace smt {

    struct theory_diff_logic_statistics {
        unsigned   m_num_conflicts;
        unsigned   m_num_assertions;
        unsigned   m_num_th2core_eqs;
        unsigned   m_num_th2core_prop;

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

    class dl_conflict : public simple_justification {
    public:
        dl_conflict(region & r, unsigned nls, literal const * lits): simple_justification(r, nls, lits) { }
            
        virtual proof * mk_proof(conflict_resolution & cr) { 
            NOT_IMPLEMENTED_YET();
            return 0;
        }
    };


    template<typename Ext>
    class theory_diff_logic : public theory, private Ext {
        
        typedef typename Ext::numeral numeral;

        class implied_eq_justification : public justification {
            theory_diff_logic & m_theory;
            theory_var          m_v1;
            theory_var          m_v2;
            unsigned            m_timestamp;
        public:
            implied_eq_justification(theory_diff_logic & theory, theory_var v1, theory_var v2, unsigned ts):
                m_theory(theory), 
                m_v1(v1), 
                m_v2(v2), 
                m_timestamp(ts) {
            }

            virtual void get_antecedents(conflict_resolution & cr) {
                m_theory.get_eq_antecedents(m_v1, m_v2, m_timestamp, cr);
            }

            virtual proof * mk_proof(conflict_resolution & cr) { NOT_IMPLEMENTED_YET(); return 0; }
        };

        class implied_bound_justification : public justification {
            theory_diff_logic& m_theory;
            edge_id            m_subsumed_edge;
            edge_id            m_bridge_edge;
        public:
            implied_bound_justification(theory_diff_logic & theory, edge_id se, edge_id be):
                m_theory(theory), 
                m_subsumed_edge(se),
                m_bridge_edge(be) {
            }

            virtual void get_antecedents(conflict_resolution & cr) {
                m_theory.get_implied_bound_antecedents(m_bridge_edge, m_subsumed_edge, cr);
            }

            virtual proof * mk_proof(conflict_resolution & cr) { NOT_IMPLEMENTED_YET(); return 0; }            
        };

        enum atom_kind {
            LE_ATOM,
            EQ_ATOM
        };

        class atom {
        protected:
            atom_kind m_kind;
            bool_var  m_bvar;
            bool      m_true;
        public:
            atom(atom_kind k, bool_var bv) : m_kind(k), m_bvar(bv), m_true(false) {}
            virtual ~atom() {}
            atom_kind kind() const { return m_kind; }
            bool_var get_bool_var() const { return m_bvar; }
            bool is_true() const { return m_true; }
            void assign_eh(bool is_true) { m_true = is_true; }
            virtual std::ostream& display(theory_diff_logic const& th, std::ostream& out) const;
        };
        
        class le_atom : public atom {
            int                 m_pos;
            int                 m_neg;
        public:
            le_atom(bool_var bv, int pos, int neg):
                atom(LE_ATOM, bv),
                m_pos(pos),
                m_neg(neg) {
            }
            virtual ~le_atom() {}
            int get_asserted_edge() const { return this->m_true?m_pos:m_neg; }
            int get_pos() const { return m_pos; }
            int get_neg() const { return m_neg; }
            virtual std::ostream& display(theory_diff_logic const& th, std::ostream& out) const;
        };

        class eq_atom : public atom {
            app_ref m_le;
            app_ref m_ge;
        public:
            eq_atom(bool_var bv, app_ref& le, app_ref& ge):
                atom(EQ_ATOM, bv), 
                m_le(le),
                m_ge(ge)
            {}
            virtual ~eq_atom() {}
            virtual std::ostream& display(theory_diff_logic const& th, std::ostream& out) const;
            app* get_le() const { return m_le.get(); }
            app* get_ge() const { return m_ge.get(); }
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

        class theory_diff_logic_del_eh : public clause_del_eh {
            theory_diff_logic& m_super;
        public:
            theory_diff_logic_del_eh(theory_diff_logic& s) : m_super(s) {}
            virtual ~theory_diff_logic_del_eh() {}
            virtual void operator()(ast_manager&, clause* cls) {
                TRACE("dl_activity", tout << "deleting " << cls << "\n";);
                m_super.del_clause_eh(cls);
                dealloc(this);
            }
        };

        front_end_params &             m_params;
        arith_util                     m_util;
        arith_eq_adapter               m_arith_eq_adapter;
        theory_diff_logic_statistics   m_stats;
        dl_graph<GExt>                 m_graph;
        theory_var                     m_zero_int; // cache the variable representing the zero variable.
        theory_var                     m_zero_real; // cache the variable representing the zero variable.
        int_vector                     m_scc_id;                  // Cheap equality propagation
        bool                           m_modified_since_eq_prop;  // true if new constraints were asserted 
                                                                  // since last eq propagation.
        eq_prop_info_set               m_eq_prop_info_set;        // set of existing equality prop infos
        ptr_vector<eq_prop_info>       m_eq_prop_infos;

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

        // Set a conflict due to a negative cycle.
        void set_neg_cycle_conflict();
               
        void new_edge(dl_var src, dl_var dst, unsigned num_edges, edge_id const* edges);

        // Create a new theory variable.
        virtual theory_var mk_var(enode* n);

        virtual theory_var mk_var(app* n);
                
        void mark_as_modified_since_eq_prop();
        
        void unmark_as_modified_since_eq_prop();
        
        bool propagate_cheap_equalities();

        void compute_delta();

        void found_non_diff_logic_expr(expr * n);

        bool is_interpreted(app* n) const;

        void del_clause_eh(clause* cls);

    public:    
        theory_diff_logic(ast_manager& m, front_end_params & params):
            theory(m.get_family_id("arith")),
            m_params(params),
            m_util(m),
            m_arith_eq_adapter(*this, params, m_util),
            m_zero_int(null_theory_var),
            m_zero_real(null_theory_var),
            m_modified_since_eq_prop(false),
            m_asserted_qhead(0),
            m_num_core_conflicts(0),
            m_num_propagation_calls(0),
            m_agility(0.5),
            m_is_lia(true),
            m_non_diff_logic_exprs(false),
            m_factory(0),
            m_nc_functor(*this) {
        }            

        ~theory_diff_logic() {
            reset_eh();
        }

        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_diff_logic, get_manager(), m_params); }

        virtual char const * get_name() const { return "difference-logic"; }

        /**
           \brief See comment in theory::mk_eq_atom
        */
        virtual app * mk_eq_atom(expr * lhs, expr * rhs) { return m_util.mk_eq(lhs, rhs); }

        virtual void init(context * ctx);

        virtual bool internalize_atom(app * atom, bool gate_ctx);
                                                     
        virtual bool internalize_term(app * term);

        virtual void internalize_eq_eh(app * atom, bool_var v);

        virtual void assign_eh(bool_var v, bool is_true);

        virtual void new_eq_eh(theory_var v1, theory_var v2);

        virtual bool use_diseqs() const { return true; }

        virtual void new_diseq_eh(theory_var v1, theory_var v2);

        virtual void push_scope_eh();

        virtual void pop_scope_eh(unsigned num_scopes);

        virtual void restart_eh() {
            m_arith_eq_adapter.restart_eh();
        }

        virtual void relevant_eh(app* e);

        virtual void init_search_eh() {
            m_arith_eq_adapter.init_search_eh();
        }

        virtual final_check_status final_check_eh();

        virtual bool is_shared(theory_var v) const {
            return false;
        }
    
        virtual bool can_propagate() {
            return m_asserted_qhead != m_asserted_atoms.size();
        }
        
        virtual void propagate();
        
        virtual justification * why_is_diseq(theory_var v1, theory_var v2) {
            NOT_IMPLEMENTED_YET();
            return 0;
        }

        // virtual void flush_eh();

        virtual void reset_eh();

        virtual void init_model(model_generator & m);
        
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

        virtual bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const;
                
        virtual void display(std::ostream & out) const;
        
        virtual void collect_statistics(::statistics & st) const;

    private:        

        virtual void new_eq_eh(theory_var v1, theory_var v2, justification& j);

        virtual void new_diseq_eh(theory_var v1, theory_var v2, justification& j);

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

        theory_var get_zero(sort* s) const { return m_util.is_int(s)?m_zero_int:m_zero_real; }

        theory_var get_zero(expr* e) const { return get_zero(get_manager().get_sort(e)); }

        void inc_conflicts();

    };

    struct idl_ext {
        // TODO: It doesn't need to be a rational, but a bignum integer.
        static const bool m_int_theory = true;
        typedef rational numeral;
        numeral     m_epsilon;
        idl_ext() : m_epsilon(1) {}
    };

    struct sidl_ext {
        // TODO: It doesn't need to be a rational, but a bignum integer.
        static const bool m_int_theory = true;
        typedef s_integer numeral;
        numeral m_epsilon;
        sidl_ext() : m_epsilon(1) {}
    };

    struct rdl_ext {
        static const bool m_int_theory = false;
        typedef inf_int_rational numeral;
        numeral      m_epsilon;
        rdl_ext() : m_epsilon(rational(), true) {}
    };

    struct srdl_ext {
        static const bool m_int_theory = false;
        typedef inf_s_integer numeral;
        numeral m_epsilon;
        srdl_ext() : m_epsilon(s_integer(0),true) {}
    };


    typedef theory_diff_logic<idl_ext>  theory_idl;
    typedef theory_diff_logic<sidl_ext> theory_fidl;
    typedef theory_diff_logic<rdl_ext> theory_rdl;
    typedef theory_diff_logic<srdl_ext> theory_frdl;
};




#endif /* _THEORY_DIFF_LOGIC_H_ */
