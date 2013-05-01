/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_horn_ineq.h

Abstract:
    
    A*x <= weight + D*x, coefficients to A and D are non-negative, 
    D is a diagonal matrix.
    Coefficients to weight may have both signs.
   
    Label variables by weight.
    Select inequality that is not satisfied.
    Set delta(LHS) := 0
    Set delta(RHS(x)) := weight(x) - b
    Propagate weight increment through inequalities.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-18

Revision History:

    The implementaton is derived from theory_diff_logic.

--*/

#ifndef _THEORY_HORN_INEQ_H_
#define _THEORY_HORN_INEQ_H_

#include"rational.h"
#include"inf_rational.h"
#include"inf_int_rational.h"
#include"inf_eps_rational.h"
#include"smt_theory.h"
#include"arith_decl_plugin.h"
#include"smt_justification.h"
#include"map.h"
#include"smt_params.h"
#include"arith_eq_adapter.h"
#include"smt_model_generator.h"
#include"numeral_factory.h"
#include"smt_clause.h"

namespace smt {

    class horn_ineq_tester {
        ast_manager&      m;
        arith_util        a;
        ptr_vector<expr>  m_todo;
        svector<lbool>    m_pols;
        ast_mark pos_mark, neg_mark;
        obj_map<expr, rational>               m_coeff_map;
        rational                              m_weight;
        vector<std::pair<expr*, rational> >   m_terms;

    public:
        enum classify_t {
            co_horn,
            horn,
            diff,
            non_horn
        };
        horn_ineq_tester(ast_manager& m);

        // test if formula is in the Horn inequality fragment:
        bool operator()(expr* fml);
        bool operator()(unsigned num_fmls, expr* const* fmls);

        // linearize inequality/equality
        classify_t linearize(expr* e);
        classify_t linearize(expr* e1, expr* e2);

        // retrieve linearization
        vector<std::pair<expr*,rational> > const& get_linearization() const;        
        rational const& get_weight() const { return m_weight; }
    private:
        bool test_expr(lbool p, expr* e);
        classify_t linearize();
    };

    template<typename Ext>
    class theory_horn_ineq : public theory, private Ext {
        
        typedef typename Ext::numeral numeral;
        typedef typename Ext::inf_numeral inf_numeral;
        typedef literal explanation;
        typedef theory_var th_var;
        typedef svector<th_var> th_var_vector;
        typedef unsigned clause_id;
        typedef vector<std::pair<th_var, rational> >  coeffs;
        static const clause_id null_clause_id = UINT_MAX;

        class clause;
        class graph;
        class assignment_trail;
        class parent_trail;

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
            virtual ~atom() {}
            bool_var get_bool_var() const { return m_bvar; }
            bool is_true() const { return m_true; }
            void assign_eh(bool is_true) { m_true = is_true; }
            int get_asserted_edge() const { return this->m_true?m_pos:m_neg; }
            int get_pos() const { return m_pos; }
            int get_neg() const { return m_neg; }
            std::ostream& display(theory_horn_ineq const& th, std::ostream& out) const;
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

        stats                   m_stats;        
        smt_params              m_params;
        arith_util              a;
        arith_eq_adapter        m_arith_eq_adapter;
        th_var                  m_zero_int; // cache the variable representing the zero variable.
        th_var                  m_zero_real; // cache the variable representing the zero variable.

        graph*                  m_graph;
        atoms                   m_atoms;
        unsigned_vector         m_asserted_atoms;   // set of asserted atoms
        unsigned                m_asserted_qhead;   
        u_map<unsigned>         m_bool_var2atom;
        svector<scope>          m_scopes;

        double                  m_agility;
        bool                    m_lia;
        bool                    m_lra;
        bool                    m_non_horn_ineq_exprs;

        horn_ineq_tester        m_test;


        arith_factory *         m_factory;
        rational                m_delta;
        rational                m_lambda;
        

        // Set a conflict due to a negative cycle.
        void set_neg_cycle_conflict();
               
        // Create a new theory variable.
        virtual th_var mk_var(enode* n);

        virtual th_var mk_var(expr* n);
                                
        void compute_delta();

        void found_non_horn_ineq_expr(expr * n);

        bool is_interpreted(app* n) const {
            return n->get_family_id() == get_family_id();
        }

    public:    
        theory_horn_ineq(ast_manager& m);

        virtual ~theory_horn_ineq();

        virtual theory * mk_fresh(context * new_ctx) { return alloc(theory_horn_ineq, get_manager()); }

        virtual char const * get_name() const { return "horn-inequality-logic"; }

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

        void propagate_core();

        bool propagate_atom(atom const& a);

        th_var mk_term(app* n);

        th_var mk_num(app* n, rational const& r);

        bool is_consistent() const;

        th_var expand(bool pos, th_var v, rational & k);

        void new_eq_or_diseq(bool is_eq, th_var v1, th_var v2, justification& eq_just);
        
        th_var get_zero(sort* s) const { return a.is_int(s)?m_zero_int:m_zero_real; }

        th_var get_zero(expr* e) const { return get_zero(get_manager().get_sort(e)); }

        void inc_conflicts();

    };

    struct rhi_ext {
        typedef inf_rational inf_numeral;
        typedef inf_eps_rational<inf_rational> numeral;
        numeral     m_epsilon;
        numeral     m_minus_infty;
        rhi_ext() : m_epsilon(inf_rational(rational(), true)), m_minus_infty(rational(-1),inf_rational()) {}
    };

    struct ihi_ext {
        typedef rational inf_numeral;
        typedef inf_eps_rational<rational> numeral;
        numeral     m_epsilon;
        numeral     m_minus_infty;
        ihi_ext() : m_epsilon(rational(1)), m_minus_infty(rational(-1),rational(0)) {}
    };

    typedef theory_horn_ineq<rhi_ext>  theory_rhi;
    typedef theory_horn_ineq<ihi_ext>  theory_ihi;
};




#endif /* _THEORY_HORN_INEQ_H_ */
