/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    recfun_solver.h

Abstract:

    Recursive function solver plugin

Author:

    Simon Cruanes December 2017
    Nikolaj Bjorner (nbjorner) 2021-02-09

--*/
#pragma once

#include "ast/recfun_decl_plugin.h"
#include "ast/ast_trail.h"
#include "sat/smt/sat_th.h"


namespace euf {
    class solver;
}

namespace recfun {

    class solver : public euf::th_euf_solver {

        struct stats {
            unsigned m_case_expansions, m_body_expansions, m_macro_expansions;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };

        // one case-expansion of `f(t1...tn)`
        struct case_expansion {
            app *              m_lhs; // the term to expand
            recfun::def *       m_def;
            ptr_vector<expr>    m_args;
            case_expansion(recfun::util& u, app * n) : 
            m_lhs(n), m_def(nullptr), m_args()  {
                SASSERT(u.is_defined(n));
                func_decl * d = n->get_decl();
                m_def = &u.get_def(d);
                m_args.append(n->get_num_args(), n->get_args());
            }
            case_expansion(case_expansion const & from)
                : m_lhs(from.m_lhs),
                  m_def(from.m_def),
                  m_args(from.m_args) {}
            case_expansion(case_expansion && from)
                : m_lhs(from.m_lhs),
                  m_def(from.m_def),
                  m_args(std::move(from.m_args)) {}
        };

        struct pp_case_expansion {
            case_expansion & e;
            ast_manager & m;
            pp_case_expansion(case_expansion & e, ast_manager & m) : e(e), m(m) {}
        };

        friend std::ostream& operator<<(std::ostream&, pp_case_expansion const &);

        // one body-expansion of `f(t1...tn)` using a `C_f_i(t1...tn)`
        struct body_expansion {
            app*                     m_pred;
            recfun::case_def const * m_cdef;
            ptr_vector<expr>         m_args;

            body_expansion(recfun::util& u, app * n) : m_pred(n), m_cdef(nullptr), m_args() {
                m_cdef = &u.get_case_def(n);
                m_args.append(n->get_num_args(), n->get_args());
            }
            body_expansion(app* pred, recfun::case_def const & d, ptr_vector<expr> & args) : 
                m_pred(pred), m_cdef(&d), m_args(args) {}
            body_expansion(body_expansion const & from): 
                m_pred(from.m_pred), m_cdef(from.m_cdef), m_args(from.m_args) {}
            body_expansion(body_expansion && from) : 
                m_pred(from.m_pred), m_cdef(from.m_cdef), m_args(std::move(from.m_args)) {}
        };

        struct pp_body_expansion {
            body_expansion & e;
            ast_manager & m;
            pp_body_expansion(body_expansion & e, ast_manager & m) : e(e), m(m) {}
        };

        friend std::ostream& operator<<(std::ostream&, pp_body_expansion const &);
        
        recfun::decl::plugin&   m_plugin;
        recfun::util&           m_util;
        stats                   m_stats;

        // book-keeping for depth of predicates
        expr_ref_vector          m_disabled_guards;
        expr_ref_vector          m_enabled_guards;
        obj_map<expr, expr_ref_vector*> m_guard2pending;
        obj_map<expr, unsigned>  m_pred_depth;
        expr_ref_vector          m_preds;
        unsigned_vector          m_preds_lim;
        unsigned                 m_num_rounds;

        ptr_vector<case_expansion>  m_q_case_expand;
        ptr_vector<body_expansion>  m_q_body_expand;
        vector<sat::literal_vector> m_q_clauses;
        ptr_vector<expr>            m_q_guards;

        bool is_enabled_guard(expr* guard) { expr_ref ng(m.mk_not(guard), m); return m_enabled_guards.contains(ng); }
        bool is_disabled_guard(expr* guard) { return m_disabled_guards.contains(guard); }

        recfun::util & u() const { return m_util; }
        bool is_defined(expr * f) const { return u().is_defined(f); }
        bool is_case_pred(expr * f) const { return u().is_case_pred(f); }

        bool is_defined(euf::enode * e) const { return is_defined(e->get_expr()); }
        bool is_case_pred(euf::enode * e) const { return is_case_pred(e->get_expr()); }

        void activate_guard(expr* guard, expr_ref_vector const& guards);

        void reset_queues();
        expr_ref apply_args(unsigned depth, recfun::vars const & vars, ptr_vector<expr> const & args, expr * e); //!< substitute variables by args
        void assert_macro_axiom(case_expansion & e);
        void assert_case_axioms(case_expansion & e);
        void assert_body_axiom(body_expansion & e);
        sat::literal mk_literal(expr* e);

        void add_induction_lemmas(unsigned depth);
        void disable_guard(expr* guard, expr_ref_vector const& guards);
        unsigned get_depth(expr* e);
        void set_depth(unsigned d, expr* e);
        void set_depth_rec(unsigned d, expr* e);
        
        sat::literal mk_eq_lit(expr* l, expr* r);
        bool is_standard_order(recfun::vars const& vars) const { 
            return vars.empty() || vars[vars.size()-1]->get_idx() == 0;
        }

        void reset();

    public:

        solver(euf::solver& ctx);
        ~solver() override;
        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override;
        void asserted(sat::literal l) override;
        sat::check_result check() override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return display_constraint(out, idx); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override { UNREACHABLE(); }
        euf::theory_var mk_var(euf::enode* n) override;
        void init_search() override;
        void finalize_model(model& mdl) override;
        bool is_shared(euf::theory_var v) const override { return true; }
    };
}
