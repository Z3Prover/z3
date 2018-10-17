/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    theory_recfun.h

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Simon Cuares December 2017

Revision History:

--*/
#ifndef THEORY_RECFUN_H_
#define THEORY_RECFUN_H_

#include "smt/smt_theory.h"
#include "smt/smt_context.h"
#include "ast/ast_pp.h"
#include "ast/recfun_decl_plugin.h"

namespace smt {

    class theory_recfun : public theory {
        struct stats {
            unsigned m_case_expansions, m_body_expansions, m_macro_expansions;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };

        // one case-expansion of `f(t1…tn)`
        struct case_expansion {
            expr *              m_lhs; // the term to expand
            recfun_def *        m_def;
            ptr_vector<expr>    m_args;
            case_expansion(recfun_util& u, app * n) : m_lhs(n), m_def(0), m_args()
            {
                SASSERT(u.is_defined(n));
                func_decl * d = n->get_decl();
                const symbol& name = d->get_name();
                m_def = &u.get_def(name);
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

        // one body-expansion of `f(t1…tn)` using a `C_f_i(t1…tn)`
        struct body_expansion {
            recfun_case_def const * m_cdef;
            ptr_vector<expr>        m_args;

            body_expansion(recfun_util& u, app * n) : m_cdef(0), m_args() {
                SASSERT(u.is_case_pred(n));
                func_decl * d = n->get_decl();
                const symbol& name = d->get_name();
                m_cdef = &u.get_case_def(name);
                for (unsigned i = 0; i < n->get_num_args(); ++i)
                    m_args.push_back(n->get_arg(i));
            }
            body_expansion(recfun_case_def const & d, ptr_vector<expr> & args) : m_cdef(&d), m_args(args) {}
            body_expansion(body_expansion const & from): m_cdef(from.m_cdef), m_args(from.m_args) {}
            body_expansion(body_expansion && from) : m_cdef(from.m_cdef), m_args(std::move(from.m_args)) {}
        };

        struct pp_body_expansion {
            body_expansion & e;
            ast_manager & m;
            pp_body_expansion(body_expansion & e, ast_manager & m) : e(e), m(m) {}
        };

        friend std::ostream& operator<<(std::ostream&, pp_body_expansion const &);
        
        struct empty{};

        typedef trail_stack<theory_recfun>  th_trail_stack;
        typedef obj_map<expr, empty> guard_set;

        recfun_decl_plugin& m_plugin;
        recfun_util&        m_util;
        stats               m_stats;
        th_trail_stack      m_trail;
        guard_set           m_guards; // true case-preds
        unsigned            m_max_depth; // for fairness and termination

        vector<case_expansion>      m_q_case_expand;
        vector<body_expansion>      m_q_body_expand;
        vector<literal_vector>      m_q_clauses;

        recfun_util & u() const { return m_util; }
        ast_manager & m() { return get_manager(); }
        bool is_defined(app * f) const { return u().is_defined(f); }
        bool is_case_pred(app * f) const { return u().is_case_pred(f); }

        bool is_defined(enode * e) const { return is_defined(e->get_owner()); }
        bool is_case_pred(enode * e) const { return is_case_pred(e->get_owner()); }

        void reset_queues();
        expr_ref apply_args(recfun::vars const & vars, ptr_vector<expr> const & args, expr * e); //!< substitute variables by args
        app_ref apply_pred(recfun::case_pred const & p, ptr_vector<expr> const & args); //<! apply predicate to args
        void assert_macro_axiom(case_expansion & e);
        void assert_case_axioms(case_expansion & e);
        void assert_body_axiom(body_expansion & e);
        void max_depth_conflict(void);
        literal mk_literal(expr* e);
        literal mk_eq_lit(expr* l, expr* r);
    protected:
        void push_case_expand(case_expansion&& e) { m_q_case_expand.push_back(e); }
        void push_body_expand(body_expansion&& e) { m_q_body_expand.push_back(e); }

        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void reset_eh() override;
        void relevant_eh(app * n) override;
        char const * get_name() const override;
        final_check_status final_check_eh() override;
        void assign_eh(bool_var v, bool is_true) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        bool can_propagate() override;
        void propagate() override;
        lbool validate_unsat_core(expr_ref_vector &) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void add_theory_assumptions(expr_ref_vector & assumptions) override;

    public:
        theory_recfun(ast_manager & m);
        virtual ~theory_recfun() override;
        void setup_params(); // read parameters
        virtual theory * mk_fresh(context * new_ctx) override;
        virtual void display(std::ostream & out) const override;
        virtual void collect_statistics(::statistics & st) const override;
        unsigned get_max_depth() const { return m_max_depth; }
        void set_max_depth(unsigned n) { SASSERT(n>0); m_max_depth = n; }
    };
}

#endif
