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
            app*                    m_pred;
            recfun::case_def const * m_cdef;
            ptr_vector<expr>        m_args;

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
        
        ast_manager&            m;
        recfun::decl::plugin&   m_plugin;
        recfun::util&           m_util;
        stats                   m_stats;

        // book-keeping for depth of predicates
        obj_map<expr, unsigned>  m_pred_depth;
        expr_ref_vector          m_preds;
        unsigned_vector          m_preds_lim;
        unsigned                 m_max_depth; // for fairness and termination

        ptr_vector<case_expansion> m_q_case_expand;
        ptr_vector<body_expansion> m_q_body_expand;
        vector<literal_vector> m_q_clauses;

        recfun::util & u() const { return m_util; }
        bool is_defined(app * f) const { return u().is_defined(f); }
        bool is_case_pred(app * f) const { return u().is_case_pred(f); }

        bool is_defined(enode * e) const { return is_defined(e->get_owner()); }
        bool is_case_pred(enode * e) const { return is_case_pred(e->get_owner()); }

        void reset_queues();
        expr_ref apply_args(unsigned depth, recfun::vars const & vars, ptr_vector<expr> const & args, expr * e); //!< substitute variables by args
        void assert_macro_axiom(case_expansion & e);
        void assert_case_axioms(case_expansion & e);
        void assert_body_axiom(body_expansion & e);
        literal mk_literal(expr* e);

        void assert_max_depth_limit(expr* guard);
        unsigned get_depth(expr* e);
        void set_depth(unsigned d, expr* e);
        void set_depth_rec(unsigned d, expr* e);
        
        literal mk_eq_lit(expr* l, expr* r);
        bool is_standard_order(recfun::vars const& vars) const { 
            return vars.empty() || vars[vars.size()-1]->get_idx() == 0;
        }
    protected:
        void push_case_expand(case_expansion* e) { m_q_case_expand.push_back(e); }
        void push_body_expand(body_expansion* e) { m_q_body_expand.push_back(e); }

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
        bool should_research(expr_ref_vector &) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void add_theory_assumptions(expr_ref_vector & assumptions) override;
        void init(context* ctx) override;

    public:
        theory_recfun(ast_manager & m);
        ~theory_recfun() override;
        theory * mk_fresh(context * new_ctx) override;
        void init_search_eh() override;
        void display(std::ostream & out) const override;
        void collect_statistics(::statistics & st) const override;
    };
}

#endif
