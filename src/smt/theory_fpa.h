/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_fpa.h

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/
#ifndef THEORY_FPA_H_
#define THEORY_FPA_H_

#include "smt/smt_theory.h"
#include "util/trail.h"
#include "ast/fpa/fpa2bv_converter.h"
#include "ast/fpa/fpa2bv_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/proto_model/value_factory.h"
#include "smt/smt_model_generator.h"

namespace smt {

    class fpa_value_factory : public value_factory {
        fpa_util          m_util;

        virtual app * mk_value_core(mpf const & val, sort * s) {
            SASSERT(m_util.get_ebits(s) == val.get_ebits());
            SASSERT(m_util.get_sbits(s) == val.get_sbits());
            return m_util.mk_value(val);
        }

    public:
        fpa_value_factory(ast_manager & m, family_id fid) :
            value_factory(m, fid),
            m_util(m) {}

        ~fpa_value_factory() override {}

        expr * get_some_value(sort * s) override {
            mpf_manager & mpfm = m_util.fm();
            scoped_mpf q(mpfm);
            mpfm.set(q, m_util.get_ebits(s), m_util.get_sbits(s), 0);
            return m_util.mk_value(q);
        }

        bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
            mpf_manager & mpfm = m_util.fm();
            scoped_mpf q(mpfm);
            mpfm.set(q, m_util.get_ebits(s), m_util.get_sbits(s), 0);
            v1 = m_util.mk_value(q);
            mpfm.set(q, m_util.get_ebits(s), m_util.get_sbits(s), 1);
            v2 = m_util.mk_value(q);
            return true;
        }

        expr * get_fresh_value(sort * s) override { NOT_IMPLEMENTED_YET(); }
        void register_value(expr * n) override { /* Ignore */ }

        app * mk_value(mpf const & x) {
            return m_util.mk_value(x);
        }
    };

    class theory_fpa : public theory {
    protected:
        typedef trail_stack<theory_fpa> th_trail_stack;

        class fpa2bv_converter_wrapped : public fpa2bv_converter {
        public:
            theory_fpa & m_th;
            fpa2bv_converter_wrapped(ast_manager & m, theory_fpa * th) :
                fpa2bv_converter(m),
                m_th(*th) {}
            virtual ~fpa2bv_converter_wrapped() {}
            void mk_const(func_decl * f, expr_ref & result) override;
            void mk_rm_const(func_decl * f, expr_ref & result) override;
        };

        class fpa_value_proc : public model_value_proc {
        protected:
            theory_fpa  & m_th;
            ast_manager & m;
            fpa_util    & m_fu;
            bv_util     & m_bu;
            buffer<model_value_dependency> m_deps;
            unsigned m_ebits;
            unsigned m_sbits;

        public:
            fpa_value_proc(theory_fpa * th, unsigned ebits, unsigned sbits) :
                m_th(*th), m(th->get_manager()), m_fu(th->m_fpa_util), m_bu(th->m_bv_util),
                m_ebits(ebits), m_sbits(sbits) {}

            ~fpa_value_proc() override {}

            void add_dependency(enode * e) { m_deps.push_back(model_value_dependency(e)); }

            void get_dependencies(buffer<model_value_dependency> & result) override {
                result.append(m_deps);
            }

            app * mk_value(model_generator & mg, ptr_vector<expr> & values) override;
        };

        class fpa_rm_value_proc : public model_value_proc {
            theory_fpa  & m_th;
            ast_manager & m;
            fpa_util    & m_fu;
            bv_util     & m_bu;
            buffer<model_value_dependency> m_deps;

        public:
            fpa_rm_value_proc(theory_fpa * th) :
                m_th(*th), m(th->get_manager()), m_fu(th->m_fpa_util), m_bu(th->m_bv_util) { (void) m_th; }

            void add_dependency(enode * e) { m_deps.push_back(model_value_dependency(e)); }

            void get_dependencies(buffer<model_value_dependency> & result) override {
                result.append(m_deps);
            }

            ~fpa_rm_value_proc() override {}
            app * mk_value(model_generator & mg, ptr_vector<expr> & values) override;
        };

    protected:
        fpa2bv_converter_wrapped  m_converter;
        fpa2bv_rewriter           m_rw;
        th_rewriter               m_th_rw;
        th_trail_stack            m_trail_stack;
        fpa_value_factory *       m_factory;
        fpa_util                & m_fpa_util;
        bv_util                 & m_bv_util;
        arith_util              & m_arith_util;
        obj_map<expr, expr*>      m_conversions;
        bool                      m_is_initialized;
        obj_hashtable<func_decl>  m_is_added_to_model;

        final_check_status final_check_eh() override;
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void apply_sort_cnstr(enode * n, sort * s) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        theory* mk_fresh(context* new_ctx) override;
        char const * get_name() const override { return "fpa"; }

        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        void assign_eh(bool_var v, bool is_true) override;
        void relevant_eh(app * n) override;
        void init_model(model_generator & m) override;
        void finalize_model(model_generator & mg) override;

    public:
        theory_fpa(ast_manager & m);
        ~theory_fpa() override;

        void init(context * ctx) override;

        void display(std::ostream & out) const override;

    protected:
        expr_ref mk_side_conditions();
        expr_ref convert(expr * e);
        expr_ref convert_atom(expr * e);
        expr_ref convert_term(expr * e);
        expr_ref convert_conversion_term(expr * e);

        void attach_new_th_var(enode * n);
        void assert_cnstr(expr * e);

        app_ref wrap(expr * e);
        app_ref unwrap(expr * e, sort * s);
    };

};

#endif /* THEORY_FPA_H_ */
