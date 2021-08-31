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
#pragma once

#include "smt/smt_theory.h"
#include "util/trail.h"
#include "ast/fpa/fpa2bv_converter.h"
#include "ast/fpa/fpa2bv_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/fpa_factory.h"
#include "smt/smt_model_generator.h"

namespace smt {

    class theory_fpa : public theory {
    protected:


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

            app * mk_value(model_generator & mg, expr_ref_vector const & values) override;
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
            app * mk_value(model_generator & mg, expr_ref_vector const & values) override;
        };

    protected:
        th_rewriter               m_th_rw;
        fpa2bv_converter_wrapped  m_converter;
        fpa2bv_rewriter           m_rw;
        trail_stack               m_trail_stack;
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
        theory_fpa(context& ctx);
        ~theory_fpa() override;

        void display(std::ostream & out) const override;

    protected:
        expr_ref mk_side_conditions();
        expr_ref convert(expr * e);

        void attach_new_th_var(enode * n);
        void assert_cnstr(expr * e);


        enode* ensure_enode(expr* e);
        enode* get_root(expr* a) { return ensure_enode(a)->get_root(); }
        app* get_ite_value(expr* e);
    };

};

