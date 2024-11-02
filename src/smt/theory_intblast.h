/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    theory_intblast
    
Abstract:

    Intblast version of bit-vector solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-24

--*/
#pragma once


#include "util/rlimit.h"
#include "ast/sls/sat_ddfw.h"
#include "smt/smt_theory.h"
#include "model/model.h"
#include "model/numeral_factory.h"
#include "ast/rewriter/bv2int_translator.h"


namespace smt {

    class theory_intblast : public theory {

        class translator_trail : public bv2int_translator_trail {
            context& ctx;
        public:
            translator_trail(context&  ctx):ctx(ctx) {}
            void push(push_back_vector<expr_ref_vector> const& c) override;
            void push(push_back_vector<ptr_vector<app>> const& c) override; 
            void push_idx(set_vector_idx_trail<expr_ref_vector> const& c) override; 
        };

        translator_trail m_trail;
        bv2int_translator m_translator;
        bv_util           bv;
        arith_util        a;
        unsigned m_vars_qhead = 0, m_preds_qhead = 0;
        bv_factory *    m_factory = nullptr;

        bool add_bound_axioms();
        bool add_predicate_axioms();

    public:
        theory_intblast(context& ctx);
        ~theory_intblast() override;

        char const* get_name() const override { return "bv-intblast"; }
        smt::theory* mk_fresh(context* new_ctx) override { return alloc(theory_intblast, *new_ctx); }
        final_check_status final_check_eh() override;
        void display(std::ostream& out) const override {}
        bool can_propagate() override;
        void propagate() override;
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void internalize_eq_eh(app * atom, bool_var v) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void init_model(model_generator& m) override;
        model_value_proc* mk_value(enode* n, model_generator& m) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}

    };

}

