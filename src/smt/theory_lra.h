/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    theory_lra.h

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach) 2016-25-3
    Nikolaj Bjorner (nbjorner)

Revision History:


--*/
#pragma once

#include "smt/theory_opt.h"

namespace smt {
    class theory_lra : public theory, public theory_opt {
        class imp;
        imp* m_imp;

    public:
        theory_lra(ast_manager& m, theory_arith_params& ap);
        ~theory_lra() override;
        theory* mk_fresh(context* new_ctx) override;
        char const* get_name() const override { return "arithmetic"; }
        
        void init(context * ctx) override;

        bool internalize_atom(app * atom, bool gate_ctx) override;
                                                     
        bool internalize_term(app * term) override;

        void internalize_eq_eh(app * atom, bool_var v) override;

        void assign_eh(bool_var v, bool is_true) override;

        lbool get_phase(bool_var v) override;

        void new_eq_eh(theory_var v1, theory_var v2) override;

        bool use_diseqs() const override;

        void new_diseq_eh(theory_var v1, theory_var v2) override;

        void push_scope_eh() override;

        void pop_scope_eh(unsigned num_scopes) override;

        void restart_eh() override;

        void relevant_eh(app* e) override;

        void init_search_eh() override;

        final_check_status final_check_eh() override;

        bool is_shared(theory_var v) const override;
    
        bool can_propagate() override;
        
        void propagate() override;
        
        justification * why_is_diseq(theory_var v1, theory_var v2) override;

        // virtual void flush_eh();

        void reset_eh() override;

        void apply_sort_cnstr(enode * n, sort * s) override;

        void init_model(model_generator & m) override;
        
        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        bool get_value(enode* n, expr_ref& r) override;
        bool include_func_interp(func_decl* f) override;
        bool get_value(enode* n, rational& r);
        bool get_lower(enode* n, expr_ref& r);
        bool get_upper(enode* n, expr_ref& r);
        bool get_lower(enode* n, rational& r, bool& is_strict);
        bool get_upper(enode* n, rational& r, bool& is_strict);
                
        void display(std::ostream & out) const override;
        
        void collect_statistics(::statistics & st) const override;

        // optimization
        expr_ref mk_ge(generic_model_converter& fm, theory_var v, inf_rational const& val);
        inf_eps value(theory_var) override;
        inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared) override;
        theory_var add_objective(app* term) override;
    };

}
