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

#include "theory_opt.h"

namespace smt {
    class theory_lra : public theory, public theory_opt {
        class imp;
        imp* m_imp;

    public:
        theory_lra(ast_manager& m, theory_arith_params& ap);
        virtual ~theory_lra();
        virtual theory* mk_fresh(context* new_ctx);
        virtual char const* get_name() const { return "lra"; }
        
        virtual void init(context * ctx);

        virtual bool internalize_atom(app * atom, bool gate_ctx);
                                                     
        virtual bool internalize_term(app * term);

        virtual void internalize_eq_eh(app * atom, bool_var v);

        virtual void assign_eh(bool_var v, bool is_true);

        virtual void new_eq_eh(theory_var v1, theory_var v2);

        virtual bool use_diseqs() const;

        virtual void new_diseq_eh(theory_var v1, theory_var v2);

        virtual void push_scope_eh();

        virtual void pop_scope_eh(unsigned num_scopes);

        virtual void restart_eh();

        virtual void relevant_eh(app* e);

        virtual void init_search_eh();

        virtual final_check_status final_check_eh();

        virtual bool is_shared(theory_var v) const;
    
        virtual bool can_propagate();
        
        virtual void propagate();
        
        virtual justification * why_is_diseq(theory_var v1, theory_var v2);

        // virtual void flush_eh();

        virtual void reset_eh();

        virtual void init_model(model_generator & m);
        
        virtual model_value_proc * mk_value(enode * n, model_generator & mg);

        virtual bool get_value(enode* n, expr_ref& r);

        virtual bool validate_eq_in_model(theory_var v1, theory_var v2, bool is_true) const;
                
        virtual void display(std::ostream & out) const;
        
        virtual void collect_statistics(::statistics & st) const;

        // optimization
        virtual inf_eps value(theory_var);
        virtual inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared); 
        virtual theory_var add_objective(app* term);
        virtual expr_ref mk_ge(filter_model_converter& fm, theory_var v, inf_rational const& val);


    };

}
