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
#ifndef _THEORY_FPA_H_
#define _THEORY_FPA_H_

#include"smt_theory.h"
#include"fpa2bv_converter.h"
#include"fpa2bv_rewriter.h"

namespace smt {
    class theory_fpa : public theory {
        typedef trail_stack<theory_fpa> th_trail_stack;
        
        fpa2bv_converter m_converter;
        fpa2bv_rewriter  m_rw;
        expr_map         m_trans_map;        
        th_trail_stack   m_trail_stack;

        virtual final_check_status final_check_eh() { return FC_DONE; }
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual void apply_sort_cnstr(enode * n, sort * s);
        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual theory* mk_fresh(context*) { return alloc(theory_fpa, get_manager()); }
        virtual char const * get_name() const { return "fpa"; }        

        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        
        void assign_eh(bool_var v, bool is_true);
        virtual void relevant_eh(app * n);
    public:
        theory_fpa(ast_manager& m);
        virtual ~theory_fpa();

    protected:
        void split_triple(expr * e, expr * & sgn, expr * & sig, expr * & exp) const {
            SASSERT(is_app_of(e, get_family_id(), OP_TO_FLOAT));
            SASSERT(to_app(e)->get_num_args() == 3);
            sgn = to_app(e)->get_arg(0);
            sig = to_app(e)->get_arg(1);
            exp = to_app(e)->get_arg(2);
        }
        
        void ensure_bv_var(expr_ref const & n);
    };

};

#endif /* _THEORY_FPA_H_ */

