/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_solver_old.cpp

Abstract:
    OLD API for using solvers.

    This has been deprecated

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_model.h"
#include"cancel_eh.h"

extern "C" {

    void Z3_API Z3_push(Z3_context c) {
        Z3_TRY;
        LOG_Z3_push(c);
        RESET_ERROR_CODE();
        CHECK_SEARCHING(c);
        mk_c(c)->push();
        Z3_CATCH;
    }
        
    void Z3_API Z3_pop(Z3_context c, unsigned num_scopes) {
        Z3_TRY;
        LOG_Z3_pop(c, num_scopes);
        RESET_ERROR_CODE();
        CHECK_SEARCHING(c);
        if (num_scopes > mk_c(c)->get_num_scopes()) {
            SET_ERROR_CODE(Z3_IOB);
            return;
        }
        if (num_scopes > 0) {
            mk_c(c)->pop(num_scopes);
        }
        Z3_CATCH;
    }

    unsigned Z3_API Z3_get_num_scopes(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_num_scopes(c);
        RESET_ERROR_CODE();
        return mk_c(c)->get_num_scopes();
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_assert_cnstr(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_assert_cnstr(c, a);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        mk_c(c)->assert_cnstr(to_expr(a));
        Z3_CATCH;
    }

    Z3_lbool Z3_API Z3_check_and_get_model(Z3_context c, Z3_model * m) {
        Z3_TRY;
        LOG_Z3_check_and_get_model(c, m);
        RESET_ERROR_CODE();
        CHECK_SEARCHING(c);
        cancel_eh<smt::kernel> eh(mk_c(c)->get_smt_kernel());
        api::context::set_interruptable si(*(mk_c(c)), eh);
        flet<bool> _model(mk_c(c)->fparams().m_model, true);
        lbool result;
        try {
            model_ref _m;
            result = mk_c(c)->check(_m);
            if (m) {
                if (_m) {
                    Z3_model_ref * m_ref = alloc(Z3_model_ref); 
                    m_ref->m_model = _m;
                    // Must bump reference counter for backward compatibility reasons.
                    // Don't need to invoke save_object, since the counter was bumped
                    m_ref->inc_ref(); 
                    *m = of_model(m_ref);
                }
                else {
                    *m = 0;
                }
            }
        }
        catch (z3_exception & ex) {
            mk_c(c)->handle_exception(ex);
            RETURN_Z3_check_and_get_model static_cast<Z3_lbool>(l_undef);
        }
        RETURN_Z3_check_and_get_model static_cast<Z3_lbool>(result);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }
    
    Z3_lbool Z3_API Z3_check(Z3_context c) {
        Z3_TRY;
        // This is just syntax sugar... 
        RESET_ERROR_CODE();   
        CHECK_SEARCHING(c);
        Z3_lbool r = Z3_check_and_get_model(c, 0);
        return r;
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    
    Z3_lbool Z3_API Z3_check_assumptions(Z3_context c, 
                                         unsigned num_assumptions, Z3_ast const assumptions[], 
                                         Z3_model * m, Z3_ast* proof, 
                                         unsigned* core_size, Z3_ast core[]) {
        Z3_TRY;
        LOG_Z3_check_assumptions(c, num_assumptions, assumptions, m, proof, core_size, core);
        RESET_ERROR_CODE();
        CHECK_SEARCHING(c);
        expr * const* _assumptions = to_exprs(assumptions);
        flet<bool> _model(mk_c(c)->fparams().m_model, true);
        cancel_eh<smt::kernel> eh(mk_c(c)->get_smt_kernel());
        api::context::set_interruptable si(*(mk_c(c)), eh);
        lbool result;
        result = mk_c(c)->get_smt_kernel().check(num_assumptions, _assumptions);
        if (result != l_false && m) {
            model_ref _m;
            mk_c(c)->get_smt_kernel().get_model(_m);
            if (_m) {
                Z3_model_ref * m_ref = alloc(Z3_model_ref); 
                m_ref->m_model = _m;
                // Must bump reference counter for backward compatibility reasons.
                // Don't need to invoke save_object, since the counter was bumped
                m_ref->inc_ref(); 
                *m = of_model(m_ref);
            }
            else {
                *m = 0;
            }
        }
        if (result == l_false && core_size) {
            *core_size = mk_c(c)->get_smt_kernel().get_unsat_core_size();
            if (*core_size > num_assumptions) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
            }
            for (unsigned i = 0; i < *core_size; ++i) {
                core[i] = of_ast(mk_c(c)->get_smt_kernel().get_unsat_core_expr(i));
            }
        }
        else if (core_size) {
            *core_size = 0;
        }
        if (result == l_false && proof) {
            *proof = of_ast(mk_c(c)->get_smt_kernel().get_proof());
        }
        else if (proof) {
            *proof = 0; // breaks abstraction.
        }
        RETURN_Z3_check_assumptions static_cast<Z3_lbool>(result);         
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_search_failure Z3_API Z3_get_search_failure(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_search_failure(c);
        RESET_ERROR_CODE();
        CHECK_SEARCHING(c);
        smt::failure f = mk_c(c)->get_smt_kernel().last_failure();
        return api::mk_Z3_search_failure(f);
        Z3_CATCH_RETURN(Z3_UNKNOWN);
    }

    class labeled_literal {
        expr_ref m_literal;
        symbol   m_label;
        bool     m_enabled;
    public:
        labeled_literal(ast_manager& m, expr* l, symbol const& n) : m_literal(l,m), m_label(n), m_enabled(true) {}
        labeled_literal(ast_manager& m, expr* l) : m_literal(l,m), m_label(), m_enabled(true) {}
        bool is_enabled() const { return m_enabled; }
        void disable() { m_enabled = false; }
        symbol const& get_label() const { return m_label; }
        expr* get_literal() { return m_literal.get(); }
    };
    
    typedef vector<labeled_literal> labels;

    Z3_literals Z3_API Z3_get_relevant_labels(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_relevant_labels(c);
        RESET_ERROR_CODE();
        buffer<symbol> labl_syms;
        ast_manager& m = mk_c(c)->m();
        expr_ref_vector lits(m);
        mk_c(c)->get_smt_kernel().get_relevant_labels(0, labl_syms);
        mk_c(c)->get_smt_kernel().get_relevant_labeled_literals(mk_c(c)->fparams().m_at_labels_cex, lits);        
        labels* lbls = alloc(labels);
        SASSERT(labl_syms.size() == lits.size());
        for (unsigned i = 0; i < lits.size(); ++i) {
            lbls->push_back(labeled_literal(m,lits[i].get(), labl_syms[i]));
        }
        RETURN_Z3(reinterpret_cast<Z3_literals>(lbls));
        Z3_CATCH_RETURN(0);
    }

    Z3_literals Z3_API Z3_get_relevant_literals(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_relevant_literals(c);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        expr_ref_vector lits(m);
        mk_c(c)->get_smt_kernel().get_relevant_literals(lits);        
        labels* lbls = alloc(labels);
        for (unsigned i = 0; i < lits.size(); ++i) {
            lbls->push_back(labeled_literal(m,lits[i].get()));
        }
        RETURN_Z3(reinterpret_cast<Z3_literals>(lbls));        
        Z3_CATCH_RETURN(0);
    }

    Z3_literals Z3_API Z3_get_guessed_literals(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_guessed_literals(c);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        expr_ref_vector lits(m);
        mk_c(c)->get_smt_kernel().get_guessed_literals(lits);        
        labels* lbls = alloc(labels);
        for (unsigned i = 0; i < lits.size(); ++i) {
            lbls->push_back(labeled_literal(m,lits[i].get()));
        }
        RETURN_Z3(reinterpret_cast<Z3_literals>(lbls));        
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_del_literals(Z3_context c, Z3_literals lbls) {
        Z3_TRY;
        LOG_Z3_del_literals(c, lbls);
        RESET_ERROR_CODE();
        dealloc(reinterpret_cast<labels*>(lbls));
        Z3_CATCH;
    }

    unsigned Z3_API Z3_get_num_literals(Z3_context c,Z3_literals lbls) {
        Z3_TRY;
        LOG_Z3_get_num_literals(c, lbls);
        RESET_ERROR_CODE();
        return reinterpret_cast<labels*>(lbls)->size();   
        Z3_CATCH_RETURN(0);
    }

    Z3_symbol Z3_API Z3_get_label_symbol(Z3_context c,Z3_literals lbls, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_label_symbol(c, lbls, idx);
        RESET_ERROR_CODE();
        return of_symbol((*reinterpret_cast<labels*>(lbls))[idx].get_label());        
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_literal(Z3_context c,Z3_literals lbls, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_literal(c, lbls, idx);
        RESET_ERROR_CODE();
        expr* e = (*reinterpret_cast<labels*>(lbls))[idx].get_literal();
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_ast(e));
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_disable_literal(Z3_context c, Z3_literals lbls, unsigned idx) {
        Z3_TRY;
        LOG_Z3_disable_literal(c, lbls, idx);
        RESET_ERROR_CODE();
        (*reinterpret_cast<labels*>(lbls))[idx].disable(); 
        Z3_CATCH;
    }

    void Z3_API Z3_block_literals(Z3_context c, Z3_literals lbls) {
        Z3_TRY;
        LOG_Z3_block_literals(c, lbls);
        RESET_ERROR_CODE();
        labels* _lbls = reinterpret_cast<labels*>(lbls);
        ast_manager& m = mk_c(c)->m();
        expr_ref_vector lits(m);
        for (unsigned i = 0; i < _lbls->size(); ++i) {
            if ((*_lbls)[i].is_enabled()) {
                lits.push_back(m.mk_not((*_lbls)[i].get_literal()));
            }
        }
        expr_ref clause(m);
        clause = m.mk_or(lits.size(), lits.c_ptr());
        mk_c(c)->save_ast_trail(clause.get());
        mk_c(c)->assert_cnstr(clause.get());
        Z3_CATCH;
    }

    Z3_API char const * Z3_context_to_string(Z3_context c) {
        Z3_TRY;
        LOG_Z3_context_to_string(c);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        mk_c(c)->get_smt_kernel().display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_context_assignment(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_context_assignment(c);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        expr_ref result(m);
        expr_ref_vector assignment(m);
        mk_c(c)->get_smt_kernel().get_assignments(assignment);
        result = mk_c(c)->mk_and(assignment.size(), assignment.c_ptr());
        RETURN_Z3(of_ast(result.get()));
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_statistics_to_string(Z3_context c) {
        Z3_TRY;
        LOG_Z3_statistics_to_string(c);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        mk_c(c)->get_smt_kernel().display_statistics(buffer);
        memory::display_max_usage(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_soft_check_cancel(Z3_context c) {
        Z3_TRY;
        LOG_Z3_soft_check_cancel(c);
        RESET_ERROR_CODE();
        mk_c(c)->interrupt();
        Z3_CATCH;
    }

};

void Z3_display_statistics(Z3_context c, std::ostream& s) {
    mk_c(c)->get_smt_kernel().display_statistics(s);
}

void Z3_display_istatistics(Z3_context c, std::ostream& s) {
    mk_c(c)->get_smt_kernel().display_istatistics(s);
}
    
