/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    api_datalog_spacer.inc

Abstract:

    Spacer-specific datalog API

Author:

    Arie Gurfinkel (arie) 

Notes:
  this file is included at the bottom of api_datalog.cpp

--*/
    Z3_lbool Z3_API Z3_fixedpoint_query_from_lvl (Z3_context c, Z3_fixedpoint d, Z3_ast q, unsigned lvl) {
        Z3_TRY;
        LOG_Z3_fixedpoint_query_from_lvl (c, d, q, lvl);
        RESET_ERROR_CODE();
        lbool r = l_undef;
        unsigned timeout = to_fixedpoint(d)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit  = to_fixedpoint(d)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        {
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            cancel_eh<reslimit> eh(mk_c(c)->m().limit());
            api::context::set_interruptable si(*(mk_c(c)), eh);        
            scoped_timer timer(timeout, &eh);
            try {
                r = to_fixedpoint_ref(d)->ctx().query_from_lvl (to_expr(q), lvl);
            }
            catch (z3_exception& ex) {
                mk_c(c)->handle_exception(ex);
                r = l_undef;
            }
            to_fixedpoint_ref(d)->ctx().cleanup();
        }
        return of_lbool(r);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_ast Z3_API Z3_fixedpoint_get_ground_sat_answer(Z3_context c, Z3_fixedpoint d) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_ground_sat_answer(c, d);
        RESET_ERROR_CODE();
        expr* e = to_fixedpoint_ref(d)->ctx().get_ground_sat_answer();
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_fixedpoint_get_rules_along_trace(
        Z3_context c,
        Z3_fixedpoint d)
    {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_rules_along_trace(c, d);
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        expr_ref_vector rules(m);
        svector<symbol> names;
        
        to_fixedpoint_ref(d)->ctx().get_rules_along_trace_as_formulas(rules, names);
        for (unsigned i = 0; i < rules.size(); ++i) {
            v->m_ast_vector.push_back(rules[i].get());
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_symbol Z3_API Z3_fixedpoint_get_rule_names_along_trace(
        Z3_context c,
        Z3_fixedpoint d)
    {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_rule_names_along_trace(c, d);
        ast_manager& m = mk_c(c)->m();
        Z3_ast_vector_ref* v = alloc(Z3_ast_vector_ref, *mk_c(c), m);
        mk_c(c)->save_object(v);
        expr_ref_vector rules(m);
        svector<symbol> names;
        std::stringstream ss;
        
        to_fixedpoint_ref(d)->ctx().get_rules_along_trace_as_formulas(rules, names);
        for (unsigned i = 0; i < names.size(); ++i) {
            ss << ";" << names[i].str();
        }
        RETURN_Z3(of_symbol(symbol(ss.str().substr(1).c_str())));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_fixedpoint_add_invariant(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred, Z3_ast property) {
        Z3_TRY;
        LOG_Z3_fixedpoint_add_invariant(c, d, pred, property);
        RESET_ERROR_CODE();
        to_fixedpoint_ref(d)->ctx ().add_invariant(to_func_decl(pred), to_expr(property));        
        Z3_CATCH;
    }

    Z3_ast Z3_API Z3_fixedpoint_get_reachable(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred) {
        Z3_TRY;
        LOG_Z3_fixedpoint_get_reachable(c, d, pred);
        RESET_ERROR_CODE();
        expr_ref r = to_fixedpoint_ref(d)->ctx().get_reachable(to_func_decl(pred));
        mk_c(c)->save_ast_trail(r);        
        RETURN_Z3(of_expr(r.get()));
        Z3_CATCH_RETURN(nullptr);
    }

