/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_consequences.cpp

Abstract:

    Tuned consequence finding for smt_context.

Author:

    nbjorner 2016-07-28.

Revision History:

--*/
#include "smt_context.h"
#include "ast_util.h"
#include "datatype_decl_plugin.h"
#include "model_pp.h"

namespace smt {

    expr_ref context::antecedent2fml(index_set const& vars) {
        expr_ref_vector premises(m_manager);
        index_set::iterator it = vars.begin(), end = vars.end();
        for (; it != end; ++it) {
            expr* e =  bool_var2expr(*it);
            premises.push_back(get_assignment(*it) != l_false ? e : m_manager.mk_not(e));
        }
        return mk_and(premises);
    }

    //
    // The literal lit is assigned at the search level, so it follows from the assumptions.
    // We retrieve the set of assumptions it depends on in the set 's'.
    // The map m_antecedents contains the association from these literals to the assumptions they depend on.
    // We then examine the contents of the literal lit and augment the set of consequences in one of the following cases:
    // - e is a propositional atom and it is one of the variables that is to be fixed.
    // - e is an equality between a variable and value that is to be fixed.
    // - e is a data-type recognizer of a variable that is to be fixed.
    // 
    void context::extract_fixed_consequences(literal lit, obj_map<expr, expr*>& vars, index_set const& assumptions, expr_ref_vector& conseq) {
        ast_manager& m = m_manager;
        datatype_util dt(m);
        expr* e1, *e2;       
        expr_ref fml(m);        
        if (lit == true_literal) return;
        expr* e = bool_var2expr(lit.var());
        index_set s;
        if (assumptions.contains(lit.var())) {
            s.insert(lit.var());
        }
        else {
            b_justification js = get_justification(lit.var());
            switch (js.get_kind()) {
            case b_justification::CLAUSE: {
                clause * cls = js.get_clause();
                if (!cls) break;
                unsigned num_lits = cls->get_num_literals();
                for (unsigned j = 0; j < num_lits; ++j) {
                    literal lit2 = cls->get_literal(j);
                    if (lit2.var() != lit.var()) {
                        s |= m_antecedents.find(lit2.var());
                    }
                }
                break;
            }
            case b_justification::BIN_CLAUSE: {
                s |= m_antecedents.find(js.get_literal().var());
                break;
            }
            case b_justification::AXIOM: {
                break;
            }
            case b_justification::JUSTIFICATION: {
                literal_vector literals;
                m_conflict_resolution->justification2literals(js.get_justification(), literals);
                for (unsigned j = 0; j < literals.size(); ++j) {
                    s |= m_antecedents.find(literals[j].var());
                }
                break;
            }
            }
        }
        m_antecedents.insert(lit.var(), s);
        TRACE("context", display_literal_verbose(tout, lit); 
              for (index_set::iterator it = s.begin(), end = s.end(); it != end; ++it) {
                  tout << " " << *it;
              }
              tout << "\n";);
        bool found = false;
        if (vars.contains(e)) {
            found = true;
            fml = lit.sign() ? m.mk_not(e) : e;
            vars.erase(e);
        }
        else if (!lit.sign() && m.is_eq(e, e1, e2)) {
            if (vars.contains(e2)) {
                std::swap(e1, e2);
            }
            if (vars.contains(e1) && m.is_value(e2)) {
                found = true;
                fml = e;
                vars.erase(e1);
            }
        }
        else if (!lit.sign() && is_app(e) && dt.is_recognizer(to_app(e)->get_decl())) {
            if (vars.contains(to_app(e)->get_arg(0))) {
                found = true;
                fml = m.mk_eq(to_app(e)->get_arg(0), m.mk_const(dt.get_recognizer_constructor(to_app(e)->get_decl())));
                vars.erase(to_app(e)->get_arg(0));
            }
        }
        if (found) {
            fml = m.mk_implies(antecedent2fml(s), fml);
            conseq.push_back(fml);
        }
    }

    void context::extract_fixed_consequences(unsigned& start, obj_map<expr, expr*>& vars, index_set const& assumptions, expr_ref_vector& conseq) {
        pop_to_search_lvl();
        SASSERT(!inconsistent());
        literal_vector const& lits = assigned_literals();
        unsigned sz = lits.size();
        for (unsigned i = start; i < sz; ++i) {            
            extract_fixed_consequences(lits[i], vars, assumptions, conseq);
        }
        start = sz;
        SASSERT(!inconsistent());
    }
    

    //
    // The assignment stack is assumed consistent.
    // For each Boolean variable, we check if there is a literal assigned to the 
    // opposite value of the reference model, and for non-Boolean variables we
    // check if the current state forces the variable to be distinct from the reference value.
    // 
    // For yet to be determined Boolean variables we furthermore force the phase to be opposite
    // to the reference value in the attempt to let the sat engine emerge with a model that
    // rules out as many non-fixed variables as possible.
    // 

    unsigned context::delete_unfixed(obj_map<expr, expr*>& var2val, expr_ref_vector& unfixed) {
        ast_manager& m = m_manager;
        ptr_vector<expr> to_delete;
        obj_map<expr,expr*>::iterator it = var2val.begin(), end = var2val.end();
        for (; it != end; ++it) {
            expr* k = it->m_key;
            expr* v = it->m_value;
            if (m.is_bool(k)) {
                literal lit = get_literal(k);
                switch (get_assignment(lit)) {
                case l_true: 
                    if (m.is_false(v)) {
                        to_delete.push_back(k);
                    }
                    else {
                        force_phase(lit.var(), false);
                    }
                    break;
                case l_false:
                    if (m.is_true(v)) {
                        to_delete.push_back(k);
                    }
                    else {
                        force_phase(lit.var(), true);
                    }
                    break;
                default:
                    to_delete.push_back(k);
                    break;
                }
            }
            else if (e_internalized(k) && m.are_distinct(v, get_enode(k)->get_root()->get_owner())) {
                to_delete.push_back(k);
            }
            else if (get_assignment(mk_diseq(k, v)) == l_true) {
                to_delete.push_back(k);
            }
        }
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            var2val.remove(to_delete[i]);
            unfixed.push_back(to_delete[i]);
        }
        return to_delete.size();
    }

#define are_equal(v, k) (e_internalized(k) && e_internalized(v) && get_enode(k)->get_root() == get_enode(v)->get_root())

    //
    // Extract equalities that are congruent at the search level.
    // Add a clause to short-circuit the congruence justifications for
    // next rounds.
    // 
    unsigned context::extract_fixed_eqs(obj_map<expr, expr*>& var2val, expr_ref_vector& conseq) {
        TRACE("context", tout << "extract fixed consequences\n";);
        ast_manager& m = m_manager;
        ptr_vector<expr> to_delete;
        expr_ref fml(m), eq(m);
        obj_map<expr,expr*>::iterator it = var2val.begin(), end = var2val.end();
        for (; it != end; ++it) {
            expr* k = it->m_key;
            expr* v = it->m_value;
            if (!m.is_bool(k) && are_equal(k, v)) {
                literal_vector literals;
                m_conflict_resolution->eq2literals(get_enode(v), get_enode(k), literals);
                index_set s;
                for (unsigned i = 0; i < literals.size(); ++i) {
                    SASSERT(get_assign_level(literals[i]) <= get_search_level());
                    s |= m_antecedents.find(literals[i].var());
                }
                
                fml = m.mk_eq(k, v);
                fml = m.mk_implies(antecedent2fml(s), fml);
                conseq.push_back(fml);
                to_delete.push_back(k);

                for (unsigned i = 0; i < literals.size(); ++i) {
                    literals[i].neg();
                }
                literal lit = mk_diseq(k, v);
                literals.push_back(lit);
                mk_clause(literals.size(), literals.c_ptr(), 0);
                TRACE("context", display_literals_verbose(tout, literals.size(), literals.c_ptr()););
            }
        }    
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            var2val.remove(to_delete[i]);
        }
        return to_delete.size();
    }

    literal context::mk_diseq(expr* e, expr* val) {
        ast_manager& m = m_manager;
        if (m.is_bool(e)) {
            return literal(get_bool_var(e), m.is_true(val));
        }
        else {
            expr_ref eq(mk_eq_atom(e, val), m);
            internalize_formula(eq, false);
            return literal(get_bool_var(eq), true);
        }
    }

    lbool context::get_consequences(expr_ref_vector const& assumptions, 
                                    expr_ref_vector const& vars, 
                                    expr_ref_vector& conseq, 
                                    expr_ref_vector& unfixed) {

        m_antecedents.reset();
        pop_to_base_lvl();
        lbool is_sat = check(assumptions.size(), assumptions.c_ptr());
        if (is_sat != l_true) {
            return is_sat;
        }
        obj_map<expr, expr*> var2val;
        index_set _assumptions;
        for (unsigned i = 0; i < assumptions.size(); ++i) {
            _assumptions.insert(get_literal(assumptions[i]).var());
        }
        model_ref mdl;
        get_model(mdl);
        ast_manager& m = m_manager;
        expr_ref_vector trail(m);
        model_evaluator eval(*mdl.get());
        expr_ref val(m);
        TRACE("context", model_pp(tout, *mdl););
        for (unsigned i = 0; i < vars.size(); ++i) {
            eval(vars[i], val);
            if (m.is_value(val)) {
                trail.push_back(val);
                var2val.insert(vars[i], val);
            } 
            else {
                unfixed.push_back(vars[i]);
            }
        }
        unsigned num_units = 0;
        extract_fixed_consequences(num_units, var2val, _assumptions, conseq);
        app_ref eq(m);
        TRACE("context", 
              tout << "vars: " << vars.size() << "\n";
              tout << "lits: " << num_units << "\n";);
        m_case_split_queue->init_search_eh();
        unsigned num_iterations = 0;
        unsigned model_threshold = 2;
        unsigned num_fixed_eqs = 0;
        unsigned num_reiterations = 0;
        while (!var2val.empty()) {
            obj_map<expr,expr*>::iterator it = var2val.begin();
            expr* e = it->m_key;
            expr* val = it->m_value;

            TRACE("context", tout << "scope level: " << get_scope_level() << "\n";);
            SASSERT(!inconsistent());

            //
            // The current variable is checked to be a backbone
            // We add the negation of the reference assignment to the variable.
            // If the variable is a Boolean, it means adding literal that has
            // the opposite value of the current reference model.
            // If the variable is a non-Boolean, it means adding a disequality.
            //
            literal lit = mk_diseq(e, val);
            mark_as_relevant(lit);
            push_scope();
            assign(lit, b_justification::mk_axiom(), true);
            flet<bool> l(m_searching, true);

            // 
            // We check if the current assignment stack can be extended to a 
            // satisfying assignment. bounded search may decide to restart, 
            // in which case it returns l_undef and clears search failure.
            //
            while (true) {
                is_sat = bounded_search();
                TRACE("context", tout << "search result: " << is_sat << "\n";);
                if (is_sat != l_true && m_last_search_failure != OK) {
                    return is_sat;
                }
                if (is_sat == l_undef) {
                    TRACE("context", tout << "restart\n";);
                    inc_limits();
                    continue;
                }
                break;
            }
            //
            // If the state is satisfiable with the current variable assigned to 
            // a different value from the reference model, it is unfixed.
            // 
            // If it is assigned above the search level we can't conclude anything
            // about its value. 
            // extract_fixed_consequences pops the assignment stack to the search level
            // so this sets up the state to retry finding fixed values.
            // 
            // Otherwise, the variable is fixed.
            // - it is either assigned at the search level to l_false, or
            // - the state is l_false, which means that the variable is fixed by
            //   the background constraints (and does not depend on assumptions).
            // 
            if (is_sat == l_true && get_assignment(lit) == l_true && is_relevant(lit)) { 
                var2val.erase(e);
                unfixed.push_back(e);
                SASSERT(!are_equal(e, val));
                TRACE("context", tout << mk_pp(e, m) << " is unfixed\n";
                      display_literal_verbose(tout, lit); tout << "\n";
                      tout << "relevant: " << is_relevant(lit) << "\n";
                      display(tout););
            }
            else if (is_sat == l_true && (get_assign_level(lit) > get_search_level() || !is_relevant(lit))) {
                TRACE("context", tout << "Retry fixing: " << mk_pp(e, m) << "\n";);
                extract_fixed_consequences(num_units, var2val, _assumptions, conseq);
                ++num_reiterations;
                continue;
            }
            else {
                //
                // The state can be labeled as inconsistent when the implied consequence does
                // not depend on assumptions, then the conflict level sits at the search level
                // which causes the conflict resolver to decide that the state is unsat.
                //
                if (l_false == is_sat) {
                    SASSERT(inconsistent());
                    m_conflict = null_b_justification;
                    m_not_l = null_literal;
                }
                TRACE("context", tout << "Fixed: " << mk_pp(e, m) << " " << is_sat << "\n";
                      if (is_sat == l_false) display(tout););
                
            }
            ++num_iterations;

            //
            // Check the slow pass: it retrieves an updated model and checks if the
            // values in the updated model differ from the values in the reference
            // model. 
            // 
            bool apply_slow_pass = model_threshold <= num_iterations || num_iterations <= 2;
            if (apply_slow_pass && is_sat == l_true) {
                delete_unfixed(var2val, unfixed);
                // The next time we check the model is after 1.5 additional iterations.
                model_threshold *= 3;
                model_threshold /= 2;                                
            }

            //
            // Walk the assignment stack at level 1 for learned consequences.
            // The current literal should be assigned at the search level unless
            // the state is is_sat == l_true and the assignment to lit is l_true.
            // This condition is checked above.
            // 
            extract_fixed_consequences(num_units, var2val, _assumptions, conseq);

            //
            // Fixed equalities can be extracted by walking all variables and checking
            // if the congruence roots are equal at the search level.
            // 
            if (apply_slow_pass) {
                num_fixed_eqs += extract_fixed_eqs(var2val, conseq);
                IF_VERBOSE(1, display_consequence_progress(verbose_stream(), num_iterations, var2val.size(), conseq.size(),
                                                           unfixed.size(), num_fixed_eqs););
                TRACE("context", display_consequence_progress(tout, num_iterations, var2val.size(), conseq.size(),
                                                              unfixed.size(), num_fixed_eqs););
            }
            TRACE("context", tout << "finishing " << mk_pp(e, m) << "\n";);
            SASSERT(!inconsistent());
            
            //
            // This becomes unnecessary when the fixed consequence are 
            // completely extracted.
            // 
            if (var2val.contains(e)) {
                TRACE("context", tout << "Fixed value to " << mk_pp(e, m) << " was not processed\n";);
                expr_ref fml(m);
                fml = m.mk_eq(e, var2val.find(e));
                if (!m_antecedents.contains(lit.var())) {
                    extract_fixed_consequences(lit, var2val, _assumptions, conseq);
                }
                fml = m.mk_implies(antecedent2fml(m_antecedents[lit.var()]), fml);
                conseq.push_back(fml);
                var2val.erase(e);
            }        
        }
        end_search();
        DEBUG_CODE(validate_consequences(assumptions, vars, conseq, unfixed););
        return l_true;
    }

    lbool context::get_consequences2(expr_ref_vector const& assumptions, 
                                    expr_ref_vector const& vars, 
                                    expr_ref_vector& conseq, 
                                    expr_ref_vector& unfixed) {

        m_antecedents.reset();
        pop_to_base_lvl();
        lbool is_sat = check(assumptions.size(), assumptions.c_ptr());
        if (is_sat != l_true) {
            TRACE("context", tout << is_sat << "\n";);
            return is_sat;
        }
        obj_map<expr, expr*> var2val;
        index_set _assumptions;
        for (unsigned i = 0; i < assumptions.size(); ++i) {
            _assumptions.insert(get_literal(assumptions[i]).var());
        }
        model_ref mdl;
        get_model(mdl);
        ast_manager& m = m_manager;
        expr_ref_vector trail(m);
        model_evaluator eval(*mdl.get());
        expr_ref val(m);
        TRACE("context", model_pp(tout, *mdl););
        for (unsigned i = 0; i < vars.size(); ++i) {
            eval(vars[i], val);
            if (m.is_value(val)) {
                trail.push_back(val);
                var2val.insert(vars[i], val);
            } 
            else {
                unfixed.push_back(vars[i]);
            }
        }
        unsigned num_units = 0;
        extract_fixed_consequences(num_units, var2val, _assumptions, conseq);
        app_ref eq(m);
        TRACE("context", 
              tout << "vars: " << vars.size() << "\n";
              tout << "lits: " << num_units << "\n";);
        m_case_split_queue->init_search_eh();
        unsigned num_iterations = 0;
        unsigned num_fixed_eqs = 0;
        unsigned chunk_size = 100; 
        
        while (!var2val.empty()) {
            obj_map<expr,expr*>::iterator it = var2val.begin(), end = var2val.end();
            unsigned num_vars = 0;
            for (; it != end && num_vars < chunk_size; ++it) {
                if (get_cancel_flag()) {
                    return l_undef;
                }
                expr* e = it->m_key;
                expr* val = it->m_value;
                literal lit = mk_diseq(e, val);
                mark_as_relevant(lit);
                if (get_assignment(lit) != l_undef) {
                    continue;
                }
                ++num_vars;
                push_scope();
                assign(lit, b_justification::mk_axiom(), true);
                if (!propagate()) {
                    if (!resolve_conflict() || inconsistent()) {
                        TRACE("context", tout << "inconsistent\n";);
                        SASSERT(inconsistent());
                        m_conflict = null_b_justification;
                        m_not_l = null_literal;
                        SASSERT(m_search_lvl == get_search_level());
                    }
                }
            }
            SASSERT(!inconsistent());
            ++num_iterations;

            lbool is_sat = l_undef;
            while (true) {
                is_sat = bounded_search();
                if (is_sat != l_true && m_last_search_failure != OK) {
                    return is_sat;
                }
                if (is_sat == l_undef) {
                    IF_VERBOSE(1, verbose_stream() << "(get-consequences inc-limits)\n";);
                    inc_limits();
                    continue;
                }
                break;
            }
            if (is_sat == l_false) {
                SASSERT(inconsistent());
                m_conflict = null_b_justification;
                m_not_l = null_literal;
            }
            if (is_sat == l_true) {
                delete_unfixed(var2val, unfixed);
            }
            extract_fixed_consequences(num_units, var2val, _assumptions, conseq);
            num_fixed_eqs += extract_fixed_eqs(var2val, conseq);
            IF_VERBOSE(1, display_consequence_progress(verbose_stream(), num_iterations, var2val.size(), conseq.size(),
                                                       unfixed.size(), num_fixed_eqs););
            TRACE("context", display_consequence_progress(tout, num_iterations, var2val.size(), conseq.size(),
                                                       unfixed.size(), num_fixed_eqs););
        }

        end_search();
        DEBUG_CODE(validate_consequences(assumptions, vars, conseq, unfixed););
        return l_true;
    }

    
    void context::display_consequence_progress(std::ostream& out, unsigned it, unsigned nv, unsigned fixed, unsigned unfixed, unsigned eq) {        
        out  << "(get-consequences"
             << " iterations: " << it
             << " variables: " << nv
             << " fixed: " << fixed
             << " unfixed: " << unfixed
             << " fixed-eqs: " << eq
             << ")\n";
    }  


    //
    // Validate, in a slow pass, that the current consequences are correctly 
    // extracted.
    // 
    void context::validate_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, 
                                        expr_ref_vector const& conseq, expr_ref_vector const& unfixed) {
        ast_manager& m = m_manager;
        expr_ref tmp(m);
        SASSERT(!inconsistent());
        for (unsigned i = 0; i < conseq.size(); ++i) {
            push();            
            for (unsigned j = 0; j < assumptions.size(); ++j) {
                assert_expr(assumptions[j]);
            }
            TRACE("context", tout << "checking: " << mk_pp(conseq[i], m) << "\n";);
            tmp = m.mk_not(conseq[i]);
            assert_expr(tmp);
            lbool is_sat = check();
            SASSERT(is_sat != l_true);
            pop(1);
        }
        model_ref mdl;
        for (unsigned i = 0; i < unfixed.size(); ++i) {
            push();            
            for (unsigned j = 0; j < assumptions.size(); ++j) {
                assert_expr(assumptions[j]);
            }
            TRACE("context", tout << "checking unfixed: " << mk_pp(unfixed[i], m) << "\n";);
            lbool is_sat = check();            
            SASSERT(is_sat != l_false);
            if (is_sat == l_true) {
                get_model(mdl);
                mdl->eval(unfixed[i], tmp);
                if (m.is_value(tmp)) {
                    tmp = m.mk_not(m.mk_eq(unfixed[i], tmp));
                    assert_expr(tmp);
                    is_sat = check();
                    SASSERT(is_sat != l_false);
                }
            }
            pop(1);
        }
    }

}
