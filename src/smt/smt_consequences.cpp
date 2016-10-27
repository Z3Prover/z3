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


    lbool context::find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
        index_set lits;
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr* n = vars[i];
            bool neg = m_manager.is_not(n, n);
            if (b_internalized(n)) {
                lits.insert(literal(get_bool_var(n), neg).index());
            }
        }
        while (!lits.empty()) {
            literal_vector mutex;
            index_set other(lits);
            while (!other.empty()) {
                index_set conseq;
                literal p = to_literal(*other.begin());
                other.erase(p.index());
                mutex.push_back(p);
                if (other.empty()) {
                    break;
                }
                get_reachable(p, other, conseq);
                other = conseq;
            }
            if (mutex.size() > 1) {
                expr_ref_vector mux(m_manager);
                for (unsigned i = 0; i < mutex.size(); ++i) {
                    expr_ref e(m_manager);
                    literal2expr(mutex[i], e);
                    mux.push_back(e);
                }
                mutexes.push_back(mux);
            }
            for (unsigned i = 0; i < mutex.size(); ++i) {
                lits.remove(mutex[i].index());
            }
        }
        return l_true;
    }

    void context::get_reachable(literal p, index_set& goal, index_set& reachable) {
        index_set seen;
        literal_vector todo;
        todo.push_back(p);
        while (!todo.empty()) {
            p = todo.back();
            todo.pop_back();
            if (seen.contains(p.index())) {
                continue;
            }
            seen.insert(p.index());
            literal np = ~p;
            if (goal.contains(np.index())) {
                reachable.insert(np.index());
            }
            watch_list & w = m_watches[np.index()];
            todo.append(static_cast<unsigned>(w.end_literals() - w.begin_literals()), w.begin_literals());
        }
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
