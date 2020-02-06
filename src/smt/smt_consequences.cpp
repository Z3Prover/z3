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
#include "util/max_cliques.h"
#include "util/stopwatch.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/datatype_decl_plugin.h"
#include "model/model_pp.h"
#include "smt/smt_context.h"

namespace smt {

    expr_ref context::antecedent2fml(index_set const& vars) {
        expr_ref_vector premises(m);
        index_set::iterator it = vars.begin(), end = vars.end();
        for (; it != end; ++it) {
            expr* e =  bool_var2expr(*it);
            e = m_assumption2orig.find(e);
            premises.push_back(get_assignment(*it) != l_false ? e : m.mk_not(e));
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
    void context::extract_fixed_consequences(literal lit, index_set const& assumptions, expr_ref_vector& conseq) {
        datatype_util dt(m);
        expr* e1, *e2;       
        expr_ref fml(m);        
        if (lit == true_literal) return;
        expr* e = bool_var2expr(lit.var());
        TRACE("context", display(tout << mk_pp(e, m) << "\n"););
        index_set s;
        if (assumptions.contains(lit.var())) {
            s.insert(lit.var());
        }
        else {
            justify(lit, s);
        }
        m_antecedents.insert(lit.var(), s);
        TRACE("context", display_literal_verbose(tout, lit); 
              for (index_set::iterator it = s.begin(), end = s.end(); it != end; ++it) {
                  tout << " " << *it;
              }
              tout << "\n";);
        bool found = false;
        if (m_var2val.contains(e)) {
            found = true;
            m_var2val.erase(e);
            e = m_var2orig.find(e);
            fml = lit.sign() ? m.mk_not(e) : e;
        }
        else if (!lit.sign() && m.is_eq(e, e1, e2)) {
            if (m_var2val.contains(e2) && m.is_value(e1)) {
                found = true;
                m_var2val.erase(e2);
                e2 = m_var2orig.find(e2);
                std::swap(e1, e2);
                fml = m.mk_eq(e1, e2);
            }
            else if (m_var2val.contains(e1) && m.is_value(e2)) {                
                found = true;
                m_var2val.erase(e1);
                e1 = m_var2orig.find(e1);
                fml = m.mk_eq(e1, e2);
            }
        }
        else if (!lit.sign() && is_app(e) && dt.is_recognizer(to_app(e)->get_decl())) {
            if (m_var2val.contains(to_app(e)->get_arg(0))) {
                found = true;
                fml = m.mk_eq(to_app(e)->get_arg(0), m.mk_const(dt.get_recognizer_constructor(to_app(e)->get_decl())));
                m_var2val.erase(to_app(e)->get_arg(0));
            }
        }
        if (found) {
            fml = m.mk_implies(antecedent2fml(s), fml);
            conseq.push_back(fml);
        }
    }

    void context::justify(literal lit, index_set& s) {
        (void)m;
        b_justification js = get_justification(lit.var());
        switch (js.get_kind()) {
        case b_justification::CLAUSE: {
            clause * cls = js.get_clause();
            if (!cls) break;
            for (literal lit2 : *cls) {
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
                if (!m_antecedents.contains(literals[j].var())) {
                    TRACE("context", tout << literals[j] << " " << mk_pp(bool_var2expr(literals[j].var()), m) << "\n";);
                }
                s |= m_antecedents.find(literals[j].var());
            }
            break;
        }
        }        
    }

    void context::extract_fixed_consequences(unsigned& start, index_set const& assumptions, expr_ref_vector& conseq) {
        pop_to_search_lvl();
        SASSERT(!inconsistent());
        literal_vector const& lits = assigned_literals();
        unsigned sz = lits.size();
        for (unsigned i = start; i < sz; ++i) {            
            extract_fixed_consequences(lits[i], assumptions, conseq);
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

    unsigned context::delete_unfixed(expr_ref_vector& unfixed) {
        ptr_vector<expr> to_delete;
        obj_map<expr,expr*>::iterator it = m_var2val.begin(), end = m_var2val.end();
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
            m_var2val.remove(to_delete[i]);
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
    unsigned context::extract_fixed_eqs(expr_ref_vector& conseq) {
        TRACE("context", tout << "extract fixed consequences\n";);
        ptr_vector<expr> to_delete;
        expr_ref fml(m), eq(m);
        obj_map<expr,expr*>::iterator it = m_var2val.begin(), end = m_var2val.end();
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
                
                fml = m.mk_eq(m_var2orig.find(k), v);
                fml = m.mk_implies(antecedent2fml(s), fml);
                conseq.push_back(fml);
                to_delete.push_back(k);

                for (unsigned i = 0; i < literals.size(); ++i) {
                    literals[i].neg();
                }
                literal lit = mk_diseq(k, v);
                literals.push_back(lit);
                mk_clause(literals.size(), literals.c_ptr(), nullptr);
                TRACE("context", display_literals_verbose(tout, literals.size(), literals.c_ptr()););
            }
        }    
        for (unsigned i = 0; i < to_delete.size(); ++i) {
            m_var2val.remove(to_delete[i]);
        }
        return to_delete.size();
    }

    literal context::mk_diseq(expr* e, expr* val) {
        if (m.is_bool(e) && b_internalized(e)) {
            return literal(get_bool_var(e), m.is_true(val));
        }
        else if (m.is_bool(e)) {
            internalize_formula(e, false);
            return literal(get_bool_var(e), !m.is_true(val));
        }
        else {
            expr_ref eq(mk_eq_atom(e, val), m);
            internalize_formula(eq, false);
            return literal(get_bool_var(eq), true);
        }
    }

    lbool context::get_consequences(expr_ref_vector const& assumptions0, 
                                    expr_ref_vector const& vars0, 
                                    expr_ref_vector& conseq, 
                                    expr_ref_vector& unfixed) {

        m_antecedents.reset();
        m_antecedents.insert(true_literal.var(), index_set());
        pop_to_base_lvl();
        expr_ref_vector vars(m), assumptions(m);
        m_var2val.reset();
        m_var2orig.reset();
        m_assumption2orig.reset();
        bool pushed = false;
        for (unsigned i = 0; i < vars0.size(); ++i) {
            expr* v = vars0[i];
            if (is_uninterp_const(v)) {
                vars.push_back(v);
                m_var2orig.insert(v, v);
            }
            else {
                if (!pushed) {
                    pushed = true;
                    push();
                }
                expr_ref c(m.mk_fresh_const("v", m.get_sort(v)), m);
                expr_ref eq(m.mk_eq(c, v), m);
                assert_expr(eq);
                vars.push_back(c);
                m_var2orig.insert(c, v);
            }
        }
        for (unsigned i = 0; i < assumptions0.size(); ++i) {
            expr* a = assumptions0[i];
            if (is_uninterp_const(a)) {
                assumptions.push_back(a);
                m_assumption2orig.insert(a, a);
            }
            else {
                if (!pushed) {
                    pushed = true;
                    push();
                }
                expr_ref c(m.mk_fresh_const("a", m.get_sort(a)), m);
                expr_ref eq(m.mk_eq(c, a), m);
                assert_expr(eq);
                assumptions.push_back(c);
                m_assumption2orig.insert(c, a);                
            }
        }
        lbool is_sat = check(assumptions.size(), assumptions.c_ptr());
        if (is_sat != l_true) {
            TRACE("context", tout << is_sat << "\n";);
            if (pushed) pop(1);            
            return is_sat;
        }

        index_set _assumptions;
        for (unsigned i = 0; i < assumptions.size(); ++i) {
            _assumptions.insert(get_literal(assumptions[i].get()).var());
        }
        model_ref mdl;
        get_model(mdl);
        expr_ref_vector trail(m);
        model_evaluator eval(*mdl.get());
        expr_ref val(m);
        TRACE("context", model_pp(tout, *mdl););
        for (unsigned i = 0; i < vars.size(); ++i) {
            eval(vars[i].get(), val);
            if (m.is_value(val)) {
                trail.push_back(val);
                m_var2val.insert(vars[i].get(), val);
            } 
            else {
                unfixed.push_back(vars[i].get());
            }
        }
        unsigned num_units = 0;
        extract_fixed_consequences(num_units, _assumptions, conseq);
        app_ref eq(m);
        TRACE("context", 
              tout << "vars: " << vars.size() << "\n";
              tout << "lits: " << num_units << "\n";);
        m_case_split_queue->init_search_eh();
        unsigned num_iterations = 0;
        unsigned num_fixed_eqs = 0;
        unsigned chunk_size = 100; 
        
        while (!m_var2val.empty()) {
            obj_map<expr,expr*>::iterator it = m_var2val.begin(), end = m_var2val.end();
            unsigned num_vars = 0;
            for (; it != end && num_vars < chunk_size; ++it) {
                if (get_cancel_flag()) {
                    if (pushed) pop(1);
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
                    if (pushed) pop(1);
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
                delete_unfixed(unfixed);
            }
            extract_fixed_consequences(num_units, _assumptions, conseq);
            num_fixed_eqs += extract_fixed_eqs(conseq);
            IF_VERBOSE(1, display_consequence_progress(verbose_stream(), num_iterations, m_var2val.size(), conseq.size(),
                                                       unfixed.size(), num_fixed_eqs););
            TRACE("context", display_consequence_progress(tout, num_iterations, m_var2val.size(), conseq.size(),
                                                       unfixed.size(), num_fixed_eqs););
        }

        end_search();
        DEBUG_CODE(validate_consequences(assumptions, vars, conseq, unfixed););
        if (pushed) {
            pop(1);
        }
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

    void context::extract_cores(expr_ref_vector const& asms, vector<expr_ref_vector>& cores, unsigned& min_core_size) {
        index_set _asms, _nasms;
        u_map<expr*> var2expr;
        for (unsigned i = 0; i < asms.size(); ++i) {
            literal lit = get_literal(asms[i]);
            _asms.insert(lit.index());
            _nasms.insert((~lit).index());
            var2expr.insert(lit.var(), asms[i]);
        }

        m_antecedents.reset();
        literal_vector const& lits = assigned_literals();
        for (unsigned i = 0; i < lits.size(); ++i) {
            literal lit = lits[i];
            index_set s;
            if (_asms.contains(lit.index())) {
                s.insert(lit.var());
            }
            else {
                justify(lit, s);
            }
            m_antecedents.insert(lit.var(), s);
            if (_nasms.contains(lit.index())) {
                expr_ref_vector core(m);
                index_set::iterator it = s.begin(), end = s.end();
                for (; it != end; ++it) {
                    core.push_back(var2expr[*it]);
                }
                core.push_back(var2expr[lit.var()]);
                cores.push_back(core);
                min_core_size = std::min(min_core_size, core.size());
            }
        }
    }

    void context::preferred_sat(literal_vector& lits) {
        bool retry = true;
        while (retry) {
            retry = false;
            for (unsigned i = 0; i < lits.size(); ++i) {
                literal lit = lits[i];
                if (lit == null_literal || get_assignment(lit) != l_undef) {
                    continue;
                }
                push_scope();
                assign(lit, b_justification::mk_axiom(), true);
                while (!propagate()) {
                    lits[i] = null_literal;
                    retry = true;
                    if (!resolve_conflict() || inconsistent()) {
                        SASSERT(inconsistent());
                        return;
                    }
                }      
            }
        }
    }

    void context::display_partial_assignment(std::ostream& out, expr_ref_vector const& asms, unsigned min_core_size) {
        unsigned num_true = 0, num_false = 0, num_undef = 0;
        for (unsigned i = 0; i < asms.size(); ++i) {
            literal lit = get_literal(asms[i]);
            if (get_assignment(lit) == l_false) {
                ++num_false;
            }
            if (get_assignment(lit) == l_true) {
                ++num_true;
            }
            if (get_assignment(lit) == l_undef) {
                ++num_undef;
            }
        }
        out << "(smt.preferred-sat true: " << num_true << " false: " << num_false << " undef: " << num_undef << " min core: " << min_core_size << ")\n"; 
    }

    lbool context::preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) {        
        pop_to_base_lvl();
        cores.reset();
        setup_context(false);
        internalize_assertions();
        if (m_asserted_formulas.inconsistent() || inconsistent()) {
            return l_false;
        }
        reset_model();
        init_search();
        flet<bool> l(m_searching, true);
        unsigned level = m_scope_lvl;
        unsigned min_core_size = UINT_MAX;
        lbool is_sat = l_true;
        unsigned num_restarts = 0;

        while (true) {
            if (m.canceled()) {
                is_sat = l_undef;
                break;
            }
            literal_vector lits;
            for (unsigned i = 0; i < asms.size(); ++i) {
                lits.push_back(get_literal(asms[i]));
            }
            preferred_sat(lits);
            if (inconsistent()) {
                SASSERT(m_scope_lvl == level);
                is_sat = l_false;
                break;
            }
            extract_cores(asms, cores, min_core_size); 
            IF_VERBOSE(1, display_partial_assignment(verbose_stream(), asms, min_core_size););
            
            if (min_core_size <= 10) {
                is_sat = l_undef;
                break;
            }
            
            is_sat = bounded_search();
            if (!restart(is_sat, level)) {
                break;
            }
            ++num_restarts;
            if (num_restarts >= min_core_size) {
                is_sat = l_undef;
                while (num_restarts <= 10*min_core_size) {
                    is_sat = bounded_search();
                    if (!restart(is_sat, level)) {
                        break;
                    }
                    ++num_restarts;
                }
                break;
            }            
        }
        end_search();

        return check_finalize(is_sat);
    }

    struct neg_literal {
        unsigned negate(unsigned i) {
            return (~to_literal(i)).index();
        }
    };

    lbool context::find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) {
        unsigned_vector ps;
        max_cliques<neg_literal> mc;
        expr_ref lit(m);
        for (unsigned i = 0; i < vars.size(); ++i) {
            expr* n = vars[i];
            bool neg = m.is_not(n, n);
            if (b_internalized(n)) {
                ps.push_back(literal(get_bool_var(n), neg).index());
            }
        }
        for (unsigned i = 0; i < m_watches.size(); ++i) {
            watch_list & w = m_watches[i];
            for (literal const* it = w.begin_literals(), *end = w.end_literals(); it != end; ++it) {
                unsigned idx1 = (~to_literal(i)).index();
                unsigned idx2 = it->index();
                if (idx1 < idx2) {
                    mc.add_edge(idx1, idx2);
                }
            }
        }
        vector<unsigned_vector> _mutexes;
        mc.cliques(ps, _mutexes);
        for (unsigned i = 0; i < _mutexes.size(); ++i) {
            expr_ref_vector lits(m);
            for (unsigned j = 0; j < _mutexes[i].size(); ++j) {
                literal2expr(to_literal(_mutexes[i][j]), lit);
                lits.push_back(lit);
            }
            mutexes.push_back(lits);
        }        
        return l_true;
    }

    //
    // Validate, in a slow pass, that the current consequences are correctly 
    // extracted.
    // 
    void context::validate_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, 
                                        expr_ref_vector const& conseq, expr_ref_vector const& unfixed) {
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
            VERIFY(check() != l_true);
            pop(1);
        }
        model_ref mdl;
        for (unsigned i = 0; i < unfixed.size(); ++i) {
            push();            
            for (expr* a : assumptions) 
                assert_expr(a);
            TRACE("context", tout << "checking unfixed: " << mk_pp(unfixed[i], m) << "\n";);
            lbool is_sat = check();            
            SASSERT(is_sat != l_false);
            if (is_sat == l_true) {
                get_model(mdl);
                tmp = (*mdl)(unfixed[i]);
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
