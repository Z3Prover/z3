/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_context.cpp

Abstract:

    PDR predicate transformers and search context.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-20.

Revision History:

    Based on pdr_dl.cpp by
     Krystof Hoder (t-khoder) 2011-9-19.

Notes:

   TODO:
   - fix the slicing with covers.
   - 
   
--*/


#include <sstream>
#include "dl_util.h"
#include "rewriter.h"
#include "rewriter_def.h"
#include "var_subst.h"
#include "util.h"
#include "pdr_prop_solver.h"
#include "pdr_context.h"
#include "pdr_generalizers.h"
#include "datatype_decl_plugin.h"
#include "for_each_expr.h"
#include "model_v2_pp.h"
#include "dl_rule_set.h"
#include "unit_subsumption_tactic.h"
#include "model_smt2_pp.h"
#include "dl_mk_rule_inliner.h"
#include "ast_smt2_pp.h"
#include "qe_lite.h"
#include "ast_ll_pp.h"
#include "proof_checker.h"

namespace pdr {


    static const unsigned infty_level = UINT_MAX;

    static bool is_infty_level(unsigned lvl) { return lvl == infty_level; }

    static unsigned next_level(unsigned lvl) { return is_infty_level(lvl)?lvl:(lvl+1); }
    
    // ----------------
    // pred_tansformer

    pred_transformer::pred_transformer(context& ctx, manager& pm, func_decl* head): 
        pm(pm), m(pm.get_manager()),
        ctx(ctx), m_head(head, m), 
        m_sig(m), m_solver(pm, head->get_name()),
        m_invariants(m), m_transition(m), m_initial_state(m), 
        m_reachable(pm, pm.get_params()) {}

    pred_transformer::~pred_transformer() {
        qinst_map::iterator it = m_rule2qinst.begin(), end = m_rule2qinst.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        rule2inst::iterator it2 = m_rule2inst.begin(), end2 = m_rule2inst.end();
        for (; it2 != end2; ++it2) {
            dealloc(it2->m_value);
        }
        rule2expr::iterator it3 = m_rule2transition.begin(), end3 = m_rule2transition.end();
        for (; it3 != end3; ++it3) {
            m.dec_ref(it3->m_value);
        }
    }

    std::ostream& pred_transformer::display(std::ostream& out) const {
        if (!rules().empty()) out << "rules\n";
        for (unsigned i = 0; i < rules().size(); ++i) {
            rules()[i]->display_smt2(m, out) << "\n";
        }        
        out << "transition\n" << mk_pp(transition(), m) << "\n";
        return out;
    }

    void pred_transformer::collect_statistics(statistics& st) const {
        m_solver.collect_statistics(st);
        m_reachable.collect_statistics(st);
        st.update("PDR num propagations", m_stats.m_num_propagations);
        unsigned np = m_invariants.size();
        for (unsigned i = 0; i < m_levels.size(); ++i) {
            np += m_levels[i].size();
        } 
        st.update("PDR num properties", np); 
    }
    
    void pred_transformer::init_sig() {
        if (m_sig.empty()) {           
            for (unsigned i = 0; i < m_head->get_arity(); ++i) {
                sort * arg_sort = m_head->get_domain(i);
                std::stringstream name_stm;
                name_stm << m_head->get_name() << '_' << i;
                func_decl_ref stm(m);
                stm = m.mk_func_decl(symbol(name_stm.str().c_str()), 0, (sort*const*)0, arg_sort);
                m_sig.push_back(pm.get_o_pred(stm, 0));       
            }
        }
    }

    void pred_transformer::ensure_level(unsigned level) {
        if (is_infty_level(level)) {
            return;
        }
        while (m_levels.size() <= level) {
            m_solver.add_level();
            m_levels.push_back(expr_ref_vector(m));
        }
    }

    bool pred_transformer::is_reachable(expr* state) {
        return m_reachable.is_reachable(state);
    }

    datalog::rule const& pred_transformer::find_rule(model_core const& model) const {
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        TRACE("pdr_verbose",
              for (; it != end; ++it) {
                  expr* pred = it->m_key;
                  tout << mk_pp(pred, m) << ":\n";
                  if (it->m_value) it->m_value->display_smt2(m, tout) << "\n";                  
              }
        );
        
        it = m_tag2rule.begin();
        if (m_tag2rule.size() == 1) {
            return *it->m_value;
        }

        expr_ref vl(m);
        for (; it != end; ++it) {
            expr* pred = it->m_key;
            TRACE("pdr", tout << mk_pp(pred, m) << "\n";);
            if (model.eval(to_app(pred)->get_decl(), vl) && m.is_true(vl)) {
                return *it->m_value;
            }
        }
        UNREACHABLE();
        return *((datalog::rule*)0);
    }

    void pred_transformer::find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& preds) const {
        preds.reset();
        unsigned tail_sz = r.get_uninterpreted_tail_size();
        for (unsigned ti = 0; ti < tail_sz; ti++) {
            preds.push_back(r.get_tail(ti)->get_decl());
        }
    }

    void pred_transformer::find_predecessors(model_core const& model, ptr_vector<func_decl>& preds) const {
        find_predecessors(find_rule(model), preds);        
    }

    void pred_transformer::remove_predecessors(expr_ref_vector& literals) {
        // remove tags
        for (unsigned i = 0; i < literals.size(); ) {
            expr* l = literals[i].get();
            m.is_not(l, l);
            if (m_tag2rule.contains(l)) {
                literals[i] = literals.back();
                literals.pop_back();
            }
            else {
                ++i;
            }
        }
    }

    void pred_transformer::simplify_formulas(tactic& tac, expr_ref_vector& v) {
        goal_ref g(alloc(goal, m, false, false, false));
        for (unsigned j = 0; j < v.size(); ++j) g->assert_expr(v[j].get()); 
        model_converter_ref mc;
        proof_converter_ref pc;
        expr_dependency_ref core(m);
        goal_ref_buffer result;
        tac(g, result, mc, pc, core);
        SASSERT(result.size() == 1);
        goal* r = result[0];
        v.reset();
        for (unsigned j = 0; j < r->size(); ++j) v.push_back(r->form(j));            
    }

    void pred_transformer::simplify_formulas() {
        tactic_ref us = mk_unit_subsumption_tactic(m);
        simplify_formulas(*us, m_invariants);
        for (unsigned i = 0; i < m_levels.size(); ++i) {
            simplify_formulas(*us, m_levels[i]);
        }             
    }

    expr_ref pred_transformer::get_formulas(unsigned level, bool add_axioms) {
        expr_ref_vector res(m);
        if (add_axioms) {
            res.push_back(pm.get_background());
            res.push_back((level == 0)?initial_state():transition());
        }
        res.append(m_invariants);
        for (unsigned i = level; i < m_levels.size(); ++i) {
            res.append(m_levels[i]);
        }     
        return pm.mk_and(res);
    }

    expr_ref pred_transformer::get_propagation_formula(decl2rel const& pts, unsigned level) {
        expr_ref result(m), tmp1(m), tmp2(m);
        expr_ref_vector conj(m);
        if (level == 0) {
            conj.push_back(initial_state());
        }
        else {
            conj.push_back(transition());
        }
        conj.push_back(get_formulas(level, true));        
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        for (; level > 0 && it != end; ++it) {
            expr* tag = it->m_key;
            datalog::rule const* r = it->m_value;
            if (!r) continue;
            find_predecessors(*r, m_predicates);
            for (unsigned i = 0; i < m_predicates.size(); ++i) {
                func_decl* d = m_predicates[i];
                pred_transformer & pt = *pts.find(d);
                tmp1 = pt.get_formulas(level-1, false);
                TRACE("pdr", tout << mk_pp(tmp1, m) << "\n";);
                pm.formula_n2o(tmp1, tmp2, i, false);
                conj.push_back(m.mk_implies(tag, tmp2));
            }
        }                  
        return pm.mk_and(conj);
    }

    bool pred_transformer::propagate_to_next_level(unsigned src_level) {
        unsigned tgt_level = next_level(src_level);
        ensure_level(next_level(tgt_level));
        expr_ref_vector& src = m_levels[src_level];

        CTRACE("pdr", !src.empty(), 
               tout << "propagating " << src_level << " to " << tgt_level;
               tout << " for relation " << head()->get_name() << "\n";);
                
        for (unsigned i = 0; i < src.size(); ) {
            expr * curr = src[i].get();                  
            unsigned stored_lvl;
            VERIFY(m_prop2level.find(curr, stored_lvl));
            SASSERT(stored_lvl >= src_level);
            bool assumes_level;
            if (stored_lvl > src_level) {
                TRACE("pdr", tout << "at level: "<< stored_lvl << " " << mk_pp(curr, m) << "\n";);
                src[i] = src.back();
                src.pop_back();
            }
            else if (is_invariant(tgt_level, curr, false, assumes_level)) {
                
                add_property(curr, tgt_level); // assumes_level?tgt_level:infty_level
                TRACE("pdr", tout << "is invariant: "<< tgt_level << " " << mk_pp(curr, m) << "\n";);              
                src[i] = src.back();
                src.pop_back();
                ++m_stats.m_num_propagations;
            }
            else {
                TRACE("pdr", tout << "not propagated: " << mk_pp(curr, m) << "\n";); 
                ++i;
            }
        }        
        IF_VERBOSE(2, verbose_stream() << "propagate: ";
                   if (is_infty_level(src_level)) {
                       verbose_stream() << "infty"; 
                   }
                   else {
                       verbose_stream() << src_level;
                   }
                   verbose_stream() << "\n";
                   for (unsigned i = 0; i < src.size(); ++i) {
                       verbose_stream() << mk_pp(src[i].get(), m) << "\n";   
                   });
        return src.empty();
    }

    bool pred_transformer::add_property1(expr * lemma, unsigned lvl) {        
        if (is_infty_level(lvl)) {
            if (m.is_false(lemma)) {
                return false;
            }
            if (!m_invariants.contains(lemma)) {
                TRACE("pdr", tout << "property1: " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
                m_invariants.push_back(lemma);
                m_solver.add_formula(lemma);
                return true;
            }
            else {
                TRACE("pdr", tout << "already contained: " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
                return false;
            }
        }
        ensure_level(lvl);        
        unsigned old_level;
        if (!m_prop2level.find(lemma, old_level) || old_level < lvl) {
            TRACE("pdr", tout << "property1: " << lvl << " " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
            m_levels[lvl].push_back(lemma);
            m_prop2level.insert(lemma, lvl);
            m_solver.add_level_formula(lemma, lvl);
            return true;
        }
        else {
            TRACE("pdr", tout << "old-level: " << old_level << " " << head()->get_name() << " " << mk_pp(lemma, m) << "\n";);
            return false;
        }
    }

    void pred_transformer::add_child_property(pred_transformer& child, expr* lemma, unsigned lvl) {
        ensure_level(lvl);
        expr_ref_vector fmls(m);
        mk_assumptions(child.head(), lemma, fmls);
        for (unsigned i = 0; i < fmls.size(); ++i) {
            TRACE("pdr", tout << "child property: " << mk_pp(fmls[i].get(), m) << "\n";);
            if (is_infty_level(lvl)) {
                m_solver.add_formula(fmls[i].get());
            }
            else {
                m_solver.add_level_formula(fmls[i].get(), lvl);
            }
        }
    }

    void pred_transformer::add_property(expr* lemma, unsigned lvl) {
        expr_ref_vector lemmas(m);
        datalog::flatten_and(lemma, lemmas);
        for (unsigned i = 0; i < lemmas.size(); ++i) {
            expr* lemma_i = lemmas[i].get();
            if (add_property1(lemma_i, lvl)) {
                IF_VERBOSE(2, verbose_stream() << lvl << " " << mk_pp(lemma_i, m) << "\n";);
                for (unsigned j = 0; j < m_use.size(); ++j) {
                    m_use[j]->add_child_property(*this, lemma_i, next_level(lvl));
                }
            }
        }
    }

    expr_ref pred_transformer::get_cover_delta(func_decl* p_orig, int level) {
        expr_ref result(m.mk_true(), m), v(m), c(m);
        if (level == -1) {
            result = pm.mk_and(m_invariants);                       
        }
        else if ((unsigned)level < m_levels.size()) {
            result = pm.mk_and(m_levels[level]);
        }
        // replace local constants by bound variables.
        expr_substitution sub(m);        
        for (unsigned i = 0; i < m_sig.size(); ++i) {
            c = m.mk_const(pm.o2n(sig(i), 0));
            v = m.mk_var(i, sig(i)->get_range());
            sub.insert(c, v);
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);
        (*rep)(result);

        // adjust result according to model converter.
        unsigned arity = m_head->get_arity();
        model_ref md = alloc(model, m);
        if (arity == 0) {
            md->register_decl(m_head, result);
        }
        else {
            func_interp* fi = alloc(func_interp, m, arity);
            fi->set_else(result);
            md->register_decl(m_head, fi);
        }
        model_converter_ref mc = ctx.get_model_converter();
        apply(mc, md, 0);
        if (p_orig->get_arity() == 0) {
            result = md->get_const_interp(p_orig);
        }
        else {
            result = md->get_func_interp(p_orig)->get_interp();
        }
        return result;        
    }

    void pred_transformer::add_cover(unsigned level, expr* property) {
        // replace bound variables by local constants.
        expr_ref result(property, m), v(m), c(m);
        expr_substitution sub(m);        
        for (unsigned i = 0; i < m_sig.size(); ++i) {
            c = m.mk_const(pm.o2n(sig(i), 0));
            v = m.mk_var(i, sig(i)->get_range());
            sub.insert(v, c);
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m);
        rep->set_substitution(&sub);
        (*rep)(result);
        TRACE("pdr", tout << "cover:\n" << mk_pp(result, m) << "\n";);
        // add the property.
        add_property(result, level);        
    }

    lbool pred_transformer::is_reachable(model_node& n, expr_ref_vector* core) {
        TRACE("pdr", 
              tout << "is-reachable: " << head()->get_name() << " level: " << n.level() << "\n";
              tout << mk_pp(n.state(), m) << "\n";);
        ensure_level(n.level());        
        model_ref model;
        prop_solver::scoped_level _sl(m_solver, n.level());
        m_solver.set_core(core);
        m_solver.set_model(&model);
        lbool is_sat = m_solver.check_conjunction_as_assumptions(n.state());
        if (is_sat == l_true && core) {            
            core->reset();
            TRACE("pdr", tout << "updating model\n"; 
                  model_smt2_pp(tout, m, *model, 0);
                  tout << mk_pp(n.state(), m) << "\n";);
            n.set_model(model);
        }
        return is_sat;
    }

    bool pred_transformer::is_invariant(unsigned level, expr* states, bool inductive, bool& assumes_level, expr_ref_vector* core) {
        expr_ref_vector conj(m);
        expr_ref tmp(m);
        
        conj.push_back(m.mk_not(states));

        if (inductive) {
            mk_assumptions(head(), states, conj);
        }
        tmp = pm.mk_and(conj);
        prop_solver::scoped_level _sl(m_solver, level);
        m_solver.set_core(core);
        lbool r = m_solver.check_conjunction_as_assumptions(tmp);
        if (r == l_false) {
            assumes_level = m_solver.assumes_level();
        }
        return r == l_false;
    }

    bool pred_transformer::check_inductive(unsigned level, expr_ref_vector& lits, bool& assumes_level) {
        manager& pm = get_pdr_manager();
        expr_ref_vector conj(m), core(m);
        expr_ref fml(m), states(m);
        states = m.mk_not(pm.mk_and(lits));
        mk_assumptions(head(), states, conj);
        fml = pm.mk_and(conj);
        prop_solver::scoped_level _sl(m_solver, level);
        m_solver.set_core(&core);
        m_solver.set_subset_based_core(true);
        lbool res = m_solver.check_assumptions_and_formula(lits, fml);
        if (res == l_false) {
            lits.reset();
            lits.append(core);
            assumes_level = m_solver.assumes_level();
        }
        return res == l_false;
    }

    void pred_transformer::mk_assumptions(func_decl* head, expr* fml, expr_ref_vector& result) {
        expr_ref tmp1(m), tmp2(m);
        obj_map<expr, datalog::rule const*>::iterator it = m_tag2rule.begin(), end = m_tag2rule.end();
        for (; it != end; ++it) {
            expr* pred = it->m_key;
            datalog::rule const* r = it->m_value;
            if (!r) continue;
            find_predecessors(*r, m_predicates);
            for (unsigned i = 0; i < m_predicates.size(); i++) {
                func_decl* d = m_predicates[i];
                if (d == head) {
                    tmp1 = m.mk_implies(pred, fml);
                    pm.formula_n2o(tmp1, tmp2, i);
                    result.push_back(tmp2);
                }
            }                  
        }
    }

    void pred_transformer::initialize(decl2rel const& pts) {
        m_initial_state = m.mk_false();
        m_transition = m.mk_true();        
        init_rules(pts, m_initial_state, m_transition);
        th_rewriter rw(m);
        rw(m_transition);
        rw(m_initial_state);
        
        m_solver.add_formula(m_transition);
        m_solver.add_level_formula(m_initial_state, 0);
        TRACE("pdr", 
              tout << "Initial state: " << mk_pp(m_initial_state, m) << "\n";
              tout << "Transition:    " << mk_pp(m_transition,  m) << "\n";);
        SASSERT(is_app(m_initial_state));
        m_reachable.add_init(to_app(m_initial_state));
    }

    void pred_transformer::init_rules(decl2rel const& pts, expr_ref& init, expr_ref& transition) {
        expr_ref_vector transitions(m);
        ptr_vector<datalog::rule const> tr_rules;
        datalog::rule const* rule;
        expr_ref_vector disj(m);
        app_ref pred(m);
        for (unsigned i = 0; i < rules().size(); ++i) {
            init_rule(pts, *rules()[i], init, tr_rules, transitions);
        }
        switch(transitions.size()) {
        case 0:
            transition = m.mk_false(); 
            break;
        case 1:
            // create a dummy tag.
            pred = m.mk_fresh_const(head()->get_name().str().c_str(), m.mk_bool_sort());
            rule = tr_rules[0];
            m_tag2rule.insert(pred, rule);
            m_rule2tag.insert(rule, pred.get());            
            transitions.push_back(pred);
            transition = pm.mk_and(transitions);
            break;
        default:
            for (unsigned i = 0; i < transitions.size(); ++i) {
                pred = m.mk_fresh_const(head()->get_name().str().c_str(), m.mk_bool_sort());
                rule = tr_rules[i];
                m_tag2rule.insert(pred, rule);                   
                m_rule2tag.insert(rule, pred);                
                disj.push_back(pred);
                transitions[i] = m.mk_implies(pred, transitions[i].get());
            }
            transitions.push_back(m.mk_or(disj.size(), disj.c_ptr()));
            transition = pm.mk_and(transitions);
            break;                 
        }
    }

    void pred_transformer::init_rule(
        decl2rel const&      pts,
        datalog::rule const& rule, 
        expr_ref&            init, 
        ptr_vector<datalog::rule const>& rules,
        expr_ref_vector&     transitions) 
    {
        // Predicates that are variable representatives. Other predicates at 
        // positions the variables occur are made equivalent with these.
        expr_ref_vector conj(m);
        app_ref_vector& var_reprs = *(alloc(app_ref_vector, m));
        qinst* qi = 0;
        ptr_vector<app> aux_vars;
                
        unsigned ut_size = rule.get_uninterpreted_tail_size();
        unsigned t_size  = rule.get_tail_size();   
        SASSERT(ut_size <= t_size);
        init_atom(pts, rule.get_head(), var_reprs, conj, UINT_MAX);
        for (unsigned i = 0; i < ut_size; ++i) {
            if (rule.is_neg_tail(i)) {
                throw default_exception("PDR does not support negated predicates in rule tails");
            }
            init_atom(pts, rule.get_tail(i), var_reprs, conj, i);
        }                  
        for (unsigned i = ut_size; i < t_size; ++i) {
            ground_free_vars(rule.get_tail(i), var_reprs, aux_vars);
        }
        SASSERT(check_filled(var_reprs));
        expr_ref_vector tail(m);
        for (unsigned i = ut_size; i < t_size; ++i) {
            tail.push_back(rule.get_tail(i));
        }        
        datalog::flatten_and(tail);
        for (unsigned i = 0; i < tail.size(); ++i) {
            expr_ref tmp(m);
            var_subst(m, false)(tail[i].get(), var_reprs.size(), (expr*const*)var_reprs.c_ptr(), tmp);
            quantifier* q;
            if (datalog::rule_manager::is_forall(m, tmp, q)) {

                if (!qi) {
                    qi = alloc(qinst, m);                                      
                }
                //
                // The contract is to instantiate q with 
                // sufficient witnesses to validate body.
                //
                qi->quantifiers.push_back(q);
                tmp = m.mk_true();
            }
            conj.push_back(tmp);
            TRACE("pdr", tout << mk_pp(tail[i].get(), m) << "\n" << mk_pp(tmp, m) << "\n";);
            SASSERT(is_ground(tmp));
        }         
        expr_ref fml = pm.mk_and(conj);
        th_rewriter rw(m);
        rw(fml);
        if (ctx.is_dl()) {
            hoist_non_bool_if(fml);
        }
        TRACE("pdr", tout << mk_pp(fml, m) << "\n";);
        SASSERT(is_ground(fml));
        if (m.is_false(fml)) {
            dealloc(qi);
            qi = 0;
            // no-op.
        }
        else {
            if (ut_size == 0 && !qi) {
                init = m.mk_or(init, fml);
            }
            transitions.push_back(fml);            
            m.inc_ref(fml);
            m_rule2transition.insert(&rule, fml.get());
            rules.push_back(&rule);
        }
        if (qi) {
            m_rule2qinst.insert(&rule, qi);            
        }
        m_rule2inst.insert(&rule,&var_reprs);
        m_rule2vars.insert(&rule, aux_vars);
    }

    bool pred_transformer::check_filled(app_ref_vector const& v) const {
        for (unsigned i = 0; i < v.size(); ++i) {
            if (!v[i]) return false;
        }
        return true;
    }

    // create constants for free variables in tail.
    void pred_transformer::ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars) {
        ptr_vector<sort> sorts;
        get_free_vars(e, sorts);
        while (vars.size() < sorts.size()) {
            vars.push_back(0);
        }
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (sorts[i] && !vars[i].get()) {
                vars[i] = m.mk_fresh_const("aux", sorts[i]);
                aux_vars.push_back(vars[i].get());
            }
        }
    }

    // create names for variables used in relations.
    void pred_transformer::init_atom(
        decl2rel const& pts, 
        app * atom, 
        app_ref_vector& var_reprs, 
        expr_ref_vector& conj, 
        unsigned tail_idx
        )
    {
        unsigned arity = atom->get_num_args();
        func_decl* head = atom->get_decl();
        pred_transformer& pt = *pts.find(head);
        for (unsigned i = 0; i < arity; i++) {
            app_ref rep(m);
            
            if (tail_idx == UINT_MAX) {
                rep = m.mk_const(pm.o2n(pt.sig(i), 0));
            }
            else {
                rep = m.mk_const(pm.o2o(pt.sig(i), 0, tail_idx));
            }            
                       
            expr * arg = atom->get_arg(i);
            if (is_var(arg)) {
                var * v = to_var(arg);
                unsigned var_idx = v->get_idx();
                if (var_idx >= var_reprs.size()) {
                    var_reprs.resize(var_idx+1);
                }
                expr * repr = var_reprs[var_idx].get();
                if (repr) {
                    conj.push_back(m.mk_eq(rep, repr));
                }
                else {
                    var_reprs[var_idx] = rep;
                }
            }
            else {
                SASSERT(is_app(arg));
                conj.push_back(m.mk_eq(rep, arg));
            }
        }
    }

    void pred_transformer::add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r) {
        r.push_back(pm.get_background());
        r.push_back((lvl == 0)?initial_state():transition());
        for (unsigned i = 0; i < rules().size(); ++i) {
            add_premises(pts, lvl, *rules()[i], r);
        }
    }

    void pred_transformer::close(expr* e) {
        m_reachable.add_reachable(e);
    }

    void pred_transformer::add_premises(decl2rel const& pts, unsigned lvl, datalog::rule& rule, expr_ref_vector& r) {        
        find_predecessors(rule, m_predicates);
        for (unsigned i = 0; i < m_predicates.size(); ++i) {
            expr_ref tmp(m);
            func_decl* head = m_predicates[i];
            pred_transformer& pt = *pts.find(head);
            expr_ref inv = pt.get_formulas(lvl, false);     
            if (!m.is_true(inv)) {
                pm.formula_n2o(inv, tmp, i, true);
                r.push_back(tmp);
            }
        }
    }

    void pred_transformer::inherit_properties(pred_transformer& other) {
        SASSERT(m_head == other.m_head);
        obj_map<expr, unsigned>::iterator it  = other.m_prop2level.begin();
        obj_map<expr, unsigned>::iterator end = other.m_prop2level.end();
        
        for (; it != end; ++it) {
            add_property(it->m_key, it->m_value);
        }
        for (unsigned i = 0; i < other.m_invariants.size(); ++i) {
            expr* e = other.m_invariants[i].get();
            m_invariants.push_back(e);
            m_solver.add_formula(e);
        }        
    }

    // ----------------
    // model_node

    void model_node::set_closed() {
        pt().close(state());
        m_closed = true; 
    }

    expr_ref model_node::get_trace() const {
        pred_transformer& p = pt();
        ast_manager& m = p.get_manager();
        manager& pm = p.get_pdr_manager();
        TRACE("pdr", model_v2_pp(tout, get_model()););
        func_decl* f = p.head();
        unsigned arity = f->get_arity();
        expr_ref_vector args(m);
        func_decl_ref v(m);
        for (unsigned i = 0; i < arity; ++i) {
            v = pm.o2n(p.sig(i),0);  
            expr* e = get_model().get_const_interp(v);
            if (e) {
                args.push_back(e);
            }
            else {
                args.push_back(m.mk_const(v));
            }
        }            
        return expr_ref(m.mk_app(f, args.size(), args.c_ptr()), m);
    }


    void model_node::mk_instantiate(datalog::rule_ref& r0, datalog::rule_ref& r1, expr_ref_vector& binding) {
        ast_manager& m = pt().get_manager();
        expr_ref_vector conjs(m);
        obj_map<expr,expr*> model;
        datalog::flatten_and(state(), conjs);
        for (unsigned i = 0; i < conjs.size(); ++i) {
            expr* e = conjs[i].get(), *e1, *e2;
            if (m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) {
                if (m.is_value(e2)) {
                    model.insert(e1, e2);
                }
                else if (m.is_value(e1)) {
                    model.insert(e2, e1);
                }
            }
            else if (m.is_not(e, e1)) {
                model.insert(e1, m.mk_false());
            }
            else {
                model.insert(e, m.mk_true());
            }
        }
        r0 = const_cast<datalog::rule*>(&pt().find_rule(*m_model.get()));
        app_ref_vector& inst = pt().get_inst(r0);
        TRACE("pdr", tout << mk_pp(state(), m) << " instance: " << inst.size() << "\n";);
        for (unsigned i = 0; i < inst.size(); ++i) {
            expr* v;
            if (model.find(inst[i].get(), v)) {
                binding.push_back(v);
            }            
            else {
                binding.push_back(m.mk_var(i, m.get_sort(inst[i].get())));
            }            
        }
        r1 = r0;
        if (!inst.empty()) {
            r1.get_manager().substitute(r1, binding.size(), binding.c_ptr());
        }
    }



    std::ostream& model_node::display(std::ostream& out, unsigned indent) {
        for (unsigned i = 0; i < indent; ++i) out << " ";
        out << m_level << " " << m_pt.head()->get_name() << " " << (m_closed?"closed":"open") << "\n";
        for (unsigned i = 0; i < indent; ++i) out << " ";
        out << "  " << mk_pp(m_state, m_state.get_manager(), indent) << "\n";
        for (unsigned i = 0; i < children().size(); ++i) {
            children()[i]->display(out, indent + 1);
        }
        return out;
    }

    unsigned model_node::index() const {
        model_node* p = parent();
        if (!p) return 0;
        for (unsigned i = 0; i < p->children().size(); ++i) {
            if (this == p->children()[i]) return i;
        }
        UNREACHABLE();
        return 0;
    }


    // ----------------
    // model_search

    model_node* model_search::next() {
        if (m_leaves.empty()) {
            return 0;
        }
        model_node* result = m_leaves.back();
        m_leaves.pop_back();
        return result;
    }

    bool model_search::is_repeated(model_node& n) const {
        model_node* p = n.parent();
        while (p) {
            if (p->state() == n.state()) {
                return true;
            }
            p = p->parent();
        }
        return false;
    }

    void model_search::add_leaf(model_node& n) {
        unsigned& count = cache(n).insert_if_not_there2(n.state(), 0)->get_data().m_value;
        ++count;
        if (count == 1 || is_repeated(n)) {
            set_leaf(n);
        }
        else {
            n.set_pre_closed();
        }
    }

    void model_search::set_leaf(model_node& n) {
        erase_children(n);
        SASSERT(n.is_open());      
        enqueue_leaf(n);
    }

    void model_search::enqueue_leaf(model_node& n) {
        if (m_bfs) {
            m_leaves.push_front(&n);
        }
        else {
            m_leaves.push_back(&n);
        }
    }

    void model_search::set_root(model_node* root) {
        reset();
        m_root = root;
        SASSERT(cache(*root).empty());        
        cache(*root).insert(root->state(), 1);
        set_leaf(*root);
    }

    obj_map<expr, unsigned>& model_search::cache(model_node const& n) {
        unsigned l = n.orig_level();
        if (l >= m_cache.size()) {
            m_cache.resize(l + 1);
        }
        return m_cache[l];
    }

    void model_search::erase_children(model_node& n) {
        ptr_vector<model_node> todo, nodes;
        todo.append(n.children());
        erase_leaf(n);
        n.reset();
        while (!todo.empty()) {
            model_node* m = todo.back();
            todo.pop_back();
            nodes.push_back(m);
            todo.append(m->children());
            erase_leaf(*m);
            remove_node(*m);
        }
        std::for_each(nodes.begin(), nodes.end(), delete_proc<model_node>());
    }

    void model_search::remove_node(model_node& n) {
        if (0 == --cache(n).find(n.state())) {
            cache(n).remove(n.state());
        }
    }

    void model_search::erase_leaf(model_node& n) {
        if (n.children().empty() && n.is_open()) {
            std::deque<model_node*>::iterator 
                it  = m_leaves.begin(), 
                end = m_leaves.end();
            for (; it != end; ++it) {
                if (*it == &n) {
                    m_leaves.erase(it);
                    break;
                }
            }
        }
    }

    std::ostream& model_search::display(std::ostream& out) const {
        if (m_root) {
            m_root->display(out, 0);
        }
        out << "goals\n";
        std::deque<model_node*>::const_iterator 
            it  = m_leaves.begin(), 
            end = m_leaves.end();
        for (; it != end; ++it) {
            (*it)->display(out, 1);
        }
        return out;
    }

    expr_ref model_search::get_trace() const {       
        pred_transformer& pt = get_root().pt();
        ast_manager& m = pt.get_manager();
        manager& pm = pt.get_pdr_manager();
        expr_ref result(m.mk_true(),m);
        expr_ref_vector rules(m);
        ptr_vector<model_node> nodes;
        nodes.push_back(m_root);
        while (!nodes.empty()) {
            model_node* current = nodes.back();
            nodes.pop_back();
            rules.push_back(current->get_trace());
            nodes.append(current->children());
        }
        return pm.mk_and(rules);
    }

    proof_ref model_search::get_proof_trace(context const& ctx) const {
        pred_transformer& pt = get_root().pt();
        ast_manager& m = pt.get_manager();
        datalog::context& dctx = ctx.get_context();
        datalog::rule_manager& rm = dctx.get_rule_manager();
        datalog::rule_unifier unifier(dctx);
        datalog::dl_decl_util util(m);
        datalog::rule_ref r0(rm), r1(rm);
        obj_map<expr, proof*> cache;
        obj_map<expr, datalog::rule*>  rules;
        ptr_vector<model_node> todo;
        proof_ref_vector trail(m);
        datalog::rule_ref_vector rules_trail(rm);
        proof* pr = 0;
        todo.push_back(m_root);
        while (!todo.empty()) {
            model_node* n = todo.back();
            if (cache.find(n->state(), pr)) {
                todo.pop_back();
                continue;
            }
            ptr_vector<proof> pfs;
            ptr_vector<datalog::rule> rls;
            ptr_vector<model_node> const& chs = n->children();
            pfs.push_back(0);
            rls.push_back(0);
            for (unsigned i = 0; i < chs.size(); ++i) {
                if (cache.find(chs[i]->state(), pr)) {
                    pfs.push_back(pr);
                    rls.push_back(rules.find(chs[i]->state()));
                }
                else {
                    todo.push_back(chs[i]);
                }
            }            
            if (pfs.size() != 1 + chs.size()) {
                continue;
            }
            proof_ref rl(m);
            expr_ref  fml0(m);
            expr_ref_vector binding(m);
            n->mk_instantiate(r0, r1, binding);
            r0->to_formula(fml0);
            proof_ref p1(m), p2(m);
            p1 = m.mk_asserted(fml0);
            pfs[0] = p1;
            rls[0] = r1;
            TRACE("pdr",
                  tout << "root: " << mk_pp(p1.get(), m) << "\n";
                  for (unsigned i = 0; i < binding.size(); ++i) {
                      tout << mk_pp(binding[i].get(), m) << "\n";
                  }
                  for (unsigned i = 1; i < pfs.size(); ++i) {
                      tout << mk_pp(pfs[i], m) << "\n";
                  }
                  );
            datalog::rule_ref reduced_rule(rm), r3(rm);            
            reduced_rule = rls[0];
            // check if binding is identity.
            bool binding_is_id = true;
            for (unsigned i = 0; binding_is_id && i < binding.size(); ++i) {
                expr* v = binding[i].get();
                binding_is_id = is_var(v) && to_var(v)->get_idx() == i;
            }
            if (rls.size() > 1 || !binding_is_id) {
                vector<expr_ref_vector> substs;
                svector<std::pair<unsigned,unsigned> > positions;
                substs.push_back(binding); // TODO base substitution.
                for (unsigned i = 1; i < rls.size(); ++i) {
                    datalog::rule& src = *rls[i];
                    bool unified = unifier.unify_rules(*reduced_rule, 0, src);
                    if (!unified) {
                        std::cout << "Could not unify rules: ";
                        reduced_rule->display(dctx, std::cout);
                        src.display(dctx, std::cout);
                    }
                    expr_ref_vector sub1 = unifier.get_rule_subst(*reduced_rule, true);
                    TRACE("pdr",
                          for (unsigned k = 0; k < sub1.size(); ++k) {
                              tout << mk_pp(sub1[k].get(), m) << " ";
                          }
                          tout << "\n";
                          );
                    for (unsigned j = 0; j < substs.size(); ++j) {
                        // TODO. apply sub1 to subst.
                    }

                    positions.push_back(std::make_pair(i,0));
                    substs.push_back(unifier.get_rule_subst(src, false));
                    VERIFY(unifier.apply(*reduced_rule.get(), 0, src, r3));
                    reduced_rule = r3;
                }
                expr_ref fml_concl(m);
                reduced_rule->to_formula(fml_concl);                    
                p1 = m.mk_hyper_resolve(pfs.size(), pfs.c_ptr(), fml_concl, positions, substs);
            }
            cache.insert(n->state(), p1);
            rules.insert(n->state(), reduced_rule);
            trail.push_back(p1);
            rules_trail.push_back(reduced_rule);
            todo.pop_back();
        }
        return proof_ref(cache.find(m_root->state()), m);
    }

    model_search::~model_search() {
        TRACE("pdr", tout << "\n";);
        reset();
    }

    void model_search::reset() {
        if (m_root) {
            erase_children(*m_root);
            remove_node(*m_root);
            dealloc(m_root);
            m_root = 0;
        }
    }

    void model_search::backtrack_level(bool uses_level, model_node& n) {
        SASSERT(m_root);
        if (uses_level && m_root->level() > n.level()) {
            IF_VERBOSE(2, verbose_stream() << "Increase level " << n.level() << "\n";);
            n.increase_level();
            enqueue_leaf(n);
        }
        else {
            model_node* p = n.parent();
            if (p) {
                set_leaf(*p);
            }               
        }     
    }

    // ----------------
    // context

    context::context(
        front_end_params&     fparams,
        params_ref const&     params,
        ast_manager&          m
        )
        : m_fparams(fparams),
          m_params(params),
          m(m),
          m_context(0),
          m_quantifier_inst(*this, m),
          m_pm(m_fparams, m_params, m),
          m_query_pred(m),
          m_query(0),
          m_search(m_params.get_bool(":bfs-model-search", true)),
          m_last_result(l_undef),
          m_inductive_lvl(0),
          m_cancel(false)
    {
    }

    context::~context() {
        reset_core_generalizers();
        reset();
    }

    void context::reset() {
        TRACE("pdr", tout << "\n";);
        cleanup();
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_rels.reset();
        m_search.reset();
        m_query = 0;       
        m_last_result = l_undef;
        m_inductive_lvl = 0;        
    }

    void context::init_rules(datalog::rule_set& rules, decl2rel& rels) {
        m_context = &rules.get_context();
        // Allocate collection of predicate transformers
        datalog::rule_set::decl2rules::iterator dit = rules.begin_grouped_rules(), dend = rules.end_grouped_rules();
        decl2rel::obj_map_entry* e;
        for (; dit != dend; ++dit) {            
            func_decl* pred = dit->m_key;
            TRACE("pdr", tout << mk_pp(pred, m) << "\n";);
            SASSERT(!rels.contains(pred));
            e = rels.insert_if_not_there2(pred, alloc(pred_transformer, *this, get_pdr_manager(), pred));            
            datalog::rule_vector const& pred_rules = *dit->m_value;            
            for (unsigned i = 0; i < pred_rules.size(); ++i) {
                e->get_data().m_value->add_rule(pred_rules[i]);
            }
        }
        // Initialize use list dependencies
        decl2rel::iterator it = rels.begin(), end = rels.end();        
        for (; it != end; ++it) {
            func_decl* pred = it->m_key;      
            pred_transformer* pt = it->m_value, *pt_user;
            obj_hashtable<func_decl> const& deps = rules.get_dependencies().get_deps(pred);
            obj_hashtable<func_decl>::iterator itf = deps.begin(), endf = deps.end();
            for (; itf != endf; ++itf) {
                TRACE("pdr", tout << mk_pp(pred, m) << " " << mk_pp(*itf, m) << "\n";);
                if (!rels.find(*itf, pt_user)) {
                    pt_user = alloc(pred_transformer, *this, get_pdr_manager(), *itf);
                    rels.insert(*itf, pt_user);
                }
                pt_user->add_use(pt);                
            }
        }      

        // Initialize the predicate transformers.
        it = rels.begin(), end = rels.end();        
        for (; it != end; ++it) {            
            pred_transformer& rel = *it->m_value;
            rel.initialize(rels);
            TRACE("pdr", rel.display(tout); );
        }
    }

    void context::update_rules(datalog::rule_set& rules) {
        decl2rel rels;
        init_core_generalizers(rules);
        init_rules(rules, rels); 
        decl2rel::iterator it = rels.begin(), end = rels.end();
        for (; it != end; ++it) {
            pred_transformer* pt = 0;
            if (m_rels.find(it->m_key, pt)) {
                it->m_value->inherit_properties(*pt);
            }
        }
        reset();
        it = rels.begin(), end = rels.end();
        for (; it != end; ++it) {
            m_rels.insert(it->m_key, it->m_value);
        }
    }

    unsigned context::get_num_levels(func_decl* p) {
        pred_transformer* pt = 0;
        if (m_rels.find(p, pt)) {
            return pt->get_num_levels();
        }
        else {
            IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
            return 0;
        }
    }

    expr_ref context::get_cover_delta(int level, func_decl* p_orig, func_decl* p) {
        pred_transformer* pt = 0;
        if (m_rels.find(p, pt)) {
            return pt->get_cover_delta(p_orig, level);
        }
        else {
            IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
            return expr_ref(m.mk_true(), m);
        }
    }

    void context::add_cover(int level, func_decl* p, expr* property) {
        pred_transformer* pt = 0;
        if (!m_rels.find(p, pt)) {
            pt = alloc(pred_transformer, *this, get_pdr_manager(), p);
            m_rels.insert(p, pt);
            IF_VERBOSE(10, verbose_stream() << "did not find predicate " << p->get_name() << "\n";);
        }
        unsigned lvl = (level == -1)?infty_level:((unsigned)level);
        pt->add_cover(lvl, property);
    }

    class context::classifier_proc {
        ast_manager& m;
        arith_util a;
        bool m_is_bool;
        bool m_is_bool_arith;
        bool m_has_arith;
        bool m_is_dl;
    public:
        classifier_proc(ast_manager& m, datalog::rule_set& rules):
            m(m), a(m), m_is_bool(true), m_is_bool_arith(true), m_has_arith(false), m_is_dl(false) {
            classify(rules);
        }
        void operator()(expr* e) {
            if (m_is_bool) {                
                if (!m.is_bool(e)) {
                    m_is_bool = false;
                }
                else if (is_var(e)) {
                    // no-op.
                }
                else if (!is_app(e)) {
                    m_is_bool = false;
                }
                else if (to_app(e)->get_num_args() > 0 &&
                         to_app(e)->get_family_id() != m.get_basic_family_id()) {
                    m_is_bool = false;
                }
            }

            m_has_arith = m_has_arith || a.is_int_real(e);

            if (m_is_bool_arith) {                
                if (!m.is_bool(e) && !a.is_int_real(e)) {
                    m_is_bool_arith = false;
                }
                else if (is_var(e)) {
                    // no-op
                }
                else if (!is_app(e)) {
                    m_is_bool_arith = false;
                }
                else if (to_app(e)->get_num_args() > 0 &&
                         to_app(e)->get_family_id() != m.get_basic_family_id() &&
                         to_app(e)->get_family_id() != a.get_family_id()) {
                    m_is_bool_arith = false;
                }
            }
        }

        bool is_bool() const { return m_is_bool; }

        bool is_bool_arith() const { return m_is_bool_arith; }

        bool is_dl() const { return m_is_dl; }


    private:

        void classify(datalog::rule_set& rules) {
            expr_fast_mark1 mark;
            datalog::rule_set::iterator it = rules.begin(), end = rules.end();        
            for (; it != end; ++it) {      
                datalog::rule& r = *(*it);
                classify_pred(mark, r.get_head());
                unsigned utsz = r.get_uninterpreted_tail_size();
                for (unsigned i = 0; i < utsz; ++i) {
                    classify_pred(mark, r.get_tail(i));                
                }
                for (unsigned i = utsz; i < r.get_tail_size(); ++i) {
                    quick_for_each_expr(*this, mark, r.get_tail(i));                    
                }
            }
            mark.reset();
 
            m_is_dl = false;
            if (m_has_arith) {
                ptr_vector<expr> forms;
                for (it = rules.begin(); it != end; ++it) {  
                    datalog::rule& r = *(*it);
                    unsigned utsz = r.get_uninterpreted_tail_size();
                    forms.push_back(r.get_head());
                    for (unsigned i = utsz; i < r.get_tail_size(); ++i) {
                        forms.push_back(r.get_tail(i));
                    }         
                }
                m_is_dl = is_difference_logic(m, forms.size(), forms.c_ptr());
            }
        }

        void classify_pred(expr_fast_mark1& mark, app* pred) {
            for (unsigned i = 0; i < pred->get_num_args(); ++i) {
                quick_for_each_expr(*this, mark, pred->get_arg(i));
            }
        }
    };

    void context::validate() {
        if (!m_params.get_bool(":validate-result", false)) {
            return;
        }
        switch(m_last_result) {
        case l_true: {
            proof_ref pr = get_proof();
            proof_checker checker(m);
            expr_ref_vector side_conditions(m);
            bool ok = checker.check(pr, side_conditions);
            if (!ok) {
                IF_VERBOSE(0, verbose_stream() << "proof validation failed\n";);
            }
            break;
        }            
        case l_false: {
            expr_ref_vector refs(m);
            model_ref model;
            vector<relation_info> rs;
            get_level_property(m_inductive_lvl, refs, rs);    
            inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
            ex.to_model(model);
            decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
            var_subst vs(m, false);
            for (; it != end; ++it) {
                ptr_vector<datalog::rule> const& rules = it->m_value->rules();
                for (unsigned i = 0; i < rules.size(); ++i) {
                    // datalog::rule* rule = rules[i];
                    // vs(rule->get_head(), 
                    // apply interpretation of predicates to rule.
                    // create formula and check for unsat.
                }
            }
            break;
        }
        default:
            break;
        }
    }

    void context::reset_core_generalizers() {
        std::for_each(m_core_generalizers.begin(), m_core_generalizers.end(), delete_proc<core_generalizer>());
        m_core_generalizers.reset();
    }

    void context::init_core_generalizers(datalog::rule_set& rules) {
        reset_core_generalizers();
        classifier_proc classify(m, rules);
        bool use_mc = m_params.get_bool(":use-multicore-generalizer", false);
        if (use_mc) {
            m_core_generalizers.push_back(alloc(core_multi_generalizer, *this, 0));
        }
        if (m_params.get_bool(":use-farkas", true) && !classify.is_bool()) {
            if (m_params.get_bool(":inline-proof-mode", true)) {
                m.toggle_proof_mode(PGM_FINE);
                m_fparams.m_proof_mode = PGM_FINE;                
                m_fparams.m_arith_bound_prop = BP_NONE;
                m_fparams.m_arith_auto_config_simplex = true;
                m_fparams.m_arith_propagate_eqs = false;
                m_fparams.m_arith_eager_eq_axioms = false;
                if (classify.is_dl()) {
                    m_fparams.m_arith_mode = AS_DIFF_LOGIC;
                    m_fparams.m_arith_expand_eqs = true;
                }
            }
            else {
                m_core_generalizers.push_back(alloc(core_farkas_generalizer, *this, m, m_fparams));
            }
        }
        if (!use_mc && m_params.get_bool(":use-inductive-generalizer", true)) {
            m_core_generalizers.push_back(alloc(core_bool_inductive_generalizer, *this, 0));
        }
        if (m_params.get_bool(":use-interpolants", false)) {
            m_core_generalizers.push_back(alloc(core_interpolant_generalizer, *this));
        }
        if (m_params.get_bool(":inductive-reachability-check", false)) {
            m_core_generalizers.push_back(alloc(core_induction_generalizer, *this));
        }
    }

    void context::get_level_property(unsigned lvl, expr_ref_vector& res, vector<relation_info>& rs) const {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            pred_transformer* r = it->m_value;
            if (r->head() == m_query_pred) {
                continue;
            }
            expr_ref conj = r->get_formulas(lvl, false);        
            m_pm.formula_n2o(0, false, conj);            
            res.push_back(conj);
            ptr_vector<func_decl> sig(r->head()->get_arity(), r->sig());
            rs.push_back(relation_info(m, r->head(), sig, conj));
        }
    }

    void context::simplify_formulas() {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            pred_transformer* r = it->m_value;
            r->simplify_formulas();
        }        
    }

    lbool context::solve() {
        m_last_result = l_undef;
        try {
            solve_impl();
            UNREACHABLE();
        }
        catch (model_exception) {        
            check_quantifiers();
            IF_VERBOSE(1, verbose_stream() << "\n"; m_search.display(verbose_stream()););  
            m_last_result = l_true;
            validate();
            return l_true;
        }
        catch (inductive_exception) {
            simplify_formulas();
            m_last_result = l_false;
            TRACE("pdr",  display_certificate(tout););      
            IF_VERBOSE(1, display_certificate(verbose_stream()););
            validate();
            return l_false;
        }
        catch (unknown_exception) {
            return l_undef;
        }
        return l_undef;
    }

    void context::cancel() {
        m_cancel = true;
    }

    void context::cleanup() {
        m_cancel = false;
    }

    void context::checkpoint() {
        if (m_cancel) {
            throw default_exception("pdr canceled");
        }
    }

    /**
       \brief retrieve answer.
    */
    expr_ref context::get_answer() {
        switch(m_last_result) {
        case l_true: return mk_sat_answer();
        case l_false: return mk_unsat_answer();
        default: return expr_ref(m.mk_true(), m);
        }
    }

    void context::get_model(model_ref& md) {
        SASSERT(m_last_result == l_false);        
        expr_ref_vector refs(m);
        vector<relation_info> rs;
        get_level_property(m_inductive_lvl, refs, rs);            
        inductive_property ex(m, m_mc, rs);
        ex.to_model(md);
    }
    
    proof_ref context::get_proof() const {
        datalog::scoped_coarse_proof _sc(m);
        proof_ref proof(m);
        SASSERT(m_last_result == l_true);
        proof = m_search.get_proof_trace(*this);
        TRACE("pdr", tout << "PDR trace: " << mk_pp(proof, m) << "\n";);
        apply(m, m_pc.get(), proof);
        return proof;
    }


    /**
        \brief Retrieve satisfying assignment with explanation.
    */
    expr_ref context::mk_sat_answer() const {
        if (m_params.get_bool(":generate-proof-trace", false)) {
            proof_ref pr = get_proof();
            return expr_ref(pr.get(), m);
        }
        return m_search.get_trace();
    }

    expr_ref context::mk_unsat_answer() const {
        expr_ref_vector refs(m);
        vector<relation_info> rs;
        get_level_property(m_inductive_lvl, refs, rs);            
        inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
        return ex.to_expr();
    }

    void context::solve_impl() {
        if (!m_rels.find(m_query_pred, m_query)) {
            throw inductive_exception();            
        }
        unsigned lvl = 0;
        bool reachable;
        while (true) {
            checkpoint();
            reachable = check_reachability(lvl);
            if (reachable) {
                throw model_exception();
            }
            if (lvl != 0) {
                propagate(lvl);
            }
            lvl++;
            m_stats.m_max_depth = std::max(m_stats.m_max_depth, lvl);
            IF_VERBOSE(1,verbose_stream() << "Entering level "<<lvl << "\n";);
        }
    }

    //
    // Check that quantifiers are satisfied in the produced model.
    // 
    void context::check_quantifiers() {
        if (has_quantifiers()) {
            m_quantifier_inst.model_check(m_search.get_root());
        }
    }

    bool context::has_quantifiers() const {
        decl2rel const& dr = get_pred_transformers();
        decl2rel::iterator it = dr.begin(), end = dr.end();
        for (; it != end; ++it) {
            pred_transformer* pt = it->m_value;
            if (pt->has_quantifiers()) return true;
        }
        return false;
    }

    //
    // Pick a potential counter example state.
    // Initialize a search tree using that counter-example.
    // If the counter-example expands to a full model, then
    // the search tree is a model, otherwise obtain the next
    // query state.
    //
    bool context::check_reachability(unsigned level) {
        expr_ref state(m.mk_true(), m);
        model_node* root = alloc(model_node, 0, state, *m_query, level);
        m_search.set_root(root);            
        
        while (model_node* node = m_search.next()) {
            IF_VERBOSE(2, verbose_stream() << "Expand node: " << node->level() << "\n";);
            checkpoint();
            expand_node(*node);   
        }
        return root->is_closed();
    }

    void context::close_node(model_node& n) {
        n.set_closed();
        model_node* p = n.parent();
        while (p && p->is_1closed()) {
            p->set_closed();
            p = p->parent();
        }
    }

    void context::check_pre_closed(model_node& n) {
        for (unsigned i = 0; i < n.children().size(); ++i) {
            if (!n.children()[i]->is_closed()) return;
        }
        n.set_pre_closed();
        model_node* p = n.parent();
        while (p && p->is_1closed()) {
            p->set_pre_closed();
            p = p->parent();
        }
    }

    void context::expand_node(model_node& n) {
        SASSERT(n.is_open());
        expr_ref_vector cube(m);

        if (n.pt().is_reachable(n.state())) {
            TRACE("pdr", tout << "reachable\n";);
            close_node(n);
        }
        else {
            switch (expand_state(n, cube)) {
            case l_true:
                if (n.level() == 0) {
                    TRACE("pdr", tout << "reachable\n";);
                    close_node(n);
                }
                else {
                    TRACE("pdr", tout << "node: " << &n << "\n";); 
                    create_children(n);
                }
                break;
            case l_false: {
                core_generalizer::cores cores;
                cores.push_back(std::make_pair(cube, true));
                
                for (unsigned i = 0; !cores.empty() && i < m_core_generalizers.size(); ++i) {
                    core_generalizer::cores new_cores;                    
                    for (unsigned j = 0; j < cores.size(); ++j) {
                        (*m_core_generalizers[i])(n, cores[j].first, cores[j].second, new_cores);
                    }
                    cores.reset();
                    cores.append(new_cores);
                }
                bool found_invariant = false;
                for (unsigned i = 0; i < cores.size(); ++i) {
                    expr_ref_vector const& core = cores[i].first;
                    bool uses_level = cores[i].second;
                    found_invariant = !uses_level || found_invariant;
                    expr_ref ncore(m_pm.mk_not_and(core), m);
                    TRACE("pdr", tout << "invariant state: " << (uses_level?"":"(inductive) ") <<  mk_pp(ncore, m) << "\n";);
                    n.pt().add_property(ncore, uses_level?n.level():infty_level);
                }
                CASSERT("pdr",n.level() == 0 || check_invariant(n.level()-1));
                m_search.backtrack_level(!found_invariant && m_params.get_bool(":flexible-trace", false), n);
                break;
            }
            case l_undef: {
                TRACE("pdr", tout << "unknown state: " << mk_pp(m_pm.mk_and(cube), m) << "\n";);
                throw unknown_exception();
            }
            }
        }
    }

    //
    // check if predicate transformer has a satisfiable predecessor state.
    // returns either a satisfiable predecessor state or 
    // return a property that blocks state and is implied by the 
    // predicate transformer (or some unfolding of it).
    // 
    lbool context::expand_state(model_node& n, expr_ref_vector& result) {
        return n.pt().is_reachable(n, &result);
    }

    void context::propagate(unsigned max_prop_lvl) {    
        if (m_params.get_bool(":simplify-formulas-pre", false)) {            
            simplify_formulas();
        }
        for (unsigned lvl = 0; lvl <= max_prop_lvl; lvl++) {
            checkpoint();
            bool all_propagated = true;
            decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
            for (; it != end; ++it) {
                checkpoint();            
                pred_transformer& r = *it->m_value;
                all_propagated = r.propagate_to_next_level(lvl) && all_propagated;
            }
            CASSERT("pdr", check_invariant(lvl));

            if (all_propagated && lvl == max_prop_lvl) {
                m_inductive_lvl = lvl;
                throw inductive_exception();
            }
        }
        if (m_params.get_bool(":simplify-formulas-post", false)) {            
            simplify_formulas();
        }
    }


    /**
       \brief create children states from model cube.

       Introduce the shorthands:

       - T(x0,x1,x)   for transition
       - phi(x)       for n.state()
       - M(x0,x1,x)   for n.model()

       Assumptions:
         M => phi & T

       In other words, 
       1. phi & T is implied by M
       
       Goal is to find phi0(x0), phi1(x1) such that:

         phi(x) & phi0(x0) & phi1(x1) => T(x0, x1, x)       

       Strategy: 

       - Extract literals from T & phi using ternary simulation with M.
       - resulting formula is Phi.

       - perform cheap existential quantifier elimination on 
         Phi <- exists x . Phi(x0,x1,x)
         (e.g., destructive equality resolution) 
   
       - Sub-strategy 1: rename  remaining x to fresh variables.
       - Sub-strategy 2: replace remaining x to M(x).

       - For each literal L in result:

         - if L is x0 pure, add L to L0
         - if L is x1 pure, add L to L1
         - if L mixes x0, x1, add x1 = M(x1) to L1, add L(x1 |-> M(x1)) to L0
         
       - Create sub-goals for L0 and L1.

    */
    void context::create_children(model_node& n) {        
        SASSERT(n.level() > 0);
        bool use_model_generalizer = m_params.get_bool(":use-model-generalizer", false);
        datalog::scoped_no_proof _sc(m);
 
        pred_transformer& pt = n.pt();
        model_ref M = n.get_model_ptr();
        datalog::rule const& r = pt.find_rule(*M);
        expr* T   = pt.get_transition(r);
        expr* phi = n.state();

        IF_VERBOSE(3, verbose_stream() << "Model:\n";
                   model_smt2_pp(verbose_stream(), m, *M, 0);
                   verbose_stream() << "\n";
                   verbose_stream() << "Transition:\n" << mk_pp(T, m) << "\n";
                   verbose_stream() << "Phi:\n" << mk_pp(phi, m) << "\n";);
                      
        model_evaluator mev(m);
        expr_ref_vector mdl(m), forms(m), Phi(m);
        forms.push_back(T);
        forms.push_back(phi);
        datalog::flatten_and(forms);        
        ptr_vector<expr> forms1(forms.size(), forms.c_ptr());
        if (use_model_generalizer) {
            Phi.append(mev.minimize_model(forms1, M));
        }
        else {
            Phi.append(mev.minimize_literals(forms1, M));
        }
        ptr_vector<func_decl> preds;
        pt.find_predecessors(r, preds);
        pt.remove_predecessors(Phi);

        app_ref_vector vars(m);
        unsigned sig_size = pt.head()->get_arity();
        for (unsigned i = 0; i < sig_size; ++i) {
            vars.push_back(m.mk_const(m_pm.o2n(pt.sig(i), 0)));
        }
        ptr_vector<app> aux_vars;
        pt.get_aux_vars(r, aux_vars);
        vars.append(aux_vars.size(), aux_vars.c_ptr());

        scoped_ptr<expr_replacer> rep;
        qe_lite qe(m);
        expr_ref phi1 = m_pm.mk_and(Phi);
        qe(vars, phi1);
        if (!use_model_generalizer) {
            reduce_disequalities(*M, 3, phi1);
        }
        get_context().get_rewriter()(phi1);

        IF_VERBOSE(2, 
                   verbose_stream() << "Vars:\n";
                   for (unsigned i = 0; i < vars.size(); ++i) {
                       verbose_stream() << mk_pp(vars[i].get(), m) << "\n";
                   }
                   verbose_stream() << "Literals\n";
                   verbose_stream() << mk_pp(m_pm.mk_and(Phi), m) << "\n";
                   verbose_stream() << "Reduced\n" << mk_pp(phi1, m) << "\n";);
        
        if (!vars.empty()) {
            // also fresh names for auxiliary variables in body?
            expr_substitution sub(m);
            expr_ref_vector refs(m);
            expr_ref tmp(m);
            proof_ref pr(m);
            pr = m.mk_asserted(m.mk_true());
            for (unsigned i = 0; i < vars.size(); ++i) {                
                VERIFY (M->eval(vars[i].get(), tmp, true));                
                refs.push_back(tmp);
                sub.insert(vars[i].get(), tmp, pr);
            }
            if (!rep) rep = mk_expr_simp_replacer(m);
            rep->set_substitution(&sub);
            (*rep)(phi1);
            IF_VERBOSE(2, verbose_stream() << "Projected:\n" << mk_pp(phi1, m) << "\n";);
        }
        Phi.reset();
        datalog::flatten_and(phi1, Phi);
        unsigned_vector indices;
        vector<expr_ref_vector> child_states;
        child_states.resize(preds.size(), expr_ref_vector(m));
        for (unsigned i = 0; i < Phi.size(); ++i) {            
            m_pm.collect_indices(Phi[i].get(), indices);    
            if (indices.size() == 0) {
                IF_VERBOSE(3, verbose_stream() << "Skipping " << mk_pp(Phi[i].get(), m) << "\n";);
            }
            else if (indices.size() == 1) {
                child_states[indices.back()].push_back(Phi[i].get());
            }
            else {
                expr_substitution sub(m);
                expr_ref tmp(m);
                proof_ref pr(m);
                pr = m.mk_asserted(m.mk_true());
                vector<ptr_vector<app> > vars;
                m_pm.collect_variables(Phi[i].get(), vars);
                SASSERT(vars.size() == indices.back()+1);
                for (unsigned j = 1; j < indices.size(); ++j) {
                    ptr_vector<app> const& vs = vars[indices[j]];
                    for (unsigned k = 0; k < vs.size(); ++k) {
                        M->eval(vs[k]->get_decl(), tmp);
                        sub.insert(vs[k], tmp, pr);
                        child_states[indices[j]].push_back(m.mk_eq(vs[k], tmp));
                    }
                }
                tmp = Phi[i].get();
                if (!rep) rep = mk_expr_simp_replacer(m);
                rep->set_substitution(&sub);
                (*rep)(tmp);
                child_states[indices[0]].push_back(tmp);
            }

        }
        
        expr_ref n_cube(m);
        for (unsigned i = 0; i < preds.size(); ++i) {            
            pred_transformer& pt = *m_rels.find(preds[i]);
            SASSERT(pt.head() == preds[i]);           
            expr_ref o_cube = m_pm.mk_and(child_states[i]);            
            m_pm.formula_o2n(o_cube, n_cube, i);
            model_node* child = alloc(model_node, &n, n_cube, pt, n.level()-1);
            ++m_stats.m_num_nodes;
            m_search.add_leaf(*child); 
            IF_VERBOSE(2, verbose_stream() << "Predecessor: " << mk_pp(o_cube, m) << "\n";);
            m_stats.m_max_depth = std::max(m_stats.m_max_depth, child->depth());
        }
        check_pre_closed(n);
        TRACE("pdr", m_search.display(tout););
    }

    void context::collect_statistics(statistics& st) const {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (it = m_rels.begin(); it != end; ++it) {
            it->m_value->collect_statistics(st);
        }
        st.update("PDR num unfoldings", m_stats.m_num_nodes);
        st.update("PDR max depth", m_stats.m_max_depth);
        m_pm.collect_statistics(st);

        for (unsigned i = 0; i < m_core_generalizers.size(); ++i) {
            m_core_generalizers[i]->collect_statistics(st);
        }
    }


    std::ostream& context::display(std::ostream& out) const {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();
        for (; it != end; ++it) {
            it->m_value->display(out);
        }        
        m_search.display(out);
        return out;
    }

    bool context::check_invariant(unsigned lvl) {
        decl2rel::iterator it = m_rels.begin(), end = m_rels.end();        
        for (; it != end; ++it) {
            checkpoint();
            if (!check_invariant(lvl, it->m_key)) {
                return false;
            }
        }
        return true;
    }

    bool context::check_invariant(unsigned lvl, func_decl* fn) {
        smt::kernel ctx(m, m_fparams);
        pred_transformer& pt = *m_rels.find(fn);
        expr_ref_vector conj(m);
        expr_ref inv = pt.get_formulas(next_level(lvl), false);
        if (m.is_true(inv)) return true;
        pt.add_premises(m_rels, lvl, conj);
        conj.push_back(m.mk_not(inv));
        expr_ref fml(m.mk_and(conj.size(), conj.c_ptr()), m);
        ctx.assert_expr(fml);
        lbool result = ctx.check();
        TRACE("pdr", tout << "Check invariant level: " << lvl << " " << result << "\n" << mk_pp(fml, m) << "\n";);
        return result == l_false;
    }

    void context::display_certificate(std::ostream& strm) const {
        switch(m_last_result) {
        case l_false: {
            expr_ref_vector refs(m);
            vector<relation_info> rs;
            get_level_property(m_inductive_lvl, refs, rs);    
            inductive_property ex(m, const_cast<model_converter_ref&>(m_mc), rs);
            strm << ex.to_string();
            break;
        }
        case l_true: {
            strm << mk_pp(mk_sat_answer(), m);
            break;
        }
        case l_undef: {
            strm << "unknown";
            break;
        }
        }
    }

}
