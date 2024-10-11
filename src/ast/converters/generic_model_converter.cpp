/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    generic_model_converter.cpp

Abstract:

    Generic model converter that hides and adds entries.
    It subsumes filter_model_converter and extension_model_converter.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-29

Notes:

--*/
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/for_each_expr.h"
#include "ast/ast_util.h"
#include "ast/occurs.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/converters/generic_model_converter.h"
#include "model/model_v2_pp.h"
#include "model/model_evaluator.h"

void generic_model_converter::add(func_decl * d, expr* e) {
    VERIFY(e);
    VERIFY(d->get_range() == e->get_sort());
    m_entries.push_back(entry(d, e, m, ADD));
}

void generic_model_converter::operator()(model_ref & md) {
    TRACE("model_converter", tout << "before generic_model_converter\n"; model_v2_pp(tout, *md); display(tout););
    
    model_evaluator ev(*(md.get()));
    ev.set_model_completion(m_completion);
    ev.set_expand_array_equalities(false);    
    expr_ref val(m);
    unsigned arity;
    bool reset_ev = false;
    obj_map<sort, ptr_vector<expr>> uninterpreted;
    for (unsigned i = m_entries.size(); i-- > 0; ) {
        entry const& e = m_entries[i];
        switch (e.m_instruction) {
        case instruction::HIDE:
            md->unregister_decl(e.m_f);
            break;
        case instruction::ADD:
            ev(e.m_def, val);
            TRACE("model_converter", tout << e.m_f->get_name() << " ->\n" << e.m_def << "\n==>\n" << val << "\n";);
            arity = e.m_f->get_arity();
            reset_ev = false;
            if (arity == 0) {
                expr* old_val = md->get_const_interp(e.m_f);
                if (old_val && old_val == val) {
                    // skip
                }
                else {
                    reset_ev = old_val != nullptr;
                    md->register_decl(e.m_f, val);
                }
                // corner case when uninterpreted constants are eliminated
                sort* s = e.m_f->get_range();
                if (m.is_uninterp(s) && !md->has_uninterpreted_sort(s)) {
                    uninterpreted.insert_if_not_there(s, {});
                    if (!uninterpreted[s].contains(val))
                        uninterpreted[s].push_back(val);
                }
            }
            else {
                func_interp * old_val = md->get_func_interp(e.m_f);
                if (old_val && old_val->get_else() == val) {
                    // skip
                }
                else {
                    reset_ev = old_val != nullptr;
                    func_interp * new_fi = alloc(func_interp, m, arity);
                    new_fi->set_else(val);
                    md->register_decl(e.m_f, new_fi);
                }
            }
            if (reset_ev) {
                ev.reset();
                ev.set_model_completion(m_completion);
                ev.set_expand_array_equalities(false);
            }
            break;
        }
    }
    for (auto const& [s, u] : uninterpreted) {
        md->register_usort(s, u.size(), u.data());
    }
    TRACE("model_converter", tout << "after generic_model_converter\n"; model_v2_pp(tout, *md););
}

void generic_model_converter::display(std::ostream & out) {
    for (entry const& e : m_entries) {
        switch (e.m_instruction) {
        case instruction::HIDE:
            display_del(out, e.m_f);
            break;
        case instruction::ADD:
            display_add(out, m, e.m_f, e.m_def);
            break;
        }
    }
}

generic_model_converter * generic_model_converter::copy(ast_translation & translator) {
    ast_manager& to = translator.to();
    generic_model_converter * res = alloc(generic_model_converter, to, m_orig.c_str());
    for (entry const& e : m_entries) {
        func_decl_ref d(translator(e.m_f.get()), to);
        switch (e.m_instruction) {
        case instruction::HIDE: 
            res->hide(d);
            break;        
        case instruction::ADD: {
            expr_ref def(translator(e.m_def.get()), to);            
            res->add(d, def);
            break;
        }
        }
    }
    return res;
}

void generic_model_converter::convert_initialize_value(vector<std::pair<expr_ref, expr_ref>> & var2value) {
    if (var2value.empty() || m_entries.empty())
        return;
    for (unsigned i = 0; i < var2value.size(); ++i) {
        auto& [var, value] = var2value[i];
        for (auto const& e : m_entries) {
            switch (e.m_instruction) {
            case HIDE: 
                break;
            case ADD: 
                if (is_uninterp_const(var) && e.m_f == to_app(var)->get_decl())
                    convert_initialize_value(e.m_def, i, var2value);                
                break;
            }
        }
    }
}

void generic_model_converter::convert_initialize_value(expr* def, unsigned i, vector<std::pair<expr_ref, expr_ref>>& var2value) {

    // var = if(c, th, el) = value
    // th = value => c = true
    // el = value => c = false
    expr* c = nullptr, *th = nullptr, *el = nullptr;
    auto& [var, value] = var2value[i];
    if (m.is_ite(def, c, th, el)) {
        if (value == th) {
            var = c;
            value = m.mk_true();
            return;
        }
        if (value == el) {
            var = c;
            value = m.mk_false();
            return;
        }
    }

    // var = def = value
    // => def = value
    if (is_uninterp(def)) {
        var = def;
        return;
    }    

}



void generic_model_converter::set_env(ast_pp_util* visitor) { 
    if (!visitor) {
        m_env = nullptr;
    }
    else {
        m_env = &visitor->env();       
        for (entry const& e : m_entries) {
            visitor->coll.visit_func(e.m_f);
            if (e.m_def) visitor->coll.visit(e.m_def);
        }
    }
}

void generic_model_converter::get_units(obj_map<expr, bool>& units) {
    th_rewriter rw(m);
    expr_safe_replace rep(m);
    expr_ref tmp(m);
    for (auto const& kv : units) {
        rep.insert(kv.m_key, kv.m_value ? m.mk_true() : m.mk_false());
    }
    for (unsigned i = m_entries.size(); i-- > 0;) {
        entry const& e = m_entries[i];
        switch (e.m_instruction) {
        case HIDE: 
            tmp = m.mk_const(e.m_f);
            if (units.contains(tmp)) {
                m.dec_ref(tmp);
                units.remove(tmp);
            }
            break;
        case ADD:
            if (e.m_f->get_arity() == 0 && m.is_bool(e.m_f->get_range())) {
                tmp = m.mk_const(e.m_f);
                if (units.contains(tmp)) {
                    break;
                }
                tmp = e.m_def;
                rep(tmp);
                rw(tmp);
                if (m.is_true(tmp)) {
                    tmp = m.mk_const(e.m_f);
                    m.inc_ref(tmp);
                    units.insert(tmp, true);
                    rep.insert(tmp, m.mk_true());
                }
                else if (m.is_false(tmp)) {
                    tmp = m.mk_const(e.m_f);
                    m.inc_ref(tmp);
                    units.insert(tmp, false);
                    rep.insert(tmp, m.mk_false());
                }
            }
            break;
        }
    }
}


/*
 \brief simplify definition expansion from model converter in the case they come from blocked clauses.
 In this case the definitions are of the form:
 
    x <=> x or not (C)

  or dually,

    x <=> not (not x or not C)

  in either case the definitions simplify to

    x or C

 */
expr_ref generic_model_converter::simplify_def(entry const& e) {
    expr_ref c(m.mk_const(e.m_f), m);
    if (m.is_bool(c) && occurs(c, e.m_def)) {
        expr_safe_replace rep(m);
        expr_ref result1 = e.m_def;
        expr_ref result2 = e.m_def;
        rep.apply_substitution(c, m.mk_true(),  result1);
        rep.apply_substitution(c, m.mk_false(), result2);
        th_rewriter rw(m);
        expr_ref result(m.mk_and(m.mk_implies(result2, c), m.mk_implies(c, result1)), m);
        rw(result);
        return result;
    }
    else {
        return expr_ref(m.mk_eq(c, e.m_def), m);
    }
}
