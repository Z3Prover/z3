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
#include "ast/for_each_expr.h"
#include "ast/ast_util.h"
#include "ast/occurs.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include "tactic/generic_model_converter.h"
#include "model/model_v2_pp.h"
#include "model/model_evaluator.h"


generic_model_converter::~generic_model_converter() {
}

void generic_model_converter::add(func_decl * d, expr* e) {
    VERIFY(e);
    VERIFY(d->get_range() == m.get_sort(e));
    m_first_idx.insert_if_not_there(d, m_entries.size());
    m_entries.push_back(entry(d, e, m, ADD));
}

void generic_model_converter::operator()(model_ref & md) {
    TRACE("model_converter", tout << "before generic_model_converter\n"; model_v2_pp(tout, *md); display(tout););
    
    model_evaluator ev(*(md.get()));
    ev.set_model_completion(true);
    ev.set_expand_array_equalities(false);    
    expr_ref val(m);
    unsigned arity;
    bool reset_ev = false;
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
                ev.set_model_completion(true);
                ev.set_expand_array_equalities(false);
            }
            break;
        }
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

model_converter * generic_model_converter::translate(ast_translation & translator) {
    ast_manager& to = translator.to();
    generic_model_converter * res = alloc(generic_model_converter, to, m_orig.c_str());
    for (entry const& e : m_entries) {
        res->m_entries.push_back(entry(translator(e.m_f.get()), translator(e.m_def.get()), to, e.m_instruction));
    }
    return res;
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

struct min_app_idx_proc {
    unsigned m_min;
    obj_map<func_decl, unsigned>& m_idxs;
    min_app_idx_proc(obj_map<func_decl, unsigned>& idxs) : m_min(UINT_MAX), m_idxs(idxs) {}
    void operator()(app * n) {
        unsigned idx;
        if (m_idxs.find(n->get_decl(), idx)) {
            m_min = std::min(m_min, idx);
        }
    }
    void operator()(var * n) {}
    void operator()(quantifier * n) {}
};

void generic_model_converter::operator()(expr_ref& fml) {
    min_app_idx_proc min_proc(m_first_idx);
    for_each_expr(min_proc, fml);
    unsigned min_idx = min_proc.m_min;
    if (min_idx == UINT_MAX) return;
    expr_ref_vector fmls(m);
    fmls.push_back(fml);
    for (unsigned i = m_entries.size(); i-- > min_idx;) {
        entry const& e = m_entries[i];
        if (e.m_instruction != instruction::ADD) {
            continue;
        }
        unsigned arity = e.m_f->get_arity();
        if (arity == 0) {
            fmls.push_back(simplify_def(e));
        }
        else {
            expr_ref_vector args(m);
            sort_ref_vector sorts(m);
            svector<symbol> names;
            for (unsigned i = 0; i < arity; ++i) {
                sorts.push_back(e.m_f->get_domain(i));
                names.push_back(symbol(i));
                args.push_back(m.mk_var(i, sorts.back()));
            }
            // TBD: check if order is correct with respect to quantifier binding ordering
            expr_ref lhs(m.mk_app(e.m_f, arity, args.c_ptr()), m);
            expr_ref body(m.mk_eq(lhs, e.m_def), m);
            fmls.push_back(m.mk_forall(arity, sorts.c_ptr(), names.c_ptr(), body));
        }
        if (m_first_idx[e.m_f] == i) {
            m_first_idx.remove(e.m_f);
        }
    }
    unsigned j = min_idx;
    for (unsigned i = min_idx; i < m_entries.size(); ++i) {
        entry& e = m_entries[i];
        if (e.m_instruction == instruction::HIDE) {
            if (i != j) {
                m_entries[j] = e;
            }
            ++j;
        }
    }
    m_entries.shrink(j);
    fml = mk_and(fmls);
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
