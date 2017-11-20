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
#include "tactic/generic_model_converter.h"
#include "model/model_v2_pp.h"
#include "model/model_evaluator.h"


void generic_model_converter::operator()(model_ref & md, unsigned goal_idx) {
    std::cout << "model converter\n";
    TRACE("model_converter", tout << "before generic_model_converter\n"; model_v2_pp(tout, *md); display(tout););
    model_evaluator ev(*(md.get()));
    ev.set_model_completion(true);
    ev.set_expand_array_equalities(false);
    expr_ref val(m);
    unsigned arity;
    for (unsigned i = m_hide_entries.size(); i-- > 0; ) {
        entry const& e = m_hide_entries[i];
        std::cout << "hide " << e.m_f << "\n";
        md->unregister_decl(e.m_f);
    }
    for (unsigned i = m_add_entries.size(); i-- > 0; ) {
        entry const& e = m_add_entries[i];
        ev(e.m_def, val);
        std::cout << e.m_f << " " << e.m_def << " " << val << "\n";
        TRACE("model_converter", tout << e.m_f->get_name() << " ->\n" << e.m_def << "\n==>\n" << val << "\n";);
        arity = e.m_f->get_arity();
        if (arity == 0) {
            md->register_decl(e.m_f, val);
        }
        else {
            func_interp * new_fi = alloc(func_interp, m, arity);
            new_fi->set_else(val);
            md->register_decl(e.m_f, new_fi);
        }
    }
    TRACE("model_converter", tout << "after generic_model_converter\n"; model_v2_pp(tout, *md););
}

void generic_model_converter::display(std::ostream & out) {
    for (entry const& e : m_hide_entries) {
        display_del(out, e.m_f);
    }
    for (entry const& e : m_add_entries) {
        display_del(out, e.m_f);
    }
}

model_converter * generic_model_converter::translate(ast_translation & translator) {
    ast_manager& to = translator.to();
    generic_model_converter * res = alloc(generic_model_converter, to);
    for (entry const& e : m_hide_entries) {
        res->m_hide_entries.push_back(entry(translator(e.m_f.get()), translator(e.m_def.get()), to, e.m_instruction));
    }
    for (entry const& e : m_add_entries) {
        res->m_add_entries.push_back(entry(translator(e.m_f.get()), translator(e.m_def.get()), to, e.m_instruction));
    }
    return res;
}

void generic_model_converter::collect(ast_pp_util& visitor) { 
    m_env = &visitor.env(); 
    for (entry const& e : m_hide_entries) {
        visitor.coll.visit_func(e.m_f);
    }
    for (entry const& e : m_add_entries) {
        visitor.coll.visit_func(e.m_f);
        if (e.m_def) visitor.coll.visit(e.m_def);
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
    for (unsigned i = m_add_entries.size(); i-- > min_idx;) {
        entry const& e = m_add_entries[i];
        m_add_entries.pop_back();
        unsigned arity = e.m_f->get_arity();
        if (arity == 0) {
            fml = m.mk_and(fml, m.mk_eq(m.mk_const(e.m_f), e.m_def));
        }
        else {
            NOT_IMPLEMENTED_YET();
        }
        if (m_first_idx[e.m_f] == i) {
            m_first_idx.remove(e.m_f);
        }
    }
}
