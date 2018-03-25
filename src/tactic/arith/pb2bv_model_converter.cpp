/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pb2bv_model_converter.cpp

Abstract:

    Model converter for the pb2bv tactic.

Author:

    Christoph (cwinter) 2012-02-15

Notes:

--*/
#include "util/trace.h"
#include "ast/arith_decl_plugin.h"
#include "model/model_v2_pp.h"
#include "tactic/arith/pb2bv_model_converter.h"

pb2bv_model_converter::pb2bv_model_converter(ast_manager & _m) : m(_m) {

}

pb2bv_model_converter::pb2bv_model_converter(ast_manager & _m, obj_map<func_decl, expr*> const & c2bit, bound_manager const & bm):
    m(_m) {
    for (auto const& kv : c2bit) {
        m_c2bit.push_back(func_decl_pair(kv.m_key, to_app(kv.m_value)->get_decl()));
        m.inc_ref(kv.m_key);
        m.inc_ref(to_app(kv.m_value)->get_decl());
    }      
    for (expr* c : bm) {
        SASSERT(is_uninterp_const(c));
        func_decl * d = to_app(c)->get_decl();
        if (!c2bit.contains(d)) {
            SASSERT(d->get_arity() == 0);
            m.inc_ref(d);
            m_c2bit.push_back(func_decl_pair(d, static_cast<func_decl*>(nullptr)));
        }
    }
}
    
pb2bv_model_converter::~pb2bv_model_converter() {
    for (auto const& kv : m_c2bit) {
        m.dec_ref(kv.first);
        m.dec_ref(kv.second);
    }
}

void pb2bv_model_converter::get_units(obj_map<expr, bool>& units) { 
    if (!m_c2bit.empty()) units.reset(); 
}


void pb2bv_model_converter::operator()(model_ref & md) {
    TRACE("pb2bv", tout << "converting model:\n"; model_v2_pp(tout, *md); display(tout););
    arith_util a_util(m);

    for (auto const& kv : m_c2bit) {
        if (kv.second) {
            expr * val = md->get_const_interp(kv.second);
            if (val == nullptr || m.is_false(val)) {
                /* false's and don't cares get the integer 0 solution*/ 
                md->register_decl(kv.first, a_util.mk_numeral(rational(0), true));
            } 
            else { 
                md->register_decl(kv.first, a_util.mk_numeral(rational(1), true));
            }
        }
        else {
            // kv.first is a don't care.
            md->register_decl(kv.first, a_util.mk_numeral(rational(0), true));
        }
    }
}

void pb2bv_model_converter::display(std::ostream & out) {
    out << "(pb2bv-model-converter";
    for (auto const& kv : m_c2bit) {
        out << "\n  (" << kv.first->get_name() << " ";            
        if (kv.second == 0)
            out << "0";
        else
            out << kv.second->get_name();
        out << ")";
    }
    out << ")\n";
}

model_converter * pb2bv_model_converter::translate(ast_translation & translator) {
    ast_manager & to = translator.to();
    pb2bv_model_converter * res = alloc(pb2bv_model_converter, to);
    for (auto const& kv : m_c2bit) {
        func_decl * f1 = translator(kv.first);
        func_decl * f2 = translator(kv.second);
        res->m_c2bit.push_back(func_decl_pair(f1, f2));
        to.inc_ref(f1);
        to.inc_ref(f2);
    }
    return res;
}
