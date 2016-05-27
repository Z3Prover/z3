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
#include"trace.h"
#include"arith_decl_plugin.h"
#include"model_v2_pp.h"
#include"pb2bv_model_converter.h"

pb2bv_model_converter::pb2bv_model_converter(ast_manager & _m) : m(_m) {

}

pb2bv_model_converter::pb2bv_model_converter(ast_manager & _m, obj_map<func_decl, expr*> const & c2bit, bound_manager const & bm):
    m(_m) {
    obj_map<func_decl, expr*>::iterator it  = c2bit.begin();
    obj_map<func_decl, expr*>::iterator end = c2bit.end();
    for ( ; it != end; it++) {
        m_c2bit.push_back(func_decl_pair(it->m_key, to_app(it->m_value)->get_decl()));
        m.inc_ref(it->m_key);
        m.inc_ref(to_app(it->m_value)->get_decl());
    }      
    bound_manager::iterator it2  = bm.begin();
    bound_manager::iterator end2 = bm.end();
    for (; it2 != end2; ++it2) {
        expr * c = *it2;
        SASSERT(is_uninterp_const(c));
        func_decl * d = to_app(c)->get_decl();
        if (!c2bit.contains(d)) {
            SASSERT(d->get_arity() == 0);
            m.inc_ref(d);
            m_c2bit.push_back(func_decl_pair(d, static_cast<func_decl*>(0)));
        }
    }
}
    
pb2bv_model_converter::~pb2bv_model_converter() {
    svector<func_decl_pair>::const_iterator it  = m_c2bit.begin();
    svector<func_decl_pair>::const_iterator end = m_c2bit.end();
    for (; it != end; ++it) {
        m.dec_ref(it->first);
        m.dec_ref(it->second);
    }
}

void pb2bv_model_converter::operator()(model_ref & md) {
    (*this)(md, 0);
}

void pb2bv_model_converter::operator()(model_ref & md, unsigned goal_idx) {
    SASSERT(goal_idx == 0);
    TRACE("pb2bv", tout << "converting model:\n"; model_v2_pp(tout, *md); display(tout););
    arith_util a_util(m);

    svector<func_decl_pair>::const_iterator it  = m_c2bit.begin();
    svector<func_decl_pair>::const_iterator end = m_c2bit.end();
    for (; it != end; ++it) {
        if (it->second) {
            expr * val = md->get_const_interp(it->second);
            if (val == 0 || m.is_false(val)) {
                /* false's and don't cares get the integer 0 solution*/ 
                md->register_decl(it->first, a_util.mk_numeral(rational(0), true));
            } 
            else { 
                md->register_decl(it->first, a_util.mk_numeral(rational(1), true));
            }
        }
        else {
            // it->first is a don't care.
            md->register_decl(it->first, a_util.mk_numeral(rational(0), true));
        }
    }
}

void pb2bv_model_converter::display(std::ostream & out) {
    out << "(pb2bv-model-converter";
    svector<func_decl_pair>::const_iterator it  = m_c2bit.begin();
    svector<func_decl_pair>::const_iterator end = m_c2bit.end();
    for (; it != end; ++it) {
        out << "\n  (" << it->first->get_name() << " ";            
        if (it->second == 0)
            out << "0";
        else
            out << it->second->get_name();
        out << ")";
    }
    out << ")\n";
}

model_converter * pb2bv_model_converter::translate(ast_translation & translator) {
    ast_manager & to = translator.to();
    pb2bv_model_converter * res = alloc(pb2bv_model_converter, to);
    svector<func_decl_pair>::iterator it = m_c2bit.begin();
    svector<func_decl_pair>::iterator end = m_c2bit.end();
    for (; it != end; it++) {
        func_decl * f1 = translator(it->first);
        func_decl * f2 = translator(it->second);
        res->m_c2bit.push_back(func_decl_pair(f1, f2));
        to.inc_ref(f1);
        to.inc_ref(f2);
    }
    return res;
}
