/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_model_converter.h

Abstract:

    Model conversion for fpa2bv_converter

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#include "ast/ast_smt2_pp.h"
#include "ast/rewriter/fpa_rewriter.h"
#include "tactic/fpa/fpa2bv_model_converter.h"

void fpa2bv_model_converter::display(std::ostream & out) {
    out << "(fpa2bv-model-converter";
    m_bv2fp->display(out);
    out << ")";
}

model_converter * fpa2bv_model_converter::translate(ast_translation & translator) {
    fpa2bv_model_converter * res = alloc(fpa2bv_model_converter, translator.to());
    res->m_bv2fp = m_bv2fp->translate(translator);
    return res;
}

void fpa2bv_model_converter::convert(model_core * mc, model * float_mdl) {
    TRACE("fpa2bv_mc", tout << "BV Model: " << std::endl;
        for (unsigned i = 0; i < mc->get_num_constants(); i++)
            tout << mc->get_constant(i)->get_name() << " --> " <<
                    mk_ismt2_pp(mc->get_const_interp(mc->get_constant(i)), m) << std::endl;
        for (unsigned i = 0; i < mc->get_num_functions(); i++) {
            func_decl * f = mc->get_function(i);
            tout << f->get_name() << "(...) := " << std::endl;
            func_interp * fi = mc->get_func_interp(f);
            for (unsigned j = 0; j < fi->num_entries(); j++) {
                func_entry const * fe = fi->get_entry(j);
                for (unsigned k = 0; k < f->get_arity(); k++)
                    tout << mk_ismt2_pp(fe->get_arg(k), m) << " ";
                tout << "--> " << mk_ismt2_pp(fe->get_result(), m) << std::endl;
            }
            tout << "else " << mk_ismt2_pp(fi->get_else(), m) << std::endl;
        });

    obj_hashtable<func_decl> seen;
    m_bv2fp->convert_consts(mc, float_mdl, seen);
    m_bv2fp->convert_rm_consts(mc, float_mdl, seen);
    m_bv2fp->convert_min_max_specials(mc, float_mdl, seen);
    m_bv2fp->convert_uf2bvuf(mc, float_mdl, seen);

    // Keep all the non-float constants.
    unsigned sz = mc->get_num_constants();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * c = mc->get_constant(i);
        if (!seen.contains(c))
            float_mdl->register_decl(c, mc->get_const_interp(c));
    }

    // And keep everything else
    sz = mc->get_num_functions();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * f = mc->get_function(i);
        if (!seen.contains(f)) {
            TRACE("fpa2bv_mc", tout << "Keeping: " << mk_ismt2_pp(f, m) << std::endl;);
            func_interp * val = mc->get_func_interp(f)->copy();
            float_mdl->register_decl(f, val);
        }
    }

    sz = mc->get_num_uninterpreted_sorts();
    for (unsigned i = 0; i < sz; i++) {
        sort * s = mc->get_uninterpreted_sort(i);
        ptr_vector<expr> u = mc->get_universe(s);
        float_mdl->register_usort(s, u.size(), u.c_ptr());
    }
}

model_converter * mk_fpa2bv_model_converter(ast_manager & m, fpa2bv_converter & conv) {
    return alloc(fpa2bv_model_converter, m, conv);
}
