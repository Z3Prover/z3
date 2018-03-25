
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/rewriter/bv_elim.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include <sstream>

bool bv_elim_cfg::reduce_quantifier(quantifier * q, 
                                expr * body, 
                                expr * const * new_patterns, 
                                expr * const * new_no_patterns,
                                expr_ref & result,
                                proof_ref & result_pr) {


    svector<symbol>  names, _names;
    sort_ref_buffer  sorts(m), _sorts(m);
    expr_ref_buffer  pats(m);
    expr_ref_buffer  no_pats(m);
    expr_ref_buffer  subst_map(m), _subst_map(m);
    var_subst        subst(m);
    bv_util          bv(m);
    expr_ref         new_body(m);
    expr*            old_body = body;
    unsigned num_decls = q->get_num_decls();
    family_id bfid = m.mk_family_id("bv");

    //
    // Traverse sequence of bound variables to eliminate
    // bit-vecctor variables and replace them by 
    // Booleans.
    // 
    unsigned var_idx = 0;
    bool found = false;
    for (unsigned i = num_decls; i > 0; ) {
        --i;
        sort*  s  = q->get_decl_sort(i);
        symbol nm = q->get_decl_name(i);

        if (bv.is_bv_sort(s)) {
            // convert n-bit bit-vector variable into sequence of n-Booleans.
            unsigned num_bits = bv.get_bv_size(s);
            expr_ref_buffer args(m);
            expr_ref bv(m);
            found = true;
            for (unsigned j = 0; j < num_bits; ++j) {
                std::ostringstream new_name;
                new_name << nm.str();
                new_name << "_";
                new_name << j;
                var* v = m.mk_var(var_idx++, m.mk_bool_sort());                
                args.push_back(v);
                _sorts.push_back(m.mk_bool_sort());
                _names.push_back(symbol(new_name.str().c_str()));
            }
            bv = m.mk_app(bfid, OP_MKBV, 0, nullptr, args.size(), args.c_ptr());
            _subst_map.push_back(bv.get());
        }
        else {
            _subst_map.push_back(m.mk_var(var_idx++, s));
            _sorts.push_back(s);
            _names.push_back(nm);
        }
    }
    if (!found) {
        return false;
    }
    // 
    // reverse the vectors.
    // 
    SASSERT(_names.size() == _sorts.size());
    for (unsigned i = _names.size(); i > 0; ) {
        --i;
        names.push_back(_names[i]);
        sorts.push_back(_sorts[i]);
    }
    for (unsigned i = _subst_map.size(); i > 0; ) {
        --i;
        subst_map.push_back(_subst_map[i]);
    }

    expr* const* sub  = subst_map.c_ptr();
    unsigned sub_size = subst_map.size();

    subst(old_body, sub_size, sub, new_body);

    for (unsigned j = 0; j < q->get_num_patterns(); j++) {
        expr_ref pat(m);        
        subst(new_patterns[j], sub_size, sub, pat);
        pats.push_back(pat);
    }
    for (unsigned j = 0; j < q->get_num_no_patterns(); j++) {
        expr_ref nopat(m);
        subst(new_no_patterns[j], sub_size, sub, nopat);
        no_pats.push_back(nopat);
    }

    result = m.mk_quantifier(true, 
                        names.size(),
                        sorts.c_ptr(),
                        names.c_ptr(),
                        new_body.get(),
                        q->get_weight(),
                        q->get_qid(),
                        q->get_skid(),
                        pats.size(), pats.c_ptr(),
                        no_pats.size(), no_pats.c_ptr());
    result_pr = m.mk_rewrite(q, result);
    return true;
}
