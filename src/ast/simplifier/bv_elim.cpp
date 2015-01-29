#include "bv_elim.h"
#include "bv_decl_plugin.h"
#include "var_subst.h"
#include <sstream>

void bv_elim::elim(quantifier* q, quantifier_ref& r) {

    svector<symbol>  names, _names;
    sort_ref_buffer  sorts(m_manager), _sorts(m_manager);
    expr_ref_buffer  pats(m_manager);
    expr_ref_buffer  no_pats(m_manager);
    expr_ref_buffer  subst_map(m_manager), _subst_map(m_manager);
    var_subst        subst(m_manager);
    bv_util          bv(m_manager);
    expr_ref         new_body(m_manager);
    expr*            old_body = q->get_expr();
    unsigned num_decls = q->get_num_decls();
    family_id bfid = m_manager.mk_family_id("bv");

    //
    // Traverse sequence of bound variables to eliminate
    // bit-vecctor variables and replace them by 
    // Booleans.
    // 
    unsigned var_idx = 0;
    for (unsigned i = num_decls; i > 0; ) {
        --i;
        sort*  s  = q->get_decl_sort(i);
        symbol nm = q->get_decl_name(i);

        if (bv.is_bv_sort(s)) {
            // convert n-bit bit-vector variable into sequence of n-Booleans.
            unsigned num_bits = bv.get_bv_size(s);
            expr_ref_buffer args(m_manager);
            expr_ref bv(m_manager);
            for (unsigned j = 0; j < num_bits; ++j) {
                std::ostringstream new_name;
                new_name << nm.str();
                new_name << "_";
                new_name << j;
                var* v = m_manager.mk_var(var_idx++, m_manager.mk_bool_sort());                
                args.push_back(v);
                _sorts.push_back(m_manager.mk_bool_sort());
                _names.push_back(symbol(new_name.str().c_str()));
            }
            bv = m_manager.mk_app(bfid, OP_MKBV, 0, 0, args.size(), args.c_ptr());
            _subst_map.push_back(bv.get());
        }
        else {
            _subst_map.push_back(m_manager.mk_var(var_idx++, s));
            _sorts.push_back(s);
            _names.push_back(nm);
        }
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
        expr_ref pat(m_manager);        
        subst(q->get_pattern(j), sub_size, sub, pat);
        pats.push_back(pat);
    }
    for (unsigned j = 0; j < q->get_num_no_patterns(); j++) {
        expr_ref nopat(m_manager);
        subst(q->get_no_pattern(j), sub_size, sub, nopat);
        no_pats.push_back(nopat);
    }

    r = m_manager.mk_quantifier(true, 
                                names.size(),
                                sorts.c_ptr(),
                                names.c_ptr(),
                                new_body.get(),
                                q->get_weight(),
                                q->get_qid(),
                                q->get_skid(),
                                pats.size(), pats.c_ptr(),
                                no_pats.size(), no_pats.c_ptr());
}

bool bv_elim_star::visit_quantifier(quantifier* q) {
    // behave like destructive resolution, do not recurse.
    return true;
}

void bv_elim_star::reduce1_quantifier(quantifier* q) {
    quantifier_ref r(m);
    proof_ref pr(m);
    m_bv_elim.elim(q, r);
    if (m.fine_grain_proofs()) {
        pr = m.mk_rewrite(q, r.get());
    }
    else {
        pr = 0;
    }
    cache_result(q, r, pr);
}
