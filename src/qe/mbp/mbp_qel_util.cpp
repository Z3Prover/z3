/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_qel_util.h

Abstract:

    Utility methods for mbp_qel

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/

#include "qe/mbp/mbp_qel_util.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/expr_functors.h"
#include "ast/for_each_expr.h"
#include "ast/pp.h"

class check_uninterp_consts : public i_expr_pred {
    obj_hashtable<app> const &m_vars;
    family_id m_fid;
    decl_kind m_decl_kind;

  public:
    check_uninterp_consts(obj_hashtable<app> const &vars, ast_manager &man,
                          family_id fid = null_family_id,
                          decl_kind dk = null_decl_kind)
        : m_vars(vars), m_fid(fid), m_decl_kind(dk) {}
    bool operator()(expr *n) override {
        return (is_app(n) && is_uninterp_const(n) &&
                m_vars.contains(to_app(n))) &&
               ((m_fid == null_family_id || m_decl_kind == null_decl_kind) ||
                (is_sort_of(to_app(n)->get_sort(), m_fid, m_decl_kind)));
    }
};

// check if e contains any apps from vars
// if fid and dk are not null, check if the variable is of desired sort
bool contains_vars(expr *e, obj_hashtable<app> const &vars, ast_manager &man,
                   family_id fid, decl_kind dk) {
    check_uninterp_consts pred(vars, man, fid, dk);
    check_pred check(pred, man, false);
    return check(e);
}

app_ref new_var(sort *s, ast_manager &m) {
    return app_ref(m.mk_fresh_const("mbptg", s), m);
}

namespace collect_uninterp_consts_ns {
struct proc {
    obj_hashtable<app> &m_out;
    proc(obj_hashtable<app> &out) : m_out(out) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (is_uninterp_const(n)) m_out.insert(n);
    }
};
} // namespace collect_uninterp_consts_ns

// Return all uninterpreted constants of \p q
void collect_uninterp_consts(expr *e, obj_hashtable<app> &out) {
    collect_uninterp_consts_ns::proc proc(out);
    for_each_expr(proc, e);
}

namespace collect_selstore_vars_ns {
struct proc {
    ast_manager &m;
    obj_hashtable<app> &m_vars;
    array_util m_array_util;
    datatype_util m_dt_util;
    proc(obj_hashtable<app> &vars, ast_manager &man)
        : m(man), m_vars(vars), m_array_util(m), m_dt_util(m) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (m_array_util.is_select(n)) {
            expr *idx = n->get_arg(1);
            if (is_app(idx) && m_dt_util.is_accessor(to_app(idx)->get_decl()))
                return;
            collect_uninterp_consts(idx, m_vars);
        } else if (m_array_util.is_store(n)) {
            expr *idx = n->get_arg(1), *elem = n->get_arg(2);
            if (!(is_app(idx) &&
                  m_dt_util.is_accessor(to_app(idx)->get_decl())))
                collect_uninterp_consts(idx, m_vars);
            if (!(is_app(elem) &&
                  m_dt_util.is_accessor(to_app(elem)->get_decl())))
                collect_uninterp_consts(elem, m_vars);
        }
    }
};
} // namespace collect_selstore_vars_ns

// collect all uninterpreted consts used as array indices or values
void collect_selstore_vars(expr *fml, obj_hashtable<app> &vars,
                           ast_manager &man) {
    collect_selstore_vars_ns::proc proc(vars, man);
    quick_for_each_expr(proc, fml);
}
