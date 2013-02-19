#include "expr_substitution.h"
#include "smt_params.h"
#include "substitution.h"
#include "unifier.h"
#include "bv_decl_plugin.h"
#include "ast_pp.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"

void tst_substitution()
{
    memory::initialize(0);
    smt_params params;
    params.m_model = true;

    enable_trace("subst_bug");

    ast_manager m;
    reg_decl_plugins(m);

    var_ref v1(m.mk_var(0, m.mk_bool_sort()), m);
    var_ref v2(m.mk_var(1, m.mk_bool_sort()), m);
    var_ref v3(m.mk_var(2, m.mk_bool_sort()), m);
    var_ref v4(m.mk_var(3, m.mk_bool_sort()), m);

    substitution subst(m);
    subst.reserve(1,4);
    unifier unif(m);

    bool ok1 = unif(v1.get(), v2.get(), subst, false);
    bool ok2 = unif(v2.get(), v1.get(), subst, false);

    expr_ref res(m);

    TRACE("substitution", subst.display(tout););
    TRACE("substitution", tout << ok1 << " " << ok2 << "\n";);
    subst.display(std::cout);
    subst.apply(v1.get(), res);
    TRACE("substitution", tout << mk_pp(res, m) << "\n";);

    expr_ref q(m), body(m);
    sort_ref_vector sorts(m);
    svector<symbol> names;
    sorts.push_back(m.mk_bool_sort());
    names.push_back(symbol("dude"));
    body = m.mk_and(m.mk_eq(v1,v2), m.mk_eq(v3,v4));
    q = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), body);
    subst.apply(q, res);
    TRACE("substitution", tout << mk_pp(q, m) << "\n->\n" << mk_pp(res, m) << "\n";);

}
