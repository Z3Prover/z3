#include "ast/reg_decl_plugins.h"
#include "muz/spacer/spacer_global_generalizer.h"

void tst_spacer() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    fp_params params;
    spacer::context ctx(params, m);
    func_decl_ref pred(m.mk_func_decl(symbol("p"), 0u, nullptr, m.mk_bool_sort()), m);
    spacer::pred_transformer pt(ctx, ctx.get_manager(), pred);
    spacer::lemma_global_generalizer generalizer(ctx);

    expr_ref x(m.mk_const("x", a.mk_int()), m);
    expr_ref y(m.mk_const("y", a.mk_int()), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref two(a.mk_int(2), m);
    expr_ref five(a.mk_int(5), m);
    expr_ref sum(a.mk_add(x, y), m);
    expr_ref post(a.mk_le(sum, five), m);
    expr_ref coefficient(m.mk_var(0, a.mk_int()), m);
    expr_ref pattern(a.mk_mul(coefficient, x), m);
    spacer::pob_ref n = pt.mk_pob(nullptr, 1, 0, post);
    n->set_concretize_pattern(pattern);
    n->set_concretize();
    n->set_gas(2);

    model_ref mdl;
    ENSURE(!generalizer.mk_concretize_pob(*n, mdl));
    ENSURE(n->post() == post);
    ENSURE(n->is_concretize_enabled());
    ENSURE(n->get_gas() == 2);

    mdl = alloc(model, m);
    mdl->register_decl(to_app(x)->get_decl(), one);
    mdl->register_decl(to_app(y)->get_decl(), two);
    spacer::pob_ref concrete = generalizer.mk_concretize_pob(*n, mdl);
    ENSURE(concrete);
    expr_ref_vector cube(m);
    flatten_and(concrete->post(), cube);
    expr_ref x_bound(a.mk_le(x, one), m);
    expr_ref y_bound(a.mk_le(y, two), m);
    ENSURE(cube.size() == 2);
    ENSURE(cube.contains(x_bound));
    ENSURE(cube.contains(y_bound));
    ENSURE(concrete->level() == n->level());
    ENSURE(concrete->depth() == n->depth());
    ENSURE(concrete->parent() == n->parent());

    mdl = nullptr;
    ENSURE(!generalizer.mk_concretize_pob(*n, mdl));
}
