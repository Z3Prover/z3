
#include "horn_subsume_model_converter.h"
#include "arith_decl_plugin.h"
#include "model_smt2_pp.h"
#include "reg_decl_plugins.h"

void tst_horn_subsume_model_converter() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);

    ptr_vector<sort> ints;
    ints.push_back(a.mk_int());
    ints.push_back(a.mk_int());
    ints.push_back(a.mk_int());

    func_decl_ref p(m), q(m), r(m);
    p = m.mk_func_decl(symbol("p"), 2, ints.c_ptr(), m.mk_bool_sort());
    q = m.mk_func_decl(symbol("q"), 2, ints.c_ptr(), m.mk_bool_sort());
    r = m.mk_func_decl(symbol("r"), 2, ints.c_ptr(), m.mk_bool_sort());

    ref<horn_subsume_model_converter> mc = alloc(horn_subsume_model_converter,m);
    model_ref mr = alloc(model, m);

    mc->insert(p, m.mk_app(q, a.mk_numeral(rational(1), true), a.mk_numeral(rational(2), true)));

    model_converter_ref mcr = mc.get();
    apply(mcr, mr, 0);
    model_smt2_pp(std::cout, m, *mr.get(), 0);

    mr = alloc(model, m);
    mc->insert(p, m.mk_app(q, a.mk_numeral(rational(3), true), a.mk_numeral(rational(5), true)));
    apply(mcr, mr, 0);
    model_smt2_pp(std::cout, m, *mr.get(), 0);

    mr = alloc(model, m);
    mc->insert(p, m.mk_app(r, m.mk_var(0,a.mk_int()), m.mk_var(1, a.mk_int())));
    apply(mcr, mr, 0);
    model_smt2_pp(std::cout, m, *mr.get(), 0);

    mr = alloc(model, m);
    app_ref head1(m);
    expr_ref body1(m), body2(m);
    func_decl_ref pred(m);
    head1 = m.mk_app(p, m.mk_var(0, a.mk_int()), m.mk_var(0, a.mk_int()));
    body1 = m.mk_app(q, m.mk_var(1, a.mk_int()), m.mk_var(2, a.mk_int()));
    VERIFY(mc->mk_horn(head1, body1, pred, body2));
    mc->insert(pred, body2); 
    apply(mcr, mr, 0);
    model_smt2_pp(std::cout, m, *mr.get(), 0);

    mr = alloc(model, m);
    head1 = m.mk_app(p, m.mk_var(0, a.mk_int()), m.mk_var(0, a.mk_int()));
    body1 = m.mk_app(q, m.mk_var(1, a.mk_int()), m.mk_var(0, a.mk_int()));
    VERIFY(mc->mk_horn(head1, body1, pred, body2));
    mc->insert(pred, body2); 
    apply(mcr, mr, 0);
    model_smt2_pp(std::cout, m, *mr.get(), 0);


}
