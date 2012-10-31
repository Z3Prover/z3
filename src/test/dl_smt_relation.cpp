#include "dl_smt_relation.h"
#include "arith_decl_plugin.h"
#include "dl_context.h"
#include "z3.h"
#include "z3_private.h"
#include "reg_decl_plugins.h"


namespace datalog {

    void test_smt_relation_unit() {
        ast_manager m;
        reg_decl_plugins(m);
        arith_util a(m);
        sort* int_sort = a.mk_int();
        sort* real_sort = a.mk_real();
        front_end_params params;
        context ctx(m, params);    
        relation_manager & rm = ctx.get_rmanager();
        relation_signature sig1;
        sig1.push_back(int_sort);
        sig1.push_back(int_sort);
        sig1.push_back(real_sort);
        
        smt_relation_plugin plugin(rm);
        
        scoped_rel<relation_base> r1 = plugin.mk_empty(sig1);

        // add_fact
        relation_fact fact1(m);
        fact1.push_back(a.mk_numeral(rational(1), true));
        fact1.push_back(a.mk_numeral(rational(2), true));
        fact1.push_back(a.mk_numeral(rational(3), false));

        relation_fact fact2(m);
        fact2.push_back(a.mk_numeral(rational(2), true));
        fact2.push_back(a.mk_numeral(rational(2), true));
        fact2.push_back(a.mk_numeral(rational(3), false));
                        
        r1->add_fact(fact1);
        r1->display(std::cout << "r1: ");


        // contains_fact
        SASSERT(r1->contains_fact(fact1));
        SASSERT(!r1->contains_fact(fact2));

        // empty
        scoped_rel<relation_base> r2 = plugin.mk_empty(sig1);
        SASSERT(!r1->empty());
        SASSERT(r2->empty());

        // clone
        scoped_rel<relation_base> r3 = r1->clone();

        // complement?
        r2->add_fact(fact2);
        scoped_rel<relation_base> r4 = dynamic_cast<smt_relation&>(*r2).complement(0);
        r4->display(std::cout << "complement r4: " );

        // join
        unsigned col_cnt = 2;
        unsigned cols1[2] = {1, 2};
        unsigned cols2[2] = {0, 2};
        scoped_ptr<relation_join_fn> joinfn = plugin.mk_join_fn(*r1, *r4, col_cnt, cols1, cols2);
        scoped_rel<relation_base> r5 = (*joinfn)(*r1, *r4);
        r5->display(std::cout<< "join r5: ");

        relation_fact fact3(m);
        fact3.push_back(a.mk_numeral(rational(1), true));
        fact3.push_back(a.mk_numeral(rational(2), true));
        fact3.push_back(a.mk_numeral(rational(3), false));
        fact3.push_back(a.mk_numeral(rational(2), true));
        fact3.push_back(a.mk_numeral(rational(2), true));
        fact3.push_back(a.mk_numeral(rational(3), false));
        SASSERT(!r5->contains_fact(fact3));
        fact3[5] = a.mk_numeral(rational(4), false);
        SASSERT(!r5->contains_fact(fact3));
        fact3[5] = a.mk_numeral(rational(3), false);
        fact3[4] = a.mk_numeral(rational(3), true);
        SASSERT(r5->contains_fact(fact3));

        // project
        unsigned removed_cols[2] = { 1, 4 };
        scoped_ptr<relation_transformer_fn> projfn = plugin.mk_project_fn(*r5, col_cnt, removed_cols);
        scoped_rel<relation_base> r6 = (*projfn)(*r5);
        r6->display(std::cout<< "project r6: ");

        // rename
        unsigned cycle[3] = { 0, 2, 4 };
        unsigned cycle_len = 3;
        scoped_rel<relation_transformer_fn> renamefn = plugin.mk_rename_fn(*r5, cycle_len, cycle);
        scoped_rel<relation_base> r7 = (*renamefn)(*r5);
        r7->display(std::cout << "rename r7: ");

        // union
        // widen
        relation_base* delta = 0;
        scoped_ptr<relation_union_fn> widenfn = plugin.mk_widen_fn(*r1, *r2, delta);
        scoped_ptr<relation_union_fn> unionfn = plugin.mk_union_fn(*r1, *r2, delta);
        scoped_rel<relation_base> r8 = r1->clone();
        (*unionfn)(*r8,*r2,0);
        r8->display(std::cout << "union r8: ");

        // filter_identical
        unsigned identical_cols[2] = { 1, 3 };
        scoped_ptr<relation_mutator_fn> filti = plugin.mk_filter_identical_fn(*r5, col_cnt, identical_cols);
        scoped_rel<relation_base> r9 = r1->clone();
        (*filti)(*r9);
        r9->display(std::cout << "filter identical r9: ");

        // filter_equal
        app_ref value(m);
        value = m.mk_const(symbol("x"), int_sort);
        scoped_rel<relation_mutator_fn> eqn = plugin.mk_filter_equal_fn(*r5, value.get(), 3);
        scoped_rel<relation_base> r10 = r1->clone();
        (*eqn)(*r10);
        r10->display(std::cout << "filter equal r10: ");


        // filter_interpreted
        app_ref cond(m);
        cond = a.mk_lt(m.mk_var(3, int_sort), m.mk_var(4, int_sort));
        scoped_rel<relation_mutator_fn> filtint = plugin.mk_filter_interpreted_fn(*r5, cond);
        scoped_rel<relation_base> r11 = r5->clone();
        (*filtint)(*r11);
        r11->display(std::cout << "filter interpreted r11: ");
                       
    }

    void test_smt_relation_api() {

        enable_trace("smt_relation");
        enable_trace("smt_relation2");
        enable_trace("quant_elim");
        Z3_config cfg = Z3_mk_config();
        Z3_set_param_value(cfg, "DL_DEFAULT_RELATION", "smt_relation2");
        Z3_context ctx = Z3_mk_context(cfg);
        Z3_fixedpoint dl = Z3_mk_fixedpoint(ctx);
        Z3_fixedpoint_inc_ref(ctx,dl);
        Z3_del_config(cfg);

        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
        Z3_func_decl nil_decl, is_nil_decl;
        Z3_func_decl cons_decl, is_cons_decl, head_decl, tail_decl;

        Z3_sort list = Z3_mk_list_sort(
            ctx, 
            Z3_mk_string_symbol(ctx, "list"),
            int_sort, 
            &nil_decl,
            &is_nil_decl,
            &cons_decl,
            &is_cons_decl,
            &head_decl,
            &tail_decl);

        Z3_sort listint[2] = { list, int_sort };
        Z3_symbol p_sym = Z3_mk_string_symbol(ctx, "p");
        Z3_symbol q_sym = Z3_mk_string_symbol(ctx, "q");


        Z3_func_decl p = Z3_mk_func_decl(ctx, p_sym, 2, listint, bool_sort);
        Z3_func_decl q = Z3_mk_func_decl(ctx, q_sym, 2, listint, bool_sort);
        Z3_fixedpoint_register_relation(ctx, dl, p);
        Z3_fixedpoint_register_relation(ctx, dl, q);


        Z3_ast zero = Z3_mk_numeral(ctx, "0", int_sort);
        Z3_ast one  = Z3_mk_numeral(ctx, "1", int_sort);
        Z3_ast two  = Z3_mk_numeral(ctx, "2", int_sort);
        Z3_ast x = Z3_mk_bound(ctx, 0, list);
        Z3_ast y = Z3_mk_bound(ctx, 1, int_sort);
        Z3_ast z = Z3_mk_bound(ctx, 2, list);
        Z3_ast zero_x[2] = { zero, x };
        Z3_ast fx = Z3_mk_app(ctx, cons_decl, 2, zero_x);
        Z3_ast zero_fx[2] = { zero, fx };
        Z3_ast ffx = Z3_mk_app(ctx, cons_decl, 2, zero_fx);
        Z3_ast xy[2] = { x, y };
        Z3_ast zy[2] = { z, y };
        // Z3_ast ffxy[2] = { ffx, y };
        // Z3_ast fxy[2] = { fx, y };
        Z3_ast zero_nil[2] = { zero, Z3_mk_app(ctx, nil_decl, 0, 0) };
        Z3_ast f0 = Z3_mk_app(ctx, cons_decl, 2, zero_nil);
        Z3_ast zero_f0[2] = { zero, f0 };
        Z3_ast f1 = Z3_mk_app(ctx, cons_decl, 2, zero_f0);
        Z3_ast zero_f1[2] = { zero, f1 };
        Z3_ast f2 = Z3_mk_app(ctx, cons_decl, 2, zero_f1);
        Z3_ast zero_f2[2] = { zero, f2 };
        Z3_ast f3 = Z3_mk_app(ctx, cons_decl, 2, zero_f2);
        Z3_ast zero_f3[2] = { zero, f3 };
        Z3_ast f4 = Z3_mk_app(ctx, cons_decl, 2, zero_f3);
        Z3_ast zero_f4[2] = { zero, f4 };
        Z3_ast f5 = Z3_mk_app(ctx, cons_decl, 2, zero_f4);
        Z3_ast zero_z[2] = { zero, z };
        Z3_ast fz = Z3_mk_app(ctx, cons_decl, 2, zero_z);
        
        Z3_ast pxy = Z3_mk_app(ctx, p, 2, xy);
        Z3_ast pzy    = Z3_mk_app(ctx, p, 2, zy);
        Z3_ast qxy = Z3_mk_app(ctx, q, 2, xy);
        Z3_ast qzy = Z3_mk_app(ctx, q, 2, zy);
        Z3_ast even_y = Z3_mk_eq(ctx, zero, Z3_mk_mod(ctx, y, two)); 
        Z3_ast odd_y  = Z3_mk_eq(ctx, one, Z3_mk_mod(ctx, y, two));
        

        // p(x, y) :- odd(y), p(z,y), f(z) = x . // dead rule.
        // q(x, y) :- p(f(f(x)), y).
        // p(x, y) :- q(f(x), y)                 // x decreases
        // p(x, y) :- even y, x = f^5(0)         // initial condition.

        Z3_ast body1[3] = { pzy, Z3_mk_eq(ctx, fz, x), odd_y };
        Z3_ast body2[2] = { pzy, Z3_mk_eq(ctx, ffx, z) };
        Z3_ast body3[2] = { qzy, Z3_mk_eq(ctx, fx, z) };
        Z3_ast body4[2] = { even_y, Z3_mk_eq(ctx, x, f5) };
        Z3_fixedpoint_add_rule(ctx, dl, Z3_mk_implies(ctx, Z3_mk_and(ctx, 3, body1), pxy), 0);
        Z3_fixedpoint_add_rule(ctx, dl, Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, body2), qxy), 0);
        Z3_fixedpoint_add_rule(ctx, dl, Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, body3), pxy), 0);
        Z3_fixedpoint_add_rule(ctx, dl, Z3_mk_implies(ctx, Z3_mk_and(ctx, 2, body4), pxy), 0);

        Z3_lbool r = Z3_fixedpoint_query(ctx, dl, pxy);
        if (r != Z3_L_UNDEF) {
            std::cout << Z3_ast_to_string(ctx, Z3_fixedpoint_get_answer(ctx, dl)) << "\n";
        }

        Z3_del_context(ctx);

    }
};

void tst_dl_smt_relation() {
    datalog::test_smt_relation_api();
    datalog::test_smt_relation_unit();
}
