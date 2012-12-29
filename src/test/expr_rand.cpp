#include "expr_rand.h"
#include "ast_pp.h"
#include "bv_decl_plugin.h"
#include "array_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "ast_smt_pp.h"
#include <iostream>
#include <sstream>
#include "reg_decl_plugins.h"

static unsigned rand_seed = 1;

void tst_expr_arith(unsigned num_files) {
    ast_manager m;
    reg_decl_plugins(m);

    expr_rand er(m);    
    er.seed(rand_seed);
    er.initialize_arith(20);

    family_id fid = m.mk_family_id("arith");
    sort* int_ty  = m.mk_sort(fid, INT_SORT, 0, 0);
    sort* real_ty = m.mk_sort(fid, REAL_SORT, 0, 0);

    er.initialize_array(3, int_ty, int_ty);
    er.initialize_array(3, int_ty, real_ty);

    er.initialize_basic(20);

    for (unsigned i = 0; i < num_files; ++i) {
        expr_ref e(m);
        er.get_next(m.mk_bool_sort(), e);
        ast_smt_pp pp(m);

        pp.set_logic("QF_AUFLIA");
        std::ostringstream buffer;
        buffer << "random_arith_" << i << ".smt";
        std::cout << buffer.str() << "\n";
        std::ofstream file(buffer.str().c_str());
        pp.display(file, e.get());
        file.close();
    }
    
}

void tst_expr_rand(unsigned num_files) {
    ast_manager m;
    
    m.register_plugin(symbol("bv"), alloc(bv_decl_plugin));
    m.register_plugin(symbol("array"), alloc(array_decl_plugin));

    expr_rand er(m);    
    er.initialize_bv(20);
    er.seed(rand_seed);
    parameter p1(1);
    parameter p2(2);
    parameter p8(8);
    parameter p32(32);
    family_id bvfid = m.mk_family_id("bv");
    sort* bv1  = m.mk_sort(bvfid, BV_SORT, 1, &p1);
    sort* bv2  = m.mk_sort(bvfid, BV_SORT, 1, &p2);
    sort* bv8  = m.mk_sort(bvfid, BV_SORT, 1, &p8);
    sort* bv32 = m.mk_sort(bvfid, BV_SORT, 1, &p32);
    er.initialize_array(3, bv8, bv32);
    er.initialize_array(3, bv1, bv1);
    er.initialize_array(3, bv1, bv2);
    er.initialize_array(3, bv2, bv1);
    er.initialize_array(3, bv2, bv2);
    er.initialize_array(3, bv8, bv8);
    er.initialize_array(3, bv32, bv32);
    er.initialize_basic(20);

    for (unsigned i = 0; i < num_files; ++i) {
        expr_ref e(m);
        er.get_next(m.mk_bool_sort(), e);
        ast_smt_pp pp(m);

        pp.set_logic("QF_AUFBV");
        std::ostringstream buffer;
        buffer << "random_bv_" << i << ".smt";
        std::cout << buffer.str() << "\n";
        std::ofstream file(buffer.str().c_str());
        pp.display(file, e.get());
        file.close();

    }
}

void tst_expr_rand(char** argv, int argc, int& i) {
    if (i + 1 < argc) {
        unsigned num_files = atol(argv[i+1]);
        i += 1;
        if (i + 1 < argc && 0 == strncmp(argv[i+1],"/rs:",3)) {
            rand_seed = atol(argv[i+1]+4);
			std::cout << "random seed:" << rand_seed << "\n";
			i += 1;
        }

        if (i + 1 < argc && 0 == strcmp(argv[i+1],"/arith")) {
            tst_expr_arith(num_files);
            return;
        }
        tst_expr_rand(num_files);
    }
}
