/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    grobner.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-05.

Revision History:

--*/
#include"smtparser.h"
#include"ast_pp.h"
#include"arith_decl_plugin.h"
#include"simplifier.h"
#include"basic_simplifier_plugin.h"
#include"arith_simplifier_plugin.h"
#include"front_end_params.h"
#include"grobner.h"
#include"reg_decl_plugins.h"

void display_eqs(grobner & gb, v_dependency_manager & dep_m) {
    std::cerr << "RESULT:\n";
    ptr_vector<grobner::equation> eqs;
    gb.get_equations(eqs);
    ptr_vector<grobner::equation>::iterator it  = eqs.begin();
    ptr_vector<grobner::equation>::iterator end = eqs.end();
    for (; it != end; ++it) {
        grobner::equation * eq = *it;
        ptr_vector<void> exs; 
        v_dependency * d = eq->get_dependency();
        dep_m.linearize(d, exs);
        std::cerr << "{";
        ptr_vector<void>::iterator it2  = exs.begin();
        ptr_vector<void>::iterator end2 = exs.end();
        for (bool first = true; it2 != end2; ++it2) {
            if (first) first = false; else std::cerr << " ";
            std::cerr << *it2; 
        }
        std::cerr << "}, lc: " << eq->is_linear_combination() << ", ";
        gb.display_equation(std::cerr, *eq);
    }
}

void tst_grobner(char ** argv, int argc, int & i) {
    front_end_params params;
    if (i + 1 < argc) {
        char const* file_path = argv[i+1];

        ast_manager m;
        smtlib::parser* parser = smtlib::parser::create(m);
        reg_decl_plugins(m);
        parser->initialize_smtlib();

        if (!parser->parse_file(file_path)) {
            std::cout << "Could not parse file : " << file_path << std::endl;
            dealloc(parser);
            return;
        }
        
        smtlib::benchmark* b = parser->get_benchmark();
        simplifier simp(m);
        basic_simplifier_plugin * bp = alloc(basic_simplifier_plugin, m);
        simp.register_plugin(bp);
        simp.register_plugin(alloc(arith_simplifier_plugin, m, *bp, params));
        arith_util util(m);
        v_dependency_manager dep_m;
        grobner gb(m, dep_m);
        
        ptr_vector<expr>::const_iterator it  = b->begin_axioms();
        ptr_vector<expr>::const_iterator end = b->end_axioms();
        for (unsigned idx = 1; it != end; ++it, ++idx) {
            expr * ax = *it;
            expr_ref s_ax(m);
            proof_ref pr(m);
            simp(ax, s_ax, pr);
            std::cerr << mk_pp(s_ax, m) << "\n";
            if (m.is_eq(s_ax))
                gb.assert_eq(s_ax, dep_m.mk_leaf(reinterpret_cast<void*>(idx)));
        }
        gb.display(std::cerr);
        gb.compute_basis(1024);
        display_eqs(gb, dep_m);
        dealloc(parser);
    }
}

