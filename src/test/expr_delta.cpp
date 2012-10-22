#include "expr_delta.h"
#include "smtparser.h"
#include "ast_pp.h"
#include "ast_smt_pp.h"

static void iterate_delta(ast_manager& m, expr_delta& delta) {
    unsigned n = 0; 
    expr_ref_vector result(m);
    std::cout << "Delta\n";
    while (true) {
        result.reset();
        if (!delta.delta_dfs(n, result)) {
            return;
        }
        std::cout << n << ": ";
        for (unsigned i = 0; i < result.size(); ++i) {
            std::cout << mk_pp(result[i].get(), m) << " ";
        }
        std::cout << "\n";
        n++;
    }
}

void tst_expr_delta1() {
    ast_manager m;
    smtlib::parser* parser = smtlib::parser::create(m);
    parser->initialize_smtlib();

    parser->parse_string(
        "(benchmark samples :logic QF_LIA                                     \n"
        " :extrafuns ((a Int) (b Int) (c Int))                                \n"
        " :assumption (> a 0)                                                 \n"
        " :assumption (> b 0)                                                 \n"
        " :formula (forall (x Int) (y Int) (z Int) (and (<= 1 x) (<= x y)))   \n"
        " :formula (forall (x Int) (y Int) (z Int) (and (<= 2 (ite (<= z 1) x (* 2 x))) (<= x y)))\n"
        " :formula (forall (x Int) (y Int) (and (<= 2 (ite (forall (z Int) (<= z 1)) x (* 2 x))) (<= x y)))\n"
        " :formula (forall (x Int) (y Int) (and (<= 2 (ite (forall (z Int) (or (> x y) (<= z 1))) x (* 2 x))) (<= x y)))\n"
        ")"
        );

    smtlib::benchmark* b = parser->get_benchmark();

    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        expr_delta delta(m);

        for (unsigned i = 0; i < b->get_num_assumptions(); ++i) {
            delta.assert_cnstr(b->get_assumptions()[i]);
        }
        delta.assert_cnstr(b->begin_formulas()[j]);
        iterate_delta(m, delta);
    }

    dealloc(parser);
}

static void get_expr_delta(unsigned position, char const* in, char const* out) {
    ast_manager m;
    smtlib::parser* parser = smtlib::parser::create(m);
    parser->initialize_smtlib();

    if (!parser->parse_file(in)) {
        std::cout << "error parsing file\n";
        dealloc(parser);
        return;
    }

    smtlib::benchmark* b = parser->get_benchmark();

    SASSERT(b->get_num_formulas() == 1);
    expr_delta delta(m);

    for (unsigned i = 0; i < b->get_num_assumptions(); ++i) {
        delta.assert_cnstr(b->get_assumptions()[i]);
    }
    delta.assert_cnstr(b->begin_formulas()[0]);


    expr_ref_vector result(m);
    if (!delta.delta_dfs(position, result)) {
        std::cout << "done\n";
    }
    else {
        ast_smt_pp pp(m);
        std::ofstream outf(out);
        if (outf.bad() || outf.fail()) {
            std::cout << "Could not open output\n";
        }
        else {
            switch(b->get_status()) {
            case smtlib::benchmark::UNKNOWN:
                pp.set_status("unknown");
                break;
            case smtlib::benchmark::SAT:
                pp.set_status("sat");
                break;
            case smtlib::benchmark::UNSAT:
                pp.set_status("unsat");
                break;
            }                
            pp.set_logic(b->get_logic().str().c_str());
            for (unsigned i = 0; i + 1 < result.size(); ++i) {
                pp.add_assumption(result[i].get());
            }
            pp.display(outf, result[result.size()-1].get());
            
            std::cout << "ok\n";
        }
    }
    
    dealloc(parser);
}

void tst_expr_delta(char** argv, int argc, int& i) {
    if (i + 3 >= argc) {
        std::cout << "Usage: <position:number> <input:file-name> <output:file-name>\n";
        return;
    }
    ++i;
    unsigned position = atol(argv[i]);
    ++i;
    char const* in_file = argv[i];
    ++i;
    char const* out_file = argv[i];

    get_expr_delta(position, in_file, out_file);
    
}
