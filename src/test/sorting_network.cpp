
#include "sorting_network.h"
#include "vector.h"
#include "ast.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"


struct ast_ext {
    ast_manager& m;
    ast_ext(ast_manager& m):m(m) {}
    typedef expr* T;
    typedef expr_ref_vector vector;
    T mk_ite(T a, T b, T c) { 
        return m.mk_ite(a, b, c);
    }
    T mk_le(T a, T b) {
        if (m.is_bool(a)) {
                return m.mk_implies(a, b);
        }
        UNREACHABLE();
        return 0;
    }
    T mk_default() {
        return m.mk_false();
    }        
};

struct unsigned_ext {
    unsigned_ext() {}
    typedef unsigned T;
    typedef svector<unsigned> vector;
    T mk_ite(T a, T b, T c) {
        return (a==1)?b:c;
    }
    T mk_le(T a, T b) {
        return (a <= b)?1:0;
    }
    T mk_default() {
        return 0;
    }
};

static void is_sorted(svector<unsigned> const& v) {
    for (unsigned i = 0; i + 1 < v.size(); ++i) {
        SASSERT(v[i] <= v[i+1]);
    }
}

static void test_sorting1() {
    svector<unsigned> in, out;
    unsigned_ext uext;
    sorting_network<unsigned_ext> sn(uext);

    in.push_back(0);
    in.push_back(1);
    in.push_back(0);
    in.push_back(1);
    in.push_back(1);
    in.push_back(0);

    sn(in, out);

    is_sorted(out);
    for (unsigned i = 0; i < out.size(); ++i) {
        std::cout << out[i];
    }
    std::cout << "\n";
}

static void test_sorting2() {
    svector<unsigned> in, out;
    unsigned_ext uext;
    sorting_network<unsigned_ext> sn(uext);

    in.push_back(0);
    in.push_back(1);
    in.push_back(2);
    in.push_back(1);
    in.push_back(1);
    in.push_back(3);

    sn(in, out);

    is_sorted(out);

    for (unsigned i = 0; i < out.size(); ++i) {
        std::cout << out[i];
    }
    std::cout << "\n";
}

static void test_sorting4_r(unsigned i, svector<unsigned>& in) {
    if (i == in.size()) {
        svector<unsigned> out;
        unsigned_ext uext;
        sorting_network<unsigned_ext> sn(uext);
        sn(in, out);
        is_sorted(out);
        std::cout << "sorted\n";
    }
    else {
        in[i] = 0;
        test_sorting4_r(i+1, in);
        in[i] = 1;
        test_sorting4_r(i+1, in);
    }
}

static void test_sorting4() {
    svector<unsigned> in;
    in.resize(5);
    test_sorting4_r(0, in);
}

void test_sorting3() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < 7; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    for (unsigned i = 0; i < in.size(); ++i) {
        std::cout << mk_pp(in[i].get(), m) << "\n";
    }
    ast_ext aext(m);
    sorting_network<ast_ext> sn(aext);
    sn(in, out);
    std::cout << "size: " << out.size() << "\n";
    for (unsigned i = 0; i < out.size(); ++i) {
        std::cout << mk_pp(out[i].get(), m) << "\n";
    }
}

void tst_sorting_network() {
    test_sorting1();
    test_sorting2();
    test_sorting3();
    test_sorting4();
}
