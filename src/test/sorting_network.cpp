
#include "sorting_network.h"
#include "vector.h"
#include "ast.h"

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

void tst_sorting_network() {
    svector<unsigned> vec;
    unsigned_ext uext;
    sorting_network<unsigned_ext> sn(uext, vec);

    svector<unsigned> in1;
    in1.push_back(0);
    in1.push_back(1);
    in1.push_back(0);
    in1.push_back(1);
    in1.push_back(1);
    in1.push_back(0);

    sn(in1);

    for (unsigned i = 0; i < vec.size(); ++i) {
        std::cout << vec[i];
    }
    std::cout << "\n";
}
