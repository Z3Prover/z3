#include "math/polysat/log.h"
#include "math/polysat/solver.h"
#include "math/polysat/viable2.h"

namespace polysat {

    struct solver_scopev {
        reslimit lim;
    };

    struct scoped_solverv : public solver_scopev, public solver {
        viable2 v;
        scoped_solverv(): solver(lim), v(*this) {}
    };

    static void test1() {
        scoped_solverv s;
        auto xv = s.add_var(3);
        auto x = s.var(xv);
        s.v.push(3);
        rational val;
        auto c = s.ule(x + 3, x + 5);
        s.v.intersect(xv, c);
        std::cout << s.v << "\n";
        std::cout << "min-max " << s.v.min_viable(xv) << " " << s.v.max_viable(xv) << "\n";
        s.v.intersect(xv, s.ule(x, 2));
        std::cout << s.v << "\n";
        s.v.intersect(xv, s.ule(1, x));
        std::cout << s.v << "\n";
        std::cout << "min-max " << s.v.min_viable(xv) << " " << s.v.max_viable(xv) << "\n";
        s.v.intersect(xv, s.ule(x, 3));
        std::cout << s.v << "\n";
        std::cout << s.v.find_viable(xv, val) << " " << val << "\n";        
        std::cout << "min-max " << s.v.min_viable(xv) << " " << s.v.max_viable(xv) << "\n";
        s.v.intersect(xv, s.ule(3, x));
        std::cout << s.v << "\n";
        std::cout << s.v.find_viable(xv, val) << " " << val << "\n";      
    }

    static void test2() {

    }
}



void tst_viable() {
    polysat::test1();
    polysat::test2();
}