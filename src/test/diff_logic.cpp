/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    diff_logic.cpp

Abstract:

    Unit tests for difference logic

Author:

    Leonardo de Moura (leonardo) 2006-11-22.

Revision History:

--*/
#ifdef _WINDOWS
#include"rational.h"
#include"diff_logic.h"
#include"smt_literal.h"
#include"util.h"
#include"debug.h"

struct diff_logic_ext {
    typedef rational numeral;
    typedef smt::literal  explanation;
};

template class dl_graph<diff_logic_ext>;

typedef dl_graph<diff_logic_ext> dlg;

struct tst_dl_functor {
	smt::literal_vector m_literals;
    void operator()(smt::literal l) {
        m_literals.push_back(l);
    }
};

static void tst1() {
    dlg g;
    smt::literal l;
    g.init_var(1);
    g.init_var(2);
    g.init_var(3);
    g.enable_edge(g.add_edge(1, 2, rational(1), l));
    g.enable_edge(g.add_edge(2, 3, rational(2), l));
    g.push();
    g.enable_edge(g.add_edge(1, 3, rational(4), l));
    g.init_var(4);
    g.enable_edge(g.add_edge(1, 4, rational(5), l));
    g.enable_edge(g.add_edge(4, 2, rational(0), l));
    g.pop(1);
}

static void tst2() {
    dlg g;
    rational w;
    smt::literal l1(1);
    smt::literal l2(2);
    smt::literal l3(3);
    smt::literal l4(4);
    smt::literal l5(5);
    smt::literal l6(6);
    g.init_var(0);
    g.init_var(1);
    g.init_var(2);
    g.init_var(3);
    g.init_var(4);
    smt::literal d;
    SASSERT(g.enable_edge(g.add_edge(1, 2, rational(-1), l1)));
    SASSERT(g.get_edge_weight(1, 2, w, d) && w == rational(-1));
    SASSERT(!g.get_edge_weight(2, 3, w, d));
    SASSERT(g.enable_edge(g.add_edge(2, 3, rational(-2), l2)));
    SASSERT(g.enable_edge(g.add_edge(1, 4, rational(1), l3)));
    SASSERT(g.get_edge_weight(1, 2, w, d) && w == rational(-1));
    SASSERT(g.get_edge_weight(1, 4, w, d) && w == rational(1));
    SASSERT(!g.get_edge_weight(1, 3, w, d));
    SASSERT(g.enable_edge(g.add_edge(2, 4, rational(10), l6)));
    SASSERT(g.is_feasible());
    g.push();
    SASSERT(g.enable_edge(g.add_edge(3, 0, rational(2), l4)));
    SASSERT(!g.enable_edge(g.add_edge(0, 1, rational(-1), l5)));
    SASSERT(!g.is_feasible());
    TRACE("diff_logic", g.display(tout););
    struct proc {
        svector<bool> found;
        proc():
            found(7, false) {
        }
        void operator()(smt::literal l) {
            found[l.var()] = true;
        }
    };
    proc p;
    g.traverse_neg_cycle(true, p);
    SASSERT(p.found[0] == false);
    SASSERT(p.found[1] == true);
    SASSERT(p.found[2] == true);
    SASSERT(p.found[3] == false);
    SASSERT(p.found[4] == true);
    SASSERT(p.found[5] == true);
    SASSERT(p.found[6] == false);
    g.pop(1);
    SASSERT(g.is_feasible());
    TRACE("diff_logic", g.display(tout););
}

static int add_edge(dlg& g, dl_var src, dl_var dst, int weight, unsigned lit) {
    int id = g.add_edge(src, dst, rational(weight), smt::literal(lit));
    bool ok = g.enable_edge(id);
    SASSERT(ok);
    return id;
}

static void tst3() {
    dlg g;
    for (unsigned i = 1; i <= 10; ++i) {
        g.init_var(i);
    }
    add_edge(g, 1, 2, 1, 12);
    add_edge(g, 1, 3, 1, 13);
    add_edge(g, 1, 4, 1, 14);
    add_edge(g, 2, 5, 1, 25);
    add_edge(g, 2, 6, 1, 26);
    add_edge(g, 3, 5, 1, 35);
    add_edge(g, 4, 5, 1, 45);
    add_edge(g, 4, 6, 1, 46);
    int xy = add_edge(g, 5, 6, 1, 56);
    add_edge(g, 5, 7, 1, 57);
    add_edge(g, 5, 9, 1, 59);
    add_edge(g, 6, 7, 1, 67);
    add_edge(g, 6, 8, 1, 68);
    add_edge(g, 6, 9, 1, 69);
    add_edge(g, 6, 10, 1, 610);
    add_edge(g, 8, 10, 1, 810);
    add_edge(g, 9, 10, 1, 910);
    TRACE("diff_logic", g.display(tout););

    int e38 = g.add_edge(3, 8, rational(3), smt::literal(38));
    std::cout << "Edge: " << e38 << "\n";

    svector<edge_id> subsumed;
    g.find_subsumed(xy, subsumed);

    for (unsigned i = 0; i < subsumed.size(); ++i) {
        std::cout << "subsumed: " << subsumed[i] << "\n";
        SASSERT(e38 == subsumed[i]);

        tst_dl_functor tst_fn;

        g.explain_subsumed_lazy(xy, subsumed[i], tst_fn);

        for (unsigned j = 0; j < tst_fn.m_literals.size(); ++j) {
            std::cout << tst_fn.m_literals[j] << " ";
        }
        std::cout << "\n";

    }


}

void tst_diff_logic() {
    //tst1();
    //tst2();
    //tst3();
}
#else
void tst_diff_logic() {
}
#endif
