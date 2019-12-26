#include "util/rlimit.h"
#include "math/grobner/pdd_grobner.h"

#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/reg_decl_plugins.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"

namespace dd {
    void print_eqs(ptr_vector<grobner::equation> const& eqs) {
        std::cout << "eqs\n";
        for (grobner::equation* e : eqs) {
            std::cout << e->poly() << "\n";
        }
    }
    void test1() {
        pdd_manager m(4);
        reslimit lim;
        pdd v0 = m.mk_var(0);
        pdd v1 = m.mk_var(1);
        pdd v2 = m.mk_var(2);
        pdd v3 = m.mk_var(3);
        
        grobner gb(lim, m);
        gb.add(v1*v2 + v1*v3);
        gb.add(v1 - 1);
        print_eqs(gb.equations());
        gb.saturate();
        print_eqs(gb.equations());
        gb.reset();

        gb.add(v1*v1*v2 + v2*v3);
        gb.add(v1*v1*v2 + v2*v1);
        gb.saturate();
        print_eqs(gb.equations());
        gb.reset();

        gb.add(v1*v1*v2 + v2*v1);
        gb.add(v1*v1*v2 + v2*v1);
        gb.saturate();
        print_eqs(gb.equations());
        gb.reset();

        // stop early on contradiction
        gb.add(v1*v3*v3 + v3*v1 + 2);
        gb.add(v1*v3*v3 + v3*v1);
        gb.add(v3*v1 + v1*v2 + v2*v3);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v1);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v2);
        gb.saturate();        
        print_eqs(gb.equations());
        gb.reset();

        // result is v1 = 0, v2 = 0.
        gb.add(v1*v3*v3 + v3*v1);
        gb.add(v3*v1 + v1*v2 + v2*v3);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v1);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v2);
        gb.saturate();        
        print_eqs(gb.equations());
        gb.reset();

        // everything rewrites to a multiple of v0
        gb.add(v3 - 2*v2);
        gb.add(v2 - 2*v1);
        gb.add(v1 - 2*v0);
        gb.saturate();        
        print_eqs(gb.equations());
        gb.reset();

        // 
    }

    void add_def(unsigned_vector const& id2var, app* e, ast_manager& m, pdd_manager& p, grobner& g) {
        expr* a, *b;
        pdd v1 = p.mk_var(id2var[e->get_id()]);
        pdd q(p);
        if (m.is_and(e)) {
            pdd r = p.one();
            for (expr* arg : *e) r *= p.mk_var(id2var[arg->get_id()]);
            q = v1 - r;
        }
        else if (m.is_or(e)) {
            pdd r = p.zero();
            for (expr* arg : *e) r |= p.mk_var(id2var[arg->get_id()]);
            q = v1 - r;
        }
        else if (m.is_not(e, a)) {
            pdd v2 = p.mk_var(id2var[a->get_id()]);
            q = v1 + v2 - 1;
        }
        else if (m.is_eq(e, a, b)) {
            pdd v2 = p.mk_var(id2var[a->get_id()]);
            pdd v3 = p.mk_var(id2var[b->get_id()]);
            // v1 = (v2 = v3)
            // 111, 100 = 0
            // 001, 010 = 0
            // 000, 011 = 1
            // 110, 101 = 1
            q = v1 - v2 - v3 + 1 + 2*v2*v3 - 2*v1*v2*v3;
        }
        else if (is_uninterp_const(e)) {
            return;
        }
        else {
            UNREACHABLE();
        }
        g.add(q);
    }

    void collect_id2var(unsigned_vector& id2var, expr_ref_vector const& fmls) {
        svector<std::pair<unsigned, unsigned>> ds;
        unsigned maxid = 0;
        for (expr* e : subterms(fmls)) {
            ds.push_back(std::make_pair(to_app(e)->get_depth(), e->get_id()));
            maxid = std::max(maxid, e->get_id());
        }
        std::sort(ds.begin(), ds.end());
        unsigned v = 1;
        id2var.resize(maxid + 1);
        for (auto p : ds) {
            id2var[p.second] = v++;
        }
    }

    void test_simplify(expr_ref_vector& fmls, bool use_mod2) {
        ast_manager& m = fmls.get_manager();
        unsigned_vector id2var;

        collect_id2var(id2var, fmls);
        pdd_manager p(id2var.size());
        if (use_mod2) p.set_mod2_semantics();
        grobner g(m.limit(), p);

        for (expr* e : subterms(fmls)) {
            add_def(id2var, to_app(e), m, p, g);
        }
        for (expr* e : fmls) {
            g.add(1 - p.mk_var(id2var[e->get_id()]));
        }
        g.display(std::cout);
        g.simplify();
        g.display(std::cout);
        //g.saturate();
        //g.display(std::cout);
    }

    void test2() {
        ast_manager m;
        reg_decl_plugins(m);
        bv_util bv(m);
        expr_ref x(m.mk_const("x", bv.mk_sort(4)), m);
        expr_ref y(m.mk_const("y", bv.mk_sort(4)), m);
        expr_ref xy(bv.mk_bv_mul(x, y), m);
        expr_ref yx(bv.mk_bv_mul(y, x), m);
        expr_ref eq(m.mk_not(m.mk_eq(xy,yx)), m);
        goal_ref g = alloc(goal, m);
        g->assert_expr(eq);
        goal_ref_buffer res;
        tactic_ref tac = mk_bit_blaster_tactic(m);
        (*tac)(g, res);
        g = res[0];

        expr_ref_vector fmls(m);
        for (unsigned i = 0; i < g->size(); ++i) {
            fmls.push_back(g->form(i));        
        }
        test_simplify(fmls, true);
        test_simplify(fmls, false);
        
    }
}

void tst_pdd_grobner() {
    dd::test1();
    dd::test2();
}
