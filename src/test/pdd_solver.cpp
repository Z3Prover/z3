#include "util/rlimit.h"
#include "math/grobner/pdd_solver.h"

#include "ast/bv_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/reg_decl_plugins.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"

namespace dd {
    void print_eqs(ptr_vector<solver::equation> const& eqs) {
        std::cout << "eqs\n";
        for (solver::equation* e : eqs) {
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
        
        solver gb(lim, m);
        gb.add(v1*v2 + v1*v3);
        gb.add(v1 - 1);
        gb.display(std::cout);
        gb.saturate();
        gb.display(std::cout);
        gb.reset();

        gb.add(v1*v1*v2 + v2*v3);
        gb.add(v1*v1*v2 + v2*v1);
        gb.display(std::cout);
        gb.saturate();
        gb.display(std::cout);
        gb.reset();

        gb.add(v1*v1*v2 + v2*v1);
        gb.add(v1*v1*v2 + v2*v1);
        gb.display(std::cout);
        gb.saturate();
        gb.display(std::cout);
        gb.reset();

        // stop early on contradiction
        gb.add(v1*v3*v3 + v3*v1 + 2);
        gb.add(v1*v3*v3 + v3*v1);
        gb.add(v3*v1 + v1*v2 + v2*v3);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v1);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v2);
        gb.saturate();        
        gb.display(std::cout << "early contradiction\n");
        gb.reset();

        // result is v1 = 0, v2 = 0.
        gb.add(v1*v3*v3 + v3*v1);
        gb.add(v3*v1 + v1*v2 + v2*v3);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v1);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v2);
        gb.saturate();        
        gb.display(std::cout << "v1 = v2 = 0\n");
        gb.reset();

        // everything rewrites to a multiple of v0
        gb.add(v3 - 2*v2);
        gb.add(v2 - 2*v1);
        gb.add(v1 - 2*v0);
        gb.saturate();    
        gb.display(std::cout << "multiple of v0\n");
        gb.reset();

        // 
    }

    expr_ref elim_or(ast_manager& m, expr* e) {
        obj_map<expr, expr*> cache;
        expr_ref_vector trail(m), todo(m), args(m);
        todo.push_back(e);
        while (!todo.empty()) {
            expr* f = todo.back(), *g;
            
            if (!is_app(f)) {
                cache.insert(f, f);
            }

            if (cache.contains(f)) {
                todo.pop_back();
                continue;
            }

            app* a = to_app(f);
            args.reset();
            for (expr* arg : *a) {
                if (cache.find(arg, g)) {
                    args.push_back(g);
                }
                else {
                    todo.push_back(arg);
                }
            }
            if (args.size() != a->get_num_args()) {
                continue;
            }
            todo.pop_back();
            if (m.is_or(a)) {
                for (unsigned i = 0; i < args.size(); ++i) {
                    args[i] = mk_not(m, args.get(i));
                }
                g = m.mk_not(m.mk_and(args.size(), args.data()));
            }
            else if (m.is_and(a)) {
                g = m.mk_and(args.size(), args.data());
                trail.push_back(g);
            }
            else if (m.is_eq(a)) {
                expr* x = args.get(0);
                expr* y = args.get(1);
                if (m.is_not(x, x)) {
                    g = m.mk_xor(x, y);
                }
                else if (m.is_not(y, y)) {
                    g = m.mk_xor(x, y);
                }
                else {
                    g = m.mk_not(m.mk_xor(x, y));
                }
            }
            else if (m.is_not(a)) {
                g = mk_not(m, args.get(0));
            }
            else {
                g = m.mk_app(a->get_decl(), args.size(), args.data());
            }
            trail.push_back(g);
            cache.insert(a, g);
        }
        return expr_ref(cache[e], m);
    }

    void add_def(unsigned_vector const& id2var, app* e, ast_manager& m, pdd_manager& p, solver& g) {
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
            q = v1 - ~v2;
        }
        else if (m.is_eq(e, a, b)) {
            pdd v2 = p.mk_var(id2var[a->get_id()]);
            pdd v3 = p.mk_var(id2var[b->get_id()]);
            q = v1 - ~(v2 ^ v3);
        }
        else if (m.is_xor(e, a, b)) {
            pdd v2 = p.mk_var(id2var[a->get_id()]);
            pdd v3 = p.mk_var(id2var[b->get_id()]);
            q = v1 - (v2 ^ v3);
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
        pdd_manager p(id2var.size(), use_mod2 ? pdd_manager::mod2_e : pdd_manager::zero_one_vars_e);
        solver g(m.limit(), p);

        for (expr* e : subterms(fmls)) {
            add_def(id2var, to_app(e), m, p, g);
        }
        if (!use_mod2) { // should be built-in 
            for (expr* e : subterms(fmls)) {
                pdd v = p.mk_var(id2var[e->get_id()]);
                g.add(v*v - v);
            }
        }
        for (expr* e : fmls) {
            g.add(1 - p.mk_var(id2var[e->get_id()]));
        }
        g.display(std::cout);
        g.simplify();
        g.display(std::cout);
        if (use_mod2) {
            solver::config cfg;
            cfg.m_enable_exlin = true;
            g.set(cfg);
            g.simplify();
            g.display(std::cout << "after exlin\n");
        }
        g.saturate();
        g.display(std::cout);
    }

    void test2() {
        ast_manager m;
        reg_decl_plugins(m);
        bv_util bv(m);
        expr_ref x(m.mk_const("x", bv.mk_sort(3)), m);
        expr_ref y(m.mk_const("y", bv.mk_sort(3)), m);
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
            fmls.push_back(elim_or(m, g->form(i)));        
        }
        test_simplify(fmls, true);
        test_simplify(fmls, false);
        
    }
}

void tst_pdd_solver() {
    dd::test1();
    dd::test2();
}
