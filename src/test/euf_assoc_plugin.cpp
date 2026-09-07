/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "util/util.h"
#include "ast/euf/euf_assoc_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace {

    struct assoc_test {
        ast_manager m;
        euf::egraph g;
        sort_ref s;
        func_decl_ref f;
        euf::assoc_plugin* p;
        unsigned next_var = 0;

        assoc_test(unsigned max_rules = 64):
            g(m),
            s(m.mk_uninterpreted_sort(symbol("S")), m),
            f(m.mk_func_decl(symbol("f"), s, s, s), m),
            p(alloc(euf::assoc_plugin, g, user_sort_family_id)) {
            p->register_associative([this](euf::enode const* n) { return n->get_decl() == f; });
            p->register_variable([](euf::enode const* n) {
                return n->num_args() == 0 && n->get_decl()->get_name() == symbol("x");
            });
            p->register_unit([](euf::enode const* n) {
                return n->num_args() == 0 && n->get_decl()->get_name() != symbol("x");
            });
            p->set_completion_limits(max_rules, 256);
            g.add_plugin(p);
        }

        expr_ref constant(char const* name) {
            return expr_ref(m.mk_const(symbol(name), s), m);
        }

        expr_ref app(expr* a, expr* b) {
            expr* args[2] = { a, b };
            return expr_ref(m.mk_app(f.get(), 2, args), m);
        }

        euf::enode* node(expr* e) {
            if (auto* n = g.find(e))
                return n;
            euf::enode_vector args;
            for (expr* arg : *to_app(e))
                args.push_back(node(arg));
            auto* n = g.mk(e, 0, args.size(), args.data());
            g.add_th_var(n, next_var++, user_sort_family_id);
            return n;
        }
    };

    void test_associative_not_commutative() {
        assoc_test t;
        expr_ref a = t.constant("a"), b = t.constant("b"), c = t.constant("c");
        expr_ref ab = t.app(a, b), ba = t.app(b, a);
        expr_ref ab_c = t.app(ab, c), a_bc = t.app(a, t.app(b, c));
        auto* n_ab = t.node(ab);
        auto* n_ba = t.node(ba);
        auto* n_ab_c = t.node(ab_c);
        auto* n_a_bc = t.node(a_bc);
        t.g.propagate();
        ENSURE(n_ab_c->get_root() == n_a_bc->get_root());
        ENSURE(n_ab->get_root() != n_ba->get_root());
    }

    void test_simplification() {
        assoc_test t;
        expr_ref x = t.constant("x"), a = t.constant("a"), b = t.constant("b"), c = t.constant("c");
        expr_ref ab = t.app(a, b);
        expr_ref xc = t.app(x, c);
        expr_ref abc = t.app(ab, c);
        auto* n_x = t.node(x);
        auto* n_ab = t.node(ab);
        auto* n_xc = t.node(xc);
        auto* n_abc = t.node(abc);
        t.g.merge(n_x, n_ab, nullptr);
        t.g.propagate();
        ENSURE(n_xc->get_root() == n_abc->get_root());
    }

    void test_completion() {
        assoc_test t;
        expr_ref a = t.constant("a"), b = t.constant("b"), c = t.constant("c");
        expr_ref u = t.constant("u"), v = t.constant("v");
        expr_ref ab = t.app(a, b), bc = t.app(b, c);
        expr_ref uc = t.app(u, c), av = t.app(a, v);
        auto* n_ab = t.node(ab);
        auto* n_bc = t.node(bc);
        auto* n_u = t.node(u);
        auto* n_v = t.node(v);
        auto* n_uc = t.node(uc);
        auto* n_av = t.node(av);
        t.g.merge(n_ab, n_u, nullptr);
        t.g.merge(n_bc, n_v, nullptr);
        t.g.propagate();
        ENSURE(n_uc->get_root() == n_av->get_root());
        ENSURE(t.p->num_rules() >= 3);
    }

    void test_completion_bound() {
        assoc_test t(2);
        expr_ref a = t.constant("a"), b = t.constant("b"), c = t.constant("c");
        expr_ref u = t.constant("u"), v = t.constant("v");
        auto* n_ab = t.node(t.app(a, b));
        auto* n_bc = t.node(t.app(b, c));
        auto* n_u = t.node(u);
        auto* n_v = t.node(v);
        t.g.merge(n_ab, n_u, nullptr);
        t.g.merge(n_bc, n_v, nullptr);
        t.g.propagate();
        ENSURE(t.p->num_rules() == 2);
    }

    void test_backtracking() {
        assoc_test t;
        expr_ref x = t.constant("x"), a = t.constant("a"), b = t.constant("b"), c = t.constant("c");
        auto* n_x = t.node(x);
        auto* n_ab = t.node(t.app(a, b));
        auto* n_xc = t.node(t.app(x, c));
        auto* n_abc = t.node(t.app(t.app(a, b), c));
        t.g.propagate();
        ENSURE(n_xc->get_root() != n_abc->get_root());
        t.g.push();
        t.g.merge(n_x, n_ab, nullptr);
        t.g.propagate();
        ENSURE(n_xc->get_root() == n_abc->get_root());
        t.g.pop(1);
        ENSURE(n_xc->get_root() != n_abc->get_root());
        ENSURE(t.p->num_rules() == 0);
    }
}

void tst_euf_assoc_plugin() {
    test_associative_not_commutative();
    test_simplification();
    test_completion();
    test_completion_bound();
    test_backtracking();
}
