/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "util/util.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_seq_plugin.h"
#include "ast/reg_decl_plugins.h"

namespace {

    class seq_euf_test {
        ast_manager m;
        seq_util seq;
        euf::egraph g;
        unsigned next_var = 0;

        static ast_manager& initialize(ast_manager& m) {
            reg_decl_plugins(m);
            return m;
        }

        euf::enode* node_core(expr* e) {
            if (auto* n = g.find(e))
                return n;
            euf::enode_vector args;
            for (expr* arg : *to_app(e))
                args.push_back(node_core(arg));
            auto* n = g.mk(e, 0, args.size(), args.data());
            if (seq.is_seq(e))
                g.add_th_var(n, next_var++, seq.get_family_id());
            return n;
        }

    public:
        seq_euf_test():
            seq(initialize(m)),
            g(m) {
            g.add_plugin(alloc(euf::seq_plugin, g));
        }

        expr_ref variable(char const* name, sort* s) {
            return expr_ref(m.mk_const(symbol(name), s), m);
        }

        expr_ref unit(expr* e) {
            return expr_ref(seq.str.mk_unit(e), m);
        }

        expr_ref concat(expr* a, expr* b) {
            return expr_ref(seq.str.mk_concat(a, b), m);
        }

        sort* element_sort() { return m.mk_uninterpreted_sort(symbol("E")); }
        sort* sequence_sort(sort* e) { return seq.str.mk_seq(e); }
        euf::enode* node(expr* e) { return node_core(e); }
        euf::egraph& egraph() { return g; }
    };

    void test_sequence_associativity() {
        seq_euf_test t;
        sort* e = t.element_sort();
        expr_ref ea = t.variable("a", e), eb = t.variable("b", e), ec = t.variable("c", e);
        expr_ref a = t.unit(ea), b = t.unit(eb), c = t.unit(ec);
        auto* left = t.node(t.concat(t.concat(a, b), c));
        auto* right = t.node(t.concat(a, t.concat(b, c)));
        auto* ab = t.node(t.concat(a, b));
        auto* ba = t.node(t.concat(b, a));
        t.egraph().propagate();
        ENSURE(left->get_root() == right->get_root());
        ENSURE(ab->get_root() != ba->get_root());
    }

    void test_sequence_completion() {
        seq_euf_test t;
        sort* e = t.element_sort();
        expr_ref ea = t.variable("a", e), eb = t.variable("b", e), ec = t.variable("c", e);
        expr_ref eu = t.variable("u", e), ev = t.variable("v", e);
        expr_ref a = t.unit(ea), b = t.unit(eb), c = t.unit(ec);
        expr_ref u = t.unit(eu), v = t.unit(ev);
        auto* ab = t.node(t.concat(a, b));
        auto* bc = t.node(t.concat(b, c));
        auto* nu = t.node(u);
        auto* nv = t.node(v);
        auto* uc = t.node(t.concat(u, c));
        auto* av = t.node(t.concat(a, v));
        t.egraph().merge(ab, nu, nullptr);
        t.egraph().merge(bc, nv, nullptr);
        t.egraph().propagate();
        ENSURE(uc->get_root() == av->get_root());
    }

    void test_sequence_variable_simplification() {
        seq_euf_test t;
        sort* e = t.element_sort();
        sort* s = t.sequence_sort(e);
        expr_ref ea = t.variable("a", e), eb = t.variable("b", e), ec = t.variable("c", e);
        expr_ref a = t.unit(ea), b = t.unit(eb), c = t.unit(ec);
        expr_ref x = t.variable("x", s);
        auto* nx = t.node(x);
        auto* ab = t.node(t.concat(a, b));
        auto* xc = t.node(t.concat(x, c));
        auto* abc = t.node(t.concat(t.concat(a, b), c));
        t.egraph().merge(nx, ab, nullptr);
        t.egraph().propagate();
        ENSURE(xc->get_root() == abc->get_root());
    }

    void test_sequence_backtracking() {
        seq_euf_test t;
        sort* e = t.element_sort();
        sort* s = t.sequence_sort(e);
        expr_ref ea = t.variable("a", e), eb = t.variable("b", e), ec = t.variable("c", e);
        expr_ref a = t.unit(ea), b = t.unit(eb), c = t.unit(ec);
        expr_ref x = t.variable("x", s);
        auto* nx = t.node(x);
        auto* ab = t.node(t.concat(a, b));
        auto* xc = t.node(t.concat(x, c));
        auto* abc = t.node(t.concat(t.concat(a, b), c));
        t.egraph().propagate();
        ENSURE(xc->get_root() != abc->get_root());
        t.egraph().push();
        t.egraph().merge(nx, ab, nullptr);
        t.egraph().propagate();
        ENSURE(xc->get_root() == abc->get_root());
        t.egraph().pop(1);
        ENSURE(xc->get_root() != abc->get_root());
    }
}

void tst_euf_seq_plugin() {
    test_sequence_associativity();
    test_sequence_completion();
    test_sequence_variable_simplification();
    test_sequence_backtracking();
}
