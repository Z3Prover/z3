/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion.cpp

Abstract:

    Ground completion for equalities

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

Notes:

Create a congruence closure of E.
Select _simplest_ term in each equivalence class. A term is _simplest_
if it is smallest in a well-order, such as a ground Knuth-Bendix order.
A basic approach is terms that are of smallest depth, are values can be chosen as simplest.
Ties between equal-depth terms can be resolved arbitrarily.

Algorithm for extracting canonical form from an E-graph:

* Compute function canon(t) that maps every term in E to a canonical, least with respect to well-order relative to the congruence closure.
  That is, terms that are equal modulo the congruence closure have the same canonical representative.

* Each f(t) = g(s) in E:
  * add f(canon(t)) = canon(f(t)), g(canon(s)) = canon(g(s)) where canon(f(t)) = canon(g(s)) by construction.

* Each other g(t) in E:
  * add g(canon(t)) to E.
  * Note that canon(g(t)) = true because g(t) = true is added to congruence closure of E.
* We claim the new formula is equivalent.
* The dependencies for each rewrite can be computed by following the equality justification data-structure.

Conditional saturation:
- forall X . Body => Head
- propagate when (all assertions in) Body is merged with True
- insert expressions from Body into a watch list.
  When elements of the watch list are merged by true/false
  trigger rep-propagation with respect to body.


Mam optimization?
   match(p, t, S) = suppose all variables in p are bound in S, check equality using canonization of p[S], otherwise prune instances from S.

--*/

#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/euf/euf_egraph.h"
#include "ast/rewriter/var_subst.h"
#include "ast/simplifiers/euf_completion.h"
#include "ast/shared_occs.h"
#include "params/smt_params_helper.hpp"

namespace euf {

    completion::completion(ast_manager& m, dependent_expr_state& fmls) :
        dependent_expr_simplifier(m, fmls),
        m_egraph(m),
        m_mam(mam::mk(*this, *this)),
        m_canonical(m),
        m_eargs(m),
        m_deps(m),
        m_rewriter(m) {
        m_tt = m_egraph.mk(m.mk_true(), 0, 0, nullptr);
        m_ff = m_egraph.mk(m.mk_false(), 0, 0, nullptr);
        m_rewriter.set_order_eq(true);
        m_rewriter.set_flat_and_or(false);

        std::function<void(euf::enode*, euf::enode*)> _on_merge =
            [&](euf::enode* root, euf::enode* other) {
            m_mam->on_merge(root, other);
            watch_rule(root, other);
            };

        std::function<void(euf::enode*)> _on_make =
            [&](euf::enode* n) {
            m_mam->add_node(n, false);
            };

        m_egraph.set_on_merge(_on_merge);
        m_egraph.set_on_make(_on_make);
    }

    completion::~completion() {
    }

    bool completion::should_stop() {
        return
            !m.inc() ||
            m_egraph.inconsistent() ||
            m_fmls.inconsistent() ||
            resource_limits_exceeded();
    }

    void completion::updt_params(params_ref const& p) {
        smt_params_helper sp(p);
        m_max_instantiations = sp.qi_max_instances();
    }

    struct completion::push_watch_rule : public trail {
        vector<ptr_vector<conditional_rule>>& m_rules;
        unsigned idx;
        push_watch_rule(vector<ptr_vector<conditional_rule>>& r, unsigned i) : m_rules(r), idx(i) {}
        void undo() override {
            m_rules[idx].pop_back();
        }
    };

    struct completion::scoped_generation {
        completion& c;
        unsigned m_generation = 0;
        scoped_generation(completion& c, unsigned g): c(c) {
            m_generation = c.m_generation;
            c.m_generation = g;
        }
        ~scoped_generation() {
            c.m_generation = m_generation;
        }
    };

    void completion::push() {
        if (m_side_condition_solver)
            m_side_condition_solver->push();
        m_egraph.push();
        dependent_expr_simplifier::push();
    }

    void completion::pop(unsigned n) {
        clear_propagation_queue();
        dependent_expr_simplifier::pop(n);
        m_egraph.pop(n);
        if (m_side_condition_solver)
            m_side_condition_solver->pop(n);
    }

    void completion::clear_propagation_queue() {
        for (auto r : m_propagation_queue)
            r->m_in_queue = false;
        m_propagation_queue.reset();
    }

    void completion::watch_rule(enode* root, enode* other) {
        auto oid = other->get_id();
        if (oid >= m_rule_watch.size())
            return;
        if (m_rule_watch[oid].empty())
            return;
        auto is_true_or_false = m.is_true(root->get_expr()) || m.is_false(root->get_expr());
        if (is_true_or_false) {
            for (auto r : m_rule_watch[oid])
                if (!r->m_in_queue)
                    r->m_in_queue = true,
                    m_propagation_queue.push_back(r);
        }
        else {
            // root is not true or false, use root to watch rules
            auto rid = root->get_id();
            m_rule_watch.reserve(rid + 1);
            for (auto r : m_rule_watch[oid]) {
                m_rule_watch[rid].push_back(r);
                get_trail().push(push_watch_rule(m_rule_watch, rid));
            }
        }
    }

    void completion::reduce() {
        m_has_new_eq = true;
        for (unsigned rounds = 0; m_has_new_eq && rounds <= 3 && !should_stop(); ++rounds) {
            ++m_epoch;
            m_has_new_eq = false;
            add_egraph();
            map_canonical();
            read_egraph();
            IF_VERBOSE(11, verbose_stream() << "(euf.completion :rounds " << rounds << ")\n");
        }
    }

    void completion::add_egraph() {
        m_nodes_to_canonize.reset();
        unsigned sz = qtail();

        for (unsigned i = qhead(); i < sz; ++i) {
            auto [f, p, d] = m_fmls[i]();
            add_constraint(f, d);
        }
        m_should_propagate = true;
        while (m_should_propagate && !should_stop()) {
            m_should_propagate = false;
            m_egraph.propagate();
            m_mam->propagate();
            propagate_rules();
            IF_VERBOSE(11, verbose_stream() << "propagate " << m_stats.m_num_instances << "\n");
            if (!m_should_propagate)
                propagate_all_rules();
        }
    }

    void completion::add_constraint(expr* f, expr_dependency* d) {
        if (m_egraph.inconsistent())
            return;
        auto add_children = [&](enode* n) {
            for (auto* ch : enode_args(n))
                m_nodes_to_canonize.push_back(ch);
            };
        expr* x, * y;
        if (m.is_eq(f, x, y)) {
            enode* a = mk_enode(x);
            enode* b = mk_enode(y);
            m_egraph.merge(a, b, d);
            add_children(a);
            add_children(b);
        }
        else if (m.is_not(f, f)) {
            enode* n = mk_enode(f);
            m_egraph.merge(n, m_ff, d);
            add_children(n);
        }
        else {
            enode* n = mk_enode(f);
            m_egraph.merge(n, m_tt, d);
            add_children(n);
            if (is_forall(f)) {
                quantifier* q = to_quantifier(f);
                ptr_vector<app> ground;
                for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                    auto p = to_app(q->get_pattern(i));
                    mam::ground_subterms(p, ground);
                    for (expr* g : ground)
                        mk_enode(g);
                    m_mam->add_pattern(q, p);
                }
                if (!get_dependency(q)) {
                    m_q2dep.insert(q, d);
                    get_trail().push(insert_obj_map(m_q2dep, q));
                }
            }
            add_rule(f, d);
        }
        if (m_side_condition_solver)
            m_side_condition_solver->add_constraint(f, d);
    }

    lbool completion::eval_cond(expr* f, expr_dependency*& d) {
        auto n = mk_enode(f);
        if (m.is_true(n->get_root()->get_expr())) {
            d = m.mk_join(d, explain_eq(n, n->get_root()));
            return l_true;
        }
        if (m.is_false(n->get_root()->get_expr()))
            return l_false;

        expr* g = nullptr;
        if (m.is_not(f, g)) {
            n = mk_enode(g);
            if (m.is_false(n->get_root()->get_expr())) {
                d = m.mk_join(d, explain_eq(n, n->get_root()));
                return l_true;
            }
            if (m.is_true(n->get_root()->get_expr()))
                return l_false;
        }
        if (m_side_condition_solver) {
            expr_dependency* sd = nullptr;
            if (m_side_condition_solver->is_true(f, sd)) {
                add_constraint(f, sd);
                d = m.mk_join(d, sd);
                return l_true;
            }
        }
        return l_undef;
    }

    void completion::add_rule(expr* f, expr_dependency* d) {
        expr* x = nullptr, * y = nullptr;
        if (!m.is_implies(f, x, y))
            return;
        expr_ref_vector body(m);
        expr_ref head(y, m);
        body.push_back(x);
        flatten_and(body);
        unsigned j = 0;
        for (auto f : body) {
            switch (eval_cond(f, d)) {
            case l_true:
                break;
            case l_false:
                return;
            case l_undef:
                body[j++] = f;
                break;
            }
        }
        body.shrink(j);
        if (body.empty())
            add_constraint(head, d);
        else {
            euf::enode_vector _body;
            for (auto* f : body)
                _body.push_back(m_egraph.find(f)->get_root());
            auto r = alloc(conditional_rule, _body, head, d);
            m_rules.push_back(r);
            get_trail().push(new_obj_trail(r));
            get_trail().push(push_back_vector(m_rules));
            insert_watch(_body[0], r);
        }
    }

    void completion::insert_watch(enode* n, conditional_rule* r) {
        n = n->get_root();
        if (m.is_not(n->get_expr()))
            n = n->get_arg(0)->get_root();
        m_rule_watch.reserve(n->get_id() + 1);
        m_rule_watch[n->get_id()].push_back(r);
        get_trail().push(push_watch_rule(m_rule_watch, n->get_id()));
    }

    void completion::propagate_all_rules() {
        for (auto* r : m_rules)
            if (!r->m_in_queue)
                r->m_in_queue = true,
                m_propagation_queue.push_back(r);
        propagate_rules();
    }

    void completion::propagate_rules() {
        for (unsigned i = 0; i < m_propagation_queue.size() && !should_stop(); ++i) {
            auto r = m_propagation_queue[i];
            r->m_in_queue = false;
            propagate_rule(*r);
        }
        clear_propagation_queue();
    }

    void completion::propagate_rule(conditional_rule& r) {
        if (!r.m_active)
            return;
        for (unsigned i = r.m_watch_index; i < r.m_body.size(); ++i) {
            auto* f = r.m_body.get(i);       
            switch (eval_cond(f->get_expr(), r.m_dep)) {
            case l_true:
                get_trail().push(value_trail(r.m_watch_index));
                ++r.m_watch_index;
                break;
            case l_false:
                get_trail().push(value_trail(r.m_active));
                r.m_active = false;
                return;
            default:
                insert_watch(f, &r);
                return;                
            }
        }
        if (r.m_body.empty()) {
            add_constraint(r.m_head, r.m_dep);
            get_trail().push(value_trail(r.m_active));
            r.m_active = false;
        }
    }

    // callback when mam finds a binding
    void completion::on_binding(quantifier* q, app* pat, enode* const* binding, unsigned mg, unsigned ming, unsigned mx) {
        if (m_egraph.inconsistent())
            return;
        var_subst subst(m);
        expr_ref_vector _binding(m);
        unsigned max_generation = 0;
        for (unsigned i = 0; i < q->get_num_decls(); ++i) {
            _binding.push_back(binding[i]->get_expr());
            max_generation = std::max(max_generation, binding[i]->generation());
        }
        expr_ref r = subst(q->get_expr(), _binding);
        IF_VERBOSE(12, verbose_stream() << "add " << r << "\n");

        scoped_generation sg(*this, max_generation + 1);
        add_constraint(r, get_dependency(q));
        propagate_rules();
        m_should_propagate = true;
        ++m_stats.m_num_instances;
    }

    void completion::read_egraph() {
        if (m_egraph.inconsistent()) {
            auto* d = explain_conflict();
            dependent_expr de(m, m.mk_false(), nullptr, d);
            m_fmls.update(0, de);
            return;
        }
        unsigned sz = qtail();
        for (unsigned i = qhead(); i < sz; ++i) {
            auto [f, p, d] = m_fmls[i]();
            expr_dependency_ref dep(d, m);
            expr_ref g = canonize_fml(f, dep);
            if (g != f) {
                m_fmls.update(i, dependent_expr(m, g, nullptr, dep));
                m_stats.m_num_rewrites++;
                IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(f, m, 3) << " -> " << mk_bounded_pp(g, m, 3) << "\n");
                update_has_new_eq(g);
            }
            CTRACE(euf_completion, g != f, tout << mk_bounded_pp(f, m) << " -> " << mk_bounded_pp(g, m) << "\n");
        }
    }

    bool completion::is_new_eq(expr* a, expr* b) {
        enode* na = m_egraph.find(a);
        enode* nb = m_egraph.find(b);
        if (!na)
            IF_VERBOSE(11, verbose_stream() << "not internalied " << mk_bounded_pp(a, m) << "\n");
        if (!nb)
            IF_VERBOSE(11, verbose_stream() << "not internalied " << mk_bounded_pp(b, m) << "\n");
        if (na && nb && na->get_root() != nb->get_root())
            IF_VERBOSE(11, verbose_stream() << m_egraph.bpp(na) << " " << m_egraph.bpp(nb) << "\n");
        return !na || !nb || na->get_root() != nb->get_root();
    }

    void completion::update_has_new_eq(expr* g) {
        expr* x, * y;
        if (m_has_new_eq)
            return;
        else if (m.is_eq(g, x, y))
            m_has_new_eq |= is_new_eq(x, y);
        else if (m.is_and(g)) {
            for (expr* arg : *to_app(g))
                update_has_new_eq(arg);
        }
        else if (m.is_not(g, g))
            m_has_new_eq |= is_new_eq(g, m.mk_false());
        else
            m_has_new_eq |= is_new_eq(g, m.mk_true());
    }

    enode* completion::mk_enode(expr* e) {
        m_todo.push_back(e);
        enode* n;
        while (!m_todo.empty()) {
            e = m_todo.back();
            if (m_egraph.find(e)) {
                m_todo.pop_back();
                continue;
            }
            if (!is_app(e)) {
                m_nodes_to_canonize.push_back(m_egraph.mk(e, m_generation, 0, nullptr));
                m_todo.pop_back();
                continue;
            }
            m_args.reset();
            unsigned sz = m_todo.size();
            for (expr* arg : *to_app(e)) {
                n = m_egraph.find(arg);
                if (n)
                    m_args.push_back(n);
                else
                    m_todo.push_back(arg);
            }
            if (sz == m_todo.size()) {
                m_nodes_to_canonize.push_back(m_egraph.mk(e, m_generation, m_args.size(), m_args.data()));
                m_todo.pop_back();
            }
        }
        return m_egraph.find(e);
    }

    expr_ref completion::canonize_fml(expr* f, expr_dependency_ref& d) {

        auto is_nullary = [&](expr* e) {
            return is_app(e) && to_app(e)->get_num_args() == 0;
            };
        expr* x, * y;
        if (m.is_eq(f, x, y)) {
            expr_ref x1 = canonize(x, d);
            expr_ref y1 = canonize(y, d);

            if (is_nullary(x)) {
                SASSERT(x1 == x);
                x1 = get_canonical(x, d);
            }
            if (is_nullary(y)) {
                SASSERT(y1 == y);
                y1 = get_canonical(y, d);
            }

            if (x == y)
                return expr_ref(m.mk_true(), m);

            if (x == x1 && y == y1)
                return m_rewriter.mk_eq(x, y);

            if (is_nullary(x) && is_nullary(y))
                return mk_and(m_rewriter.mk_eq(x, x1), m_rewriter.mk_eq(y, x1));

            if (x == x1 && is_nullary(x))
                return m_rewriter.mk_eq(y1, x1);

            if (y == y1 && is_nullary(y))
                return m_rewriter.mk_eq(x1, y1);

            if (is_nullary(x))
                return mk_and(m_rewriter.mk_eq(x, x1), m_rewriter.mk_eq(y1, x1));

            if (is_nullary(y))
                return mk_and(m_rewriter.mk_eq(y, y1), m_rewriter.mk_eq(x1, y1));

            if (x1 == y1)
                return expr_ref(m.mk_true(), m);
            else {
                expr* c = get_canonical(x, d);
                if (c == x1)
                    return m_rewriter.mk_eq(y1, c);
                else if (c == y1)
                    return m_rewriter.mk_eq(x1, c);
                else
                    return mk_and(m_rewriter.mk_eq(x1, c), m_rewriter.mk_eq(y1, c));
            }
        }

        if (m.is_not(f, x)) {
            expr_ref x1 = canonize(x, d);
            return expr_ref(mk_not(m, x1), m);
        }

        return canonize(f, d);
    }

    expr_ref completion::mk_and(expr* a, expr* b) {
        if (m.is_true(a))
            return expr_ref(b, m);
        if (m.is_true(b))
            return expr_ref(a, m);
        return expr_ref(m.mk_and(a, b), m);
    }

    expr_ref completion::canonize(expr* f, expr_dependency_ref& d) {
        if (!is_app(f))
            return expr_ref(f, m); // todo could normalize ground expressions under quantifiers

        m_eargs.reset();
        bool change = false;
        for (expr* arg : *to_app(f)) {
            m_eargs.push_back(get_canonical(arg, d));
            change |= arg != m_eargs.back();
        }
        if (m.is_eq(f))
            return m_rewriter.mk_eq(m_eargs.get(0), m_eargs.get(1));
        if (!change)
            return expr_ref(f, m);
        else
            return expr_ref(m_rewriter.mk_app(to_app(f)->get_decl(), m_eargs.size(), m_eargs.data()), m);
    }

    expr* completion::get_canonical(expr* f, expr_dependency_ref& d) {
        enode* n = m_egraph.find(f);
        enode* r = n->get_root();
        d = m.mk_join(d, explain_eq(n, r));
        d = m.mk_join(d, m_deps.get(r->get_id(), nullptr));
        SASSERT(m_canonical.get(r->get_id()));
        return m_canonical.get(r->get_id());
    }

    expr* completion::get_canonical(enode* n) {
        if (m_epochs.get(n->get_id(), 0) == m_epoch)
            return m_canonical.get(n->get_id());
        else
            return nullptr;
    }

    void completion::set_canonical(enode* n, expr* e) {
        class vtrail : public trail {
            expr_ref_vector& c;
            unsigned idx;
            expr_ref old_value;
        public:
            vtrail(expr_ref_vector& c, unsigned idx) :
                c(c), idx(idx), old_value(c.get(idx), c.m()) {
            }

            void undo() override {
                c[idx] = old_value;
                old_value = nullptr;
            }
        };
        SASSERT(e);
        if (num_scopes() > 0 && m_canonical.size() > n->get_id())
            m_trail.push(vtrail(m_canonical, n->get_id()));
        m_canonical.setx(n->get_id(), e);
        m_epochs.setx(n->get_id(), m_epoch, 0);
    }

    expr_dependency* completion::explain_eq(enode* a, enode* b) {
        if (a == b)
            return nullptr;
        ptr_vector<expr_dependency> just;
        m_egraph.begin_explain();
        m_egraph.explain_eq(just, nullptr, a, b);
        m_egraph.end_explain();
        expr_dependency* d = nullptr;
        for (expr_dependency* d2 : just)
            d = m.mk_join(d, d2);
        return d;
    }

    expr_dependency* completion::explain_conflict() {
        ptr_vector<expr_dependency> just;
        m_egraph.begin_explain();
        m_egraph.explain(just, nullptr);
        m_egraph.end_explain();
        expr_dependency* d = nullptr;
        for (expr_dependency* d2 : just)
            d = m.mk_join(d, d2);
        return d;
    }

    void completion::collect_statistics(statistics& st) const {
        st.update("euf-completion-rewrites", m_stats.m_num_rewrites);
        st.update("euf-completion-instances", m_stats.m_num_instances);
    }

    bool completion::is_gt(expr* lhs, expr* rhs) const {
        if (lhs == rhs)
            return false;
        // values are always less in ordering than non-values.
        bool v1 = m.is_value(lhs);
        bool v2 = m.is_value(rhs);
        if (!v1 && v2)
            return true;
        if (v1 && !v2)
            return false;

        if (get_depth(lhs) > get_depth(rhs))
            return true;
        if (get_depth(lhs) < get_depth(rhs))
            return false;

        // slow path
        auto n1 = get_num_exprs(lhs);
        auto n2 = get_num_exprs(rhs);
        if (n1 > n2)
            return true;
        if (n1 < n2)
            return false;

        if (is_app(lhs) && is_app(rhs)) {
            app* l = to_app(lhs);
            app* r = to_app(rhs);
            if (l->get_decl()->get_id() != r->get_decl()->get_id())
                return l->get_decl()->get_id() > r->get_decl()->get_id();
            if (l->get_num_args() != r->get_num_args())
                return l->get_num_args() > r->get_num_args();
            for (unsigned i = 0; i < l->get_num_args(); ++i)
                if (l->get_arg(i) != r->get_arg(i))
                    return is_gt(l->get_arg(i), r->get_arg(i));
            UNREACHABLE();
        }
        if (is_quantifier(lhs) && is_quantifier(rhs)) {
            expr* l = to_quantifier(lhs)->get_expr();
            expr* r = to_quantifier(rhs)->get_expr();
            return is_gt(l, r);
        }
        if (is_quantifier(lhs))
            return true;
        return false;
    }

    void completion::map_canonical() {
        m_todo.reset();
        enode_vector roots;
        if (m_nodes_to_canonize.empty())
            return;
        for (unsigned i = 0; i < m_nodes_to_canonize.size(); ++i) {
            enode* n = m_nodes_to_canonize[i]->get_root();
            if (n->is_marked1())
                continue;
            n->mark1();
            roots.push_back(n);
            enode* rep = nullptr;
            for (enode* k : enode_class(n))
                if (!rep || m.is_value(k->get_expr()) || is_gt(rep->get_expr(), k->get_expr()))
                    rep = k;
            // IF_VERBOSE(0, verbose_stream() << m_egraph.bpp(n) << " ->\n" << m_egraph.bpp(rep) << "\n";);
            m_reps.setx(n->get_id(), rep, nullptr);

            TRACE(euf_completion, tout << "rep " << m_egraph.bpp(n) << " -> " << m_egraph.bpp(rep) << "\n";
            for (enode* k : enode_class(n)) tout << m_egraph.bpp(k) << "\n";);
            m_todo.push_back(n->get_expr());
            for (enode* arg : enode_args(n)) {
                arg = arg->get_root();
                if (!arg->is_marked1())
                    m_nodes_to_canonize.push_back(arg);
            }
        }
        for (enode* r : roots)
            r->unmark1();

        // explain dependencies when no nodes are marked.
        // explain_eq uses both mark1 and mark2 on e-nodes so 
        // we cannot call it inside the previous loop where mark1 is used
        // to track which roots have been processed.
        for (enode* r : roots) {
            enode* rep = m_reps[r->get_id()];
            auto* d = explain_eq(r, rep);
            m_deps.setx(r->get_id(), d);
        }
        expr_ref new_expr(m);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            enode* n = m_egraph.find(e);
            SASSERT(n->is_root());
            enode* rep = m_reps[n->get_id()];
            if (get_canonical(n))
                m_todo.pop_back();
            else if (get_depth(rep->get_expr()) == 0 || !is_app(rep->get_expr())) {
                set_canonical(n, rep->get_expr());
                m_todo.pop_back();
            }
            else {
                m_eargs.reset();
                unsigned sz = m_todo.size();
                bool new_arg = false;
                expr_dependency* d = m_deps.get(n->get_id(), nullptr);
                for (enode* arg : enode_args(rep)) {
                    enode* rarg = arg->get_root();
                    expr* c = get_canonical(rarg);
                    if (c) {
                        m_eargs.push_back(c);
                        new_arg |= c != arg->get_expr();
                        d = m.mk_join(d, m_deps.get(rarg->get_id(), nullptr));
                    }
                    else
                        m_todo.push_back(rarg->get_expr());
                }
                if (sz == m_todo.size()) {
                    m_todo.pop_back();
                    if (new_arg)
                        new_expr = m_rewriter.mk_app(to_app(rep->get_expr())->get_decl(), m_eargs.size(), m_eargs.data());
                    else
                        new_expr = rep->get_expr();
                    set_canonical(n, new_expr);
                    m_deps.setx(n->get_id(), d);
                }
            }
        }
    }
}