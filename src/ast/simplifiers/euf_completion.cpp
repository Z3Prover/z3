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
#include "ast/expr_abstract.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_arith_plugin.h"
#include "ast/euf/euf_bv_plugin.h"
#include "ast/rewriter/var_subst.h"
#include "ast/simplifiers/euf_completion.h"
#include "ast/shared_occs.h"
#include "ast/scoped_proof.h"
#include "params/smt_params_helper.hpp"

namespace euf {

    completion::completion(ast_manager& m, dependent_expr_state& fmls) :
        dependent_expr_simplifier(m, fmls),
        m_egraph(m),
        m_mam(mam::mk(*this, *this)),
        m_canonical(m),
        m_eargs(m),
        m_expr_trail(m),
        m_consequences(m),
        m_canonical_proofs(m),
        // m_infer_patterns(m, m_smt_params),
        m_deps(m),
        m_rewriter(m),
        m_matcher(m, m_trail) {
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

        m_egraph.add_plugin(alloc(arith_plugin, m_egraph));
        m_egraph.add_plugin(alloc(bv_plugin, m_egraph));

        std::function<void(ho_subst&)> on_match =
            [&](ho_subst& s) {
            IF_VERBOSE(1, s.display(verbose_stream() << "on-match\n") << "\n");
            auto& b = *m_ho_binding;
            auto* hoq = b.m_q;
            auto* q = m_matcher.hoq2q(hoq);
            // shrink binding
            expr_ref_vector binding(m);
            for (unsigned i = 0; i < s.size(); ++i)
                binding.push_back(s.get(i));
            
            if (binding.size() > q->get_num_decls()) {
                bool change = true;
                while (change) {
                    change = false;
                    for (unsigned i = 1; i < binding.size();) {
                        var_subst sub(m);
                        auto r = sub(binding.get(i), binding);
                        change |= r != binding.get(i);
                        m_rewriter(r);
                        binding[i] = r;
                    }
                }
                binding.reverse();
                binding.shrink(q->get_num_decls());
                binding.reverse();
            }
            else {
                for (unsigned i = 0; i < binding.size();) {
                    expr_ref r(binding.get(i), m);
                    m_rewriter(r);
                    binding[i] = r;
                }
            }

            IF_VERBOSE(1, verbose_stream() << binding << "\n");
            apply_binding(b, q, binding);
            };

        m_matcher.set_on_match(on_match);

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
        // m_max_generation = sp.qi_max_generation();
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
            IF_VERBOSE(1, verbose_stream() << "(euf.completion :rounds " << rounds << " :instances " << m_stats.m_num_instances << " :stop " << should_stop() << ")\n");
        }
        map_congruences();
        for (auto c : m_consequences)
            add_consequence(c);

        TRACE(euf_completion, m_egraph.display(tout));
    }

    void completion::map_congruences() {
        unsigned sz = qtail();
        for (unsigned i = qhead(); i < sz; ++i) {
            auto [f, p, d] = m_fmls[i]();
            if (is_app(f) && to_app(f)->get_num_args() == 1 && symbol("congruences") == to_app(f)->get_decl()->get_name())
                map_congruence(to_app(f)->get_arg(0));
        }
    }

    void completion::map_congruence(expr* t) {
        auto n = m_egraph.find(t);
        if (!n)
            return;
        expr_ref_vector args(m);
        expr_mark visited;
        for (auto s : enode_class(n)) {
            expr_ref r(s->get_expr(), m);
            m_rewriter(r);
            if (visited.is_marked(r))
                continue;
            visited.mark(r);
            args.push_back(r);
        }
        expr_ref cong(m);
        cong = m.mk_app(symbol("congruence"), args.size(), args.data(), m.mk_bool_sort());
        m_fmls.add(dependent_expr(m, cong, nullptr, nullptr));        
    }

    void completion::add_consequence(expr* f) {
        expr_ref r(f, m);
        m_rewriter(r);
        f = r.get();
        auto cons = m.mk_app(symbol("consequence"), 1, &f, m.mk_bool_sort());
        m_fmls.add(dependent_expr(m, cons, nullptr, nullptr));
    }

    void completion::add_egraph() {
        m_nodes_to_canonize.reset();
        unsigned sz = qtail();
        for (unsigned i = qhead(); i < sz; ++i) {
            auto [f, p, d] = m_fmls[i]();
            add_constraint(f, p, d);
        }
        m_should_propagate = true;
        while (m_should_propagate && !should_stop()) {
            m_should_propagate = false;
            m_egraph.propagate();
            m_mam->propagate();
            flush_binding_queue();
            propagate_rules();
            propagate_closures();
            IF_VERBOSE(11, verbose_stream() << "propagate " << m_stats.m_num_instances << "\n");
            if (!should_stop())
                propagate_arithmetic();
            if (!m_should_propagate && !should_stop())
                propagate_all_rules();            
        }
        TRACE(euf, m_egraph.display(tout));
    }

    unsigned completion::push_pr_dep(proof* pr, expr_dependency* d) {
        unsigned sz = m_pr_dep.size();
        SASSERT(!m.proofs_enabled() || pr);
        m_pr_dep.push_back({ proof_ref(pr, m), d });
        get_trail().push(push_back_vector(m_pr_dep));
        return sz;
    }

    void completion::add_constraint(expr* f, proof* pr, expr_dependency* d) {
        if (m_egraph.inconsistent())
            return;
        TRACE(euf_completion, tout << mk_pp(f, m) << "\n");
        auto add_children = [&](enode* n) {
            for (auto* ch : enode_args(n))
                m_nodes_to_canonize.push_back(ch);
            };
        expr* x = nullptr, * y = nullptr, * nf = nullptr;
        if (m.is_eq(f, x, y)) {
            expr_ref y1(y, m);
            m_rewriter(y1);

            add_quantifiers(x);
            add_quantifiers(y1);
            enode* a = mk_enode(x);
            enode* b = mk_enode(y1);

            if (a->get_root() == b->get_root())
                return;

            TRACE(euf, tout << "merge and propagate\n");
            add_children(a);
            add_children(b);
            m_egraph.merge(a, b, to_ptr(push_pr_dep(pr, d)));
            m_egraph.propagate();
            m_should_propagate = true; 
            
            if (m_side_condition_solver && a->get_root() != b->get_root())
                m_side_condition_solver->add_constraint(f, pr, d);
            IF_VERBOSE(1, verbose_stream() << "eq: " << a->get_root_id() << " " << b->get_root_id() << " " 
                 << mk_pp(x, m) << " == " << y1 << "\n");
        }
        else if (m.is_not(f, nf)) {
            expr_ref f1(nf, m);
            m_rewriter(f1);
            enode* n = mk_enode(f1);
            if (m.is_false(n->get_root()->get_expr()))
                return;
            add_quantifiers(f1);
            auto n_false = mk_enode(m.mk_false());
            auto j = to_ptr(push_pr_dep(pr, d));
            m_egraph.merge(n, n_false, j);
            m_egraph.propagate();
            add_children(n);
            m_should_propagate = true;
            if (m_side_condition_solver)
                m_side_condition_solver->add_constraint(f, pr, d);
            IF_VERBOSE(1, verbose_stream() << "not: " << nf << "\n");
        }
        else {
            expr_ref f1(f, m);
            if (!m.is_implies(f) && !is_quantifier(f)) {
                m_rewriter(f1);
                f = f1;
            }
            enode* n = mk_enode(f);
            if (m.is_true(n->get_root()->get_expr()))
                return;            
            IF_VERBOSE(1, verbose_stream() << "fml: " << mk_pp(f, m) << "\n");
            m_egraph.merge(n, m_tt, to_ptr(push_pr_dep(pr, d)));
            m_egraph.propagate();
            add_children(n);
            if (is_forall(f)) {
                quantifier* q = to_quantifier(f);
#if 0
                if (q->get_num_patterns() == 0) {
                    expr_ref tmp(m);
                    m_infer_patterns(q, tmp);
                    m_egraph.mk(tmp, 0, 0, nullptr); // ensure tmp is pinned within this scope.
                    q = to_quantifier(tmp);
                }
#endif

                for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                    auto p = to_app(q->get_pattern(i));
                    auto [q1, p1] = m_matcher.compile_ho_pattern(q, p);
                    ptr_vector<app> ground;
                    mam::ground_subterms(p, ground);
                    if (p1 != p)
                        mam::ground_subterms(p1, ground);
                    for (expr* g : ground)
                        mk_enode(g);
                    m_mam->add_pattern(q, p);
                    if (p != p1)
                        m_mam->add_pattern(q1, p1);
                }
                m_q2dep.insert(q, { pr, d });
                get_trail().push(insert_obj_map(m_q2dep, q));
            }

            add_rule(f, pr, d);
            if (!is_forall(f) && !m.is_implies(f) && !m.is_or(f)) {
                add_quantifiers(f);
                if (m_side_condition_solver)
                    m_side_condition_solver->add_constraint(f, pr, d);
            }
        }
    }

    void completion::add_quantifiers(expr* f) {
        if (!has_quantifiers(f))
            return;
        ptr_vector<expr> bound;
        add_quantifiers(bound, f);
    }
    
    void completion::add_quantifiers(ptr_vector<expr>& bound, expr* f) {
        if (!has_quantifiers(f))
            return;

        ptr_vector<expr> todo;
        todo.push_back(f);
        expr_fast_mark1 visited;
        for (unsigned j = 0; j < todo.size(); ++j) {
            expr* t = todo[j];
            if (visited.is_marked(t))
                continue;
            visited.mark(t);
            if (!has_quantifiers(t))
                continue;
            if (is_app(t)) {
                for (auto arg : *to_app(t))
                    todo.push_back(arg);
            }
            else if (is_quantifier(t)) {
                auto q = to_quantifier(t);
                auto nd = q->get_num_decls();
                IF_VERBOSE(1, verbose_stream() << "bind " << mk_pp(q, m) << "\n");
                for (unsigned i = 0; i < nd; ++i) {
                    auto name = std::string("bound!") + std::to_string(bound.size());
                    auto b = m.mk_const(name, q->get_decl_sort(i));
                    if (b->get_ref_count() == 0) {
                        m_expr_trail.push_back(b);
                        get_trail().push(push_back_vector(m_expr_trail));
                    }
                    bound.push_back(b);
                }
                expr_ref inst = var_subst(m)(q->get_expr(), bound);

                if (!m_egraph.find(inst)) {
                    expr_ref clos(m);
                    m_closures.insert(q, { bound, inst });
                    get_trail().push(insert_map(m_closures, q));
                    // ensure that inst occurs in a foreign context to enable equality propagation
                    // on inst.
                    func_decl* f = m.mk_func_decl(symbol("clos!"), inst->get_sort(), m.mk_bool_sort());
                    clos = m.mk_app(f, inst);
                    mk_enode(clos);
                    // TODO: handle nested quantifiers after m_closures is updated to 
                    // index on sort declaration prefix together with quantifier
                    // add_quantifiers(bound, inst);
                }
                bound.shrink(bound.size() - nd);
            }
        }
    }

    lbool completion::eval_cond(expr* f, proof_ref& pr, expr_dependency*& d) {
        auto n = mk_enode(f);
        if (m.is_true(n->get_root()->get_expr())) {
            d = m.mk_join(d, explain_eq(n, n->get_root()));
            if (m.proofs_enabled()) 
                pr = prove_eq(n, n->get_root());
            return l_true;
        }
        if (m.is_false(n->get_root()->get_expr()))
            return l_false;

        expr* g = nullptr;
        if (m.is_not(f, g)) {
            n = mk_enode(g);
            if (m.is_false(n->get_root()->get_expr())) {
                d = m.mk_join(d, explain_eq(n, n->get_root()));
                if (m.proofs_enabled())
                    pr = prove_eq(n, n->get_root());
                return l_true;
            }
            if (m.is_true(n->get_root()->get_expr()))
                return l_false;
        }
        if (m_side_condition_solver && m_propagate_with_solver) {
            expr_dependency* sd = nullptr;
            if (m_side_condition_solver->is_true(f, pr, sd)) {
                add_constraint(f, pr, sd);
                d = m.mk_join(d, sd);
                return l_true;
            }
        }
        return l_undef;
    }

    void completion::add_rule(expr* f, proof* pr, expr_dependency* d) {
        expr* x = nullptr, * y = nullptr;
        expr_ref_vector body(m);
        proof_ref pr_i(m), pr0(m);
        expr_ref_vector prs(m);
        expr_ref head(m);
        if (m.is_implies(f, x, y)) {
            head = y;
            body.push_back(x);
        } 
        else if (m.is_or(f)) {
            for (auto arg : *to_app(f)) {
                if (m.is_eq(arg)) {
                    if (head)
                        return;
                    head = arg;
                }
                else
                    body.push_back(arg);
            }
            if (!head)
                return;
        }
        else 
            return;

        flatten_and(body);
        unsigned j = 0;
        flet<bool> _propagate_with_solver(m_propagate_with_solver, true);
        
        for (auto f : body) {
            switch (eval_cond(f, pr_i, d)) {
            case l_true:
                if (m.proofs_enabled())
                    prs.push_back(pr_i);
                break;
            case l_false:
                return;
            case l_undef:
                body[j++] = f;
                break;
            }
        }
        body.shrink(j);
        if (m.proofs_enabled()) {
            prs.push_back(pr);
            if (body.empty()) {
                prs.push_back(head);
                pr0 = m.mk_app(symbol("rup"), prs.size(), prs.data(), m.mk_proof_sort());
            }
        }
        if (body.empty())
            add_constraint(head, pr0, d);        
        else {
            euf::enode_vector _body;
            for (auto* f : body)
                _body.push_back(m_egraph.find(f)->get_root());
            auto r = alloc(conditional_rule, _body, head, prs, d);
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
        flet<bool> _propagate_with_solver(m_propagate_with_solver, true);
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
        proof_ref pr(m);
        for (unsigned i = r.m_watch_index; i < r.m_body.size(); ++i) {
            auto* f = r.m_body.get(i);    
            switch (eval_cond(f->get_expr(), pr, r.m_dep)) {
            case l_true:
                get_trail().push(value_trail(r.m_watch_index));
                get_trail().push(push_back_vector(r.m_proofs));
                ++r.m_watch_index;
                r.m_proofs.push_back(pr);
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
            if (m.proofs_enabled()) {
                get_trail().push(push_back_vector(r.m_proofs));
                r.m_proofs.push_back(r.m_head);
                pr = m.mk_app(symbol("rup"), r.m_proofs.size(), r.m_proofs.data(), m.mk_proof_sort());
            }
            add_constraint(r.m_head, pr, r.m_dep);
            get_trail().push(value_trail(r.m_active));
            r.m_active = false;
        }
    }

    //
    // extract shared arithmetic terms T
    // extract shared variables V
    // add t = rewriter(t) to E-graph
    // solve for V by solver producing theta
    // add theta to E-graph
    // add theta to canonize (?)
    //
    void completion::propagate_arithmetic() {
        ptr_vector<expr> shared_terms, shared_vars;
        expr_mark visited;
        arith_util a(m);
        bool merged = false;
        for (auto n : m_egraph.nodes()) {
            expr* e = n->get_expr();
            if (!is_app(e))
                continue;
            app* t = to_app(e);
            bool is_arith = a.is_arith_expr(t);
            for (auto arg : *t) {
                bool is_arith_arg = a.is_arith_expr(arg);
                if (is_arith_arg == is_arith)
                    continue;
                if (visited.is_marked(arg))
                    continue;
                visited.mark(arg);
                if (is_arith_arg)
                    shared_terms.push_back(arg);
                else
                    shared_vars.push_back(arg);
            }           
        }
        for (auto t : shared_terms) {
            auto tn = m_egraph.find(t);
            
            if (!tn)
                continue;
            expr_ref r(t, m);
            m_rewriter(r);
            if (r == t)
                continue;
            auto n = m_egraph.find(t);
            auto t_root = tn->get_root();
            if (n && n->get_root() == t_root) 
                continue;
            
            if (!n)
                n = mk_enode(r);
            TRACE(euf_completion, tout << "propagate-arith: " << mk_pp(t, m) << " -> " << r << "\n");
            
            m_egraph.merge(tn, n, nullptr);
            merged = true;
        }
        visited.reset();
        for (auto v : shared_vars) {
            if (visited.is_marked(v))
                continue;
            visited.mark(v);
            vector<side_condition_solver::solution> sol;
            expr_ref term(m), guard(m);
            sol.push_back({ v, term, guard });
            m_side_condition_solver->solve_for(sol);
            for (auto [v, t, g] : sol) {
                if (!t)
                    continue;
                visited.mark(v);
                auto a = mk_enode(v);
                auto b = mk_enode(t);
                if (a->get_root() == b->get_root())
                    continue;
                TRACE(euf_completion, tout << "propagate-arith: " << m_egraph.bpp(a) << " -> " << m_egraph.bpp(b) << "\n");
                IF_VERBOSE(1, verbose_stream() << "propagate-arith: " << m_egraph.bpp(a) << " -> " << m_egraph.bpp(b) << "\n");
                m_egraph.merge(a, b, nullptr); // TODO guard justifies reason.
                merged = true;
            }
        }
        if (merged) {
            m_egraph.propagate();
            m_should_propagate = true;
        }
    }

    void completion::propagate_closures() {
        for (auto [q, clos] : m_closures) {
            expr* body = clos.second;
            auto n = m_egraph.find(body);
            SASSERT(n);
#if 0
            verbose_stream() << "class of " << mk_pp(body, m) << "\n";
            for (auto s : euf::enode_class(n)) {
                verbose_stream() << mk_pp(s->get_expr(), m) << "\n";
            }
#endif
            if (n->is_root())
                continue;
            auto qn = m_egraph.find(q);
#if 0
            verbose_stream() << "class of " << mk_pp(q, m) << "\n";
            for (auto s : euf::enode_class(qn)) {
                verbose_stream() << mk_pp(s->get_expr(), m) << "\n";
            }
#endif
            expr_ref new_body = expr_ref(n->get_root()->get_expr(), m);
            expr_ref new_q = expr_abstract(m, clos.first, new_body);
            new_q = m.update_quantifier(q, new_q);
            auto new_qn = m_egraph.find(new_q);
            if (!new_qn)
                new_qn = m_egraph.mk(new_q, qn->generation(), 0, nullptr);
            if (new_qn->get_root() == qn->get_root())
                continue;
            m_egraph.merge(new_qn, qn, nullptr); // todo track dependencies
            m_should_propagate = true;
        }
    }

    binding* completion::tmp_binding(quantifier* q, app* pat, euf::enode* const* _binding) {
        if (q->get_num_decls() > m_tmp_binding_capacity) {
            void* mem = memory::allocate(sizeof(binding) + q->get_num_decls() * sizeof(euf::enode*));
            m_tmp_binding = new (mem) binding(q, pat, 0, 0, 0);
            m_tmp_binding_capacity = q->get_num_decls();
        }

        for (unsigned i = q->get_num_decls(); i-- > 0; )
            m_tmp_binding->m_nodes[i] = _binding[i];
        m_tmp_binding->m_pattern = pat;
        m_tmp_binding->m_q = q;
        return m_tmp_binding.get();
    }

    binding* completion::alloc_binding(quantifier* q, app* pat, euf::enode* const* _binding, unsigned max_generation, unsigned min_top, unsigned max_top) {
        binding* b = tmp_binding(q, pat, _binding);

        if (m_bindings.contains(b))
            return nullptr;

        for (unsigned i = q->get_num_decls(); i-- > 0; )
            b->m_nodes[i] = b->m_nodes[i]->get_root();

        if (m_bindings.contains(b))
            return nullptr;

        unsigned n = q->get_num_decls();
        unsigned sz = sizeof(binding) + sizeof(euf::enode* const*) * n;
        void* mem = get_region().allocate(sz);
        b = new (mem) binding(q, pat, max_generation, min_top, max_top);
        b->init(b);
        for (unsigned i = 0; i < n; ++i)
            b->m_nodes[i] = _binding[i]->get_root();

        m_bindings.insert(b);
        get_trail().push(insert_map<bindings, binding*>(m_bindings, b));
        return b;
    }

    // callback when mam finds a binding
    void completion::on_binding(quantifier* q, app* pat, enode* const* binding, unsigned max_global, unsigned min_top, unsigned max_top) {
        if (should_stop())
            return;
        if (max_top >= m_max_generation)
            return;
        auto* b = alloc_binding(q, pat, binding, max_global, min_top, max_top);
        if (!b)
            return;
        insert_binding(b);
    }

    void completion::insert_binding(binding* b) {
        m_queue.reserve(b->m_max_top_generation + 1);
        m_queue[b->m_max_top_generation].push_back(b);
    }

    void completion::flush_binding_queue() {
        TRACE(euf_completion, 
            tout << "flush-queue\n";
            for (unsigned i = 0; i < m_queue.size(); ++i)
                tout << i << ": " << m_queue[i].size() << "\n";);
        IF_VERBOSE(10,
            verbose_stream() << "flush-queue\n";
        for (unsigned i = 0; i < m_queue.size(); ++i)
            verbose_stream() << i << ": " << m_queue[i].size() << "\n");

        for (auto& g : m_queue) {
            for (auto b : g)
                apply_binding(*b);
            g.reset();
        }
    }

    void completion::apply_binding(binding& b) {
        if (should_stop())
            return;
        expr_ref_vector _binding(m);
        quantifier* q = b.m_q;
        for (unsigned i = 0; i < q->get_num_decls(); ++i)
            _binding.push_back(b.m_nodes[i]->get_expr());
        if (m_matcher.is_ho_pattern(b.m_pattern)) {
            flet<binding*> set_binding(m_ho_binding, &b);
            m_matcher.refine_ho_match(b.m_pattern, _binding);
        }
        else        
            apply_binding(b, q, _binding);
        
    }

    void completion::apply_binding(binding& b, quantifier* q, expr_ref_vector const& s) {
        var_subst subst(m);
        expr_ref r = subst(q->get_expr(), s);      
        scoped_generation sg(*this, b.m_max_top_generation + 1);
        auto [pr, d] = get_dependency(q);
        if (pr)
            pr = m.mk_quant_inst(m.mk_or(m.mk_not(q), r), s.size(), s.data());
        m_consequences.push_back(r);
        TRACE(euf_completion, tout << "new instantiation: " << r << " q: " << mk_pp(q, m) << "\n");
        add_constraint(r, pr, d);
        propagate_rules();
        m_egraph.propagate();
    }

    void completion::read_egraph() {
        if (m_egraph.inconsistent()) {
            auto* d = explain_conflict();
            proof_ref pr(m);
            if (m.proofs_enabled()) 
                pr = prove_conflict();
            
            dependent_expr de(m, m.mk_false(), pr.get(), d);
            m_fmls.update(0, de);
            return;
        }
        unsigned sz = qtail();
        for (unsigned i = qhead(); i < sz; ++i) {
            auto [f, p, d] = m_fmls[i]();
            expr_dependency_ref dep(d, m);
            proof_ref pr(p, m);
            expr_ref g = canonize_fml(f, pr, dep);
            if (g != f) {
                m_fmls.update(i, dependent_expr(m, g, pr, dep));
                m_stats.m_num_rewrites++;
                IF_VERBOSE(2, verbose_stream() << mk_bounded_pp(f, m, 3) << " -> " << mk_bounded_pp(g, m, 3) << "\n");
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
                n = m_egraph.mk(e, m_generation, m_args.size(), m_args.data());
                if (m_egraph.get_plugin(e->get_sort()->get_family_id()))
                    m_egraph.add_th_var(n, m_th_var++, e->get_sort()->get_family_id());
                if (!m.is_eq(e)) {
                    for (auto ch : m_args)
                        for (auto idv : euf::enode_th_vars(*ch))
                            m_egraph.register_shared(n, idv.get_id());
                }
                                    
                m_nodes_to_canonize.push_back(n);
                m_todo.pop_back();
            }
        }
        return m_egraph.find(e);
    }


    expr_ref completion::canonize_fml(expr* f, proof_ref& pr, expr_dependency_ref& d) {

        auto is_nullary = [&](expr* e) {
            return is_app(e) && to_app(e)->get_num_args() == 0;
            };
        expr* x, * y;
        proof_ref pr1(m), pr2(m), pr3(m);
        if (m.is_eq(f, x, y)) {
            expr_ref x1 = canonize(x, pr1, d);
            expr_ref y1 = canonize(y, pr2, d);

            if (is_nullary(x)) {
                SASSERT(x1 == x);
                x1 = get_canonical(x, pr1, d);
            }
            if (is_nullary(y)) {
                SASSERT(y1 == y);
                y1 = get_canonical(y, pr2, d);
            }

            expr_ref r(m);

            if (x == y)
                r = expr_ref(m.mk_true(), m);
            else if (x == x1 && y == y1)
                r = m_rewriter.mk_eq(x, y);
            else if (is_nullary(x) && is_nullary(y)) 
                r = mk_and(m_rewriter.mk_eq(x, x1), m_rewriter.mk_eq(y, x1));
            else if (x == x1 && is_nullary(x))
                r = m_rewriter.mk_eq(y1, x1);
            else if (y == y1 && is_nullary(y))
                r = m_rewriter.mk_eq(x1, y1);
            else if (is_nullary(x))
                r = mk_and(m_rewriter.mk_eq(x, x1), m_rewriter.mk_eq(y1, x1));
            else if (is_nullary(y))
                r = mk_and(m_rewriter.mk_eq(y, y1), m_rewriter.mk_eq(x1, y1));
            if (x1 == y1)
                r = expr_ref(m.mk_true(), m);
            else {
                auto c = get_canonical(x, pr3, d);
                if (c == x1)
                    r = m_rewriter.mk_eq(y1, c);
                else if (c == y1)
                    r = m_rewriter.mk_eq(x1, c);
                else
                    r = mk_and(m_rewriter.mk_eq(x1, c), m_rewriter.mk_eq(y1, c));
            }

            if (m.proofs_enabled()) {
                expr_ref_vector prs(m);
                prs.push_back(pr);
                if (pr1) prs.push_back(pr1);
                if (pr2) prs.push_back(pr2);
                if (pr3) prs.push_back(pr3);
                prs.push_back(r);
                pr = m.mk_app(symbol("euf"), prs.size(), prs.data(), m.mk_proof_sort());
            }

            return r;
        }

        if (m.is_not(f, x)) {
            expr_ref x1 = canonize(x, pr1, d);
            expr_ref r(mk_not(m, x1), m);
            if (m.proofs_enabled()) {
                expr* prs[3] = { pr, pr1, r };
                pr = m.mk_app(symbol("euf"), 3, prs, m.mk_proof_sort());
            }
            return r;
        }

        return canonize(f, pr, d);
    }

    expr_ref completion::mk_and(expr* a, expr* b) {
        if (m.is_true(a))
            return expr_ref(b, m);
        if (m.is_true(b))
            return expr_ref(a, m);
        return expr_ref(m.mk_and(a, b), m);
    }

    expr_ref completion::canonize(expr* f, proof_ref& pr, expr_dependency_ref& d) {
        
        if (!is_app(f))
            return expr_ref(f, m); // todo could normalize ground expressions under quantifiers

        m_eargs.reset();
        bool change = false;
        expr_ref_vector prs(m);
        for (expr* arg : *to_app(f)) {
            proof_ref pr1(m);
            m_eargs.push_back(get_canonical(arg, pr1, d));
            change |= arg != m_eargs.back();
            if (arg != m_eargs.back() && pr1)
                prs.push_back(pr1);
        }
        expr_ref r(m);
        if (m.is_eq(f))
            r = m_rewriter.mk_eq(m_eargs.get(0), m_eargs.get(1));
        else if (!change)
            return expr_ref(f, m);
        else
            r = expr_ref(m_rewriter.mk_app(to_app(f)->get_decl(), m_eargs.size(), m_eargs.data()), m);
        if (m.proofs_enabled()) {
            prs.push_back(r);
            pr = m.mk_app(symbol("euf"), prs.size(), prs.data(), m.mk_proof_sort());
        }
        return r;
    }

    expr_ref completion::get_canonical(quantifier* q, proof_ref& pr, expr_dependency_ref& d) {
        std::pair<ptr_vector<expr>, expr*> clos;
//        verbose_stream() << "canonize " << mk_pp(q, m) << "\n";
        if (!m_closures.find(q, clos))
            return expr_ref(q, m);
        expr* body = clos.second;
        SASSERT(m_egraph.find(body));
#if 0
        verbose_stream() << "class of " << mk_pp(body, m) << "\n";
        for (auto s : euf::enode_class(n)) {
            verbose_stream() << mk_pp(s->get_expr(), m) << "\n";
        }
#endif
        auto n = m_egraph.find(q);
#if 0
        verbose_stream() << "class of " << mk_pp(q, m) << "\n";
        for (auto s : euf::enode_class(n)) {
            verbose_stream() << mk_pp(s->get_expr(), m) << "\n";
        }
#endif
        expr_ref new_body = get_canonical(body, pr, d);
        expr_ref result = expr_abstract(m, clos.first, new_body);
        result = m.update_quantifier(q, result);
        if (m.proofs_enabled()) {
            // add proof rule 
            // 
            // body = new_body
            // ---------------------------
            // Q x . body = Q x . new_body
            NOT_IMPLEMENTED_YET();
        }
        return result;
    }


    expr_ref completion::get_canonical(expr* f, proof_ref& pr, expr_dependency_ref& d) {
        expr_ref e(m);
        if (has_quantifiers(f)) {
            if (is_quantifier(f))
                return get_canonical(to_quantifier(f), pr, d);
            else if (is_app(f)) {
                expr_ref_vector args(m);
                for (auto arg : *to_app(f)) {
                    // TODO: pr reconstruction
                    args.push_back(get_canonical(arg, pr, d));
                }
                e = m.mk_app(to_app(f)->get_decl(), args);
                if (!m_egraph.find(e))
                    return e;
                f = e;
            }
            else
                UNREACHABLE();

        }
        enode* n = m_egraph.find(f);
        if (!n) n = mk_enode(f);
        enode* r = n->get_root();
        d = m.mk_join(d, explain_eq(n, r));
        d = m.mk_join(d, m_deps.get(r->get_id(), nullptr));
        if (m.proofs_enabled()) {
            pr = prove_eq(n, r);
            if (get_canonical_proof(r)) 
                pr = m.mk_transitivity(pr, get_canonical_proof(r));            
        }
        SASSERT(m_canonical.get(r->get_id()));
        return expr_ref(m_canonical.get(r->get_id()), m);
    }

    expr* completion::get_canonical(enode* n) {
        if (m_epochs.get(n->get_id(), 0) == m_epoch)
            return m_canonical.get(n->get_id());
        else
            return nullptr;
    }

    proof* completion::get_canonical_proof(enode* n) {
        if (m_epochs.get(n->get_id(), 0) == m_epoch && n->get_id() < m_canonical_proofs.size())
            return m_canonical_proofs.get(n->get_id());
        else
            return nullptr;
    }

    void completion::set_canonical(enode* n, expr* e, proof* pr) {
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
        if (pr)
            m_canonical_proofs.setx(n->get_id(), pr);
        m_epochs.setx(n->get_id(), m_epoch, 0);
    }

    expr_dependency* completion::explain_eq(enode* a, enode* b) {
        if (a == b)
            return nullptr;
        ptr_vector<size_t> just;
        m_egraph.begin_explain();
        m_egraph.explain_eq(just, nullptr, a, b);
        m_egraph.end_explain();
        expr_dependency* d = nullptr;
        for (size_t* j : just)
            d = m.mk_join(d, m_pr_dep[from_ptr(j)].second);
        return d;
    }

    expr_dependency* completion::explain_conflict() {
        ptr_vector<size_t> just;
        m_egraph.begin_explain();
        m_egraph.explain(just, nullptr);
        m_egraph.end_explain();
        expr_dependency* d = nullptr;
        for (size_t* j : just) 
            d = m.mk_join(d, m_pr_dep[from_ptr(j)].second);
        return d;
    }

    proof_ref completion::prove_eq(enode* a, enode* b) {
        expr_ref_vector prs(m);
        proof_ref pr(m);
        ptr_vector<size_t> just;
        m_egraph.begin_explain();
        m_egraph.explain_eq(just, nullptr, a, b);
        m_egraph.end_explain();
        for (size_t* j : just)
            prs.push_back(m_pr_dep[from_ptr(j)].first);
        prs.push_back(m.mk_eq(a->get_expr(), b->get_expr()));
        pr = m.mk_app(symbol("euf"), prs.size(), prs.data(), m.mk_proof_sort());
        return pr;
    }

    proof_ref completion::prove_conflict() {
        expr_ref_vector prs(m);
        proof_ref pr(m);
        ptr_vector<size_t> just;
        m_egraph.begin_explain();
        m_egraph.explain(just, nullptr);
        m_egraph.end_explain();
        for (size_t* j : just)
            prs.push_back(m_pr_dep[from_ptr(j)].first);
        prs.push_back(m.mk_false());
        pr = m.mk_app(symbol("euf"), prs.size(), prs.data(), m.mk_proof_sort());
        return pr;
    }

    void completion::collect_statistics(statistics& st) const {
        st.update("euf-completion-rewrites", m_stats.m_num_rewrites);
        st.update("euf-completion-instances", m_stats.m_num_instances);
        m_egraph.collect_statistics(st);
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
        expr_ref_vector prs(m);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            enode* n = m_egraph.find(e);
            SASSERT(n->is_root());
            enode* rep = m_reps[n->get_id()];
            if (get_canonical(n))
                m_todo.pop_back();
            else if (get_depth(rep->get_expr()) == 0 || !is_app(rep->get_expr())) {
                set_canonical(n, rep->get_expr(), nullptr);
                m_todo.pop_back();
            }
            else {
                m_eargs.reset();
                unsigned sz = m_todo.size();
                bool new_arg = false;
                expr_dependency* d = m_deps.get(n->get_id(), nullptr);
                proof_ref pr(m);
                prs.reset();
                for (enode* arg : enode_args(rep)) {
                    auto rarg = arg->get_root();
                    auto c = get_canonical(rarg);
                    if (c) {
                        m_eargs.push_back(c);
                        new_arg |= c != arg->get_expr();
                        d = m.mk_join(d, m_deps.get(rarg->get_id(), nullptr));
                        if (m.proofs_enabled() && c != arg->get_expr() && get_canonical_proof(rarg))
                            prs.push_back(get_canonical_proof(rarg));
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
                    if (m.proofs_enabled() && new_arg) {
                        prs.push_back(m.mk_eq(n->get_expr(), new_expr));
                        pr = m.mk_app(symbol("euf"), prs.size(), prs.data(), m.mk_proof_sort());
                    }
                    set_canonical(n, new_expr, pr);
                    m_deps.setx(n->get_id(), d);
                }
            }
        }
    }
}
