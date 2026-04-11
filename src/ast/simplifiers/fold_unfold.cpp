/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    fold_unfold.h

Abstract:

    fold-unfold simplifier

Author:

    Nikolaj Bjorner (nbjorner) 2025-11-5.

- remove alias x = y
- remove alias with const x = k
- fold-unfold simplification x = f(y), y = g(z), f(g(z)) = u -> x |-> u

- assign levels to E-nodes:
  - dfs over roots.
  - visit children, assign level
  - 
- remove alias with linear x = f(y) -> x |-> f(y) if level y < level x
--*/

#include "ast/ast_pp.h"
#include "ast/simplifiers/fold_unfold.h"
#include "ast/rewriter/expr_replacer.h"
#include "util/union_find.h"
#include "params/smt_params_helper.hpp"

namespace euf {

    fold_unfold::fold_unfold(ast_manager& m, dependent_expr_state& fmls)
        : dependent_expr_simplifier(m, fmls),
        m_rewriter(m),
        m_egraph(m) {
        register_extract_eqs(m, m_extract_plugins);
        m_rewriter.set_flat_and_or(false);
        // flat sum/prod := false
    }

    void fold_unfold::reduce() {
        if (!m_config.m_enabled)
            return;

        m_fmls.freeze_suffix();

        for (extract_eq* ex : m_extract_plugins)
            ex->pre_process(m_fmls);

        reduce_alias(true);
        reduce_linear();
        reduce_alias(false);
    }

    void fold_unfold::reduce_alias(bool fuf) {
        m_subst = nullptr;
        dep_eq_vector eqs;
        get_eqs(eqs);
        extract_subst(fuf, eqs);
        vector<dependent_expr> old_fmls;
        apply_subst(old_fmls);
    }

    void fold_unfold::get_eqs(dep_eq_vector& eqs) {
        for (extract_eq* ex : m_extract_plugins)
            for (unsigned i : indices())
                ex->get_eqs(m_fmls[i], eqs);
    }

    void fold_unfold::extract_subst(bool fuf, dep_eq_vector const& eqs) {
        m_find.reset();
        for (auto const& [orig, v, t, d] : eqs) {
            auto a = mk_enode(v);
            auto b = mk_enode(t);
            // verbose_stream() << mk_bounded_pp(v, m) << " == " << mk_bounded_pp(t, m) << "\n";
            proof_ref pr(m);
            auto j = to_ptr(push_pr_dep(pr, d));
            m_egraph.merge(a, b, j);
        }

        // choose uninterpreted or value representative
        auto find_rep = [&](enode *a, ptr_buffer<enode>& vars) {
            enode *rep = nullptr;
            for (auto b : euf::enode_class(a)) {
                expr *t = b->get_expr();
                if (is_uninterp_const(t))
                    vars.push_back(b);
                if (m.is_value(t))
                    rep = b;
            }
            if (!rep) {
                for (auto v : vars)
                    if (!rep || v->get_id() < rep->get_id())
                        rep = v;
            }
            return rep;
        };

        for (auto a : m_egraph.nodes()) {
            if (!a->is_root())
                continue;
            ptr_buffer<enode> vars;
            enode *rep = find_rep(a, vars);
            if (!rep)
                continue;
            for (auto w : vars) {
                if (w != rep)
                    m_find.setx(w->get_id(), rep, nullptr);
            }
        }
        if (fuf) {
            // find new equalities by performing fold-unfold
            vector<std::tuple<enode *, expr_ref, proof_ref, expr_dependency *>> new_eqs;
            for (auto n : m_egraph.nodes()) {
                if (!n->is_root())
                    continue;
                auto ne = n->get_expr();
                unsigned depth = 3;
                vector<std::pair<expr_ref, expr_dependency *>> es;
                unfold(depth, n, nullptr, es);
                // verbose_stream() << "unfolds " << es.size() << "\n";
                for (auto [e, d] : es) {
                    expr_ref r(m);
                    proof_ref pr(m);
                    fold(e, r, pr);
                    if (ne == r)
                        continue;
                    new_eqs.push_back({n, r, pr, d});
                }
            }
            for (auto const &[a, t, pr, d] : new_eqs) {
                auto b = mk_enode(t);
                auto j = to_ptr(push_pr_dep(pr, d));
                m_egraph.merge(a, b, j);
            }
        }

        for (auto a : m_egraph.nodes()) {            
            if (!a->is_root())
                continue;
            ptr_buffer<enode> vars;
            enode *rep = find_rep(a, vars);
            if (!rep)
                continue;
            for (auto v : vars) {
                if (v == rep)
                    continue;
                m_find.setx(v->get_id(), rep, nullptr);
                // verbose_stream() << "insert " << mk_pp(v->get_expr(), m) << " " << mk_pp(rep->get_expr(), m) << "\n";
                insert_subst(v->get_expr(), rep->get_expr(), explain_eq(v, rep));
                m_stats.m_num_elim_vars++;
            }
        }
    }

    expr_dependency *fold_unfold::explain_eq(enode *a, enode *b) {
        if (a == b)
            return nullptr;
        ptr_vector<size_t> just;
        m_egraph.begin_explain();
        m_egraph.explain_eq(just, nullptr, a, b);
        m_egraph.end_explain();
        expr_dependency *d = nullptr;
        for (size_t *j : just)
            d = m.mk_join(d, m_pr_dep[from_ptr(j)].second);        
        return d;
    }

    unsigned fold_unfold::push_pr_dep(proof *pr, expr_dependency *d) {
        unsigned sz = m_pr_dep.size();
        SASSERT(!m.proofs_enabled() || pr);
        m_pr_dep.push_back({proof_ref(pr, m), d});
        m_trail.push(push_back_vector(m_pr_dep));
        return sz;
    }

    enode *fold_unfold::mk_enode(expr *e) {
        m_todo.push_back(e);
        enode *n;
        while (!m_todo.empty()) {
            e = m_todo.back();
            if (m_egraph.find(e)) {
                m_todo.pop_back();
                continue;
            }
            if (!is_app(e)) {
                m_egraph.mk(e, m_generation, 0, nullptr);
                m_todo.pop_back();
                continue;
            }
            m_args.reset();
            unsigned sz = m_todo.size();
            for (expr *arg : *to_app(e)) {
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
                m_todo.pop_back();
            }
        }
        return m_egraph.find(e);
    }


    void fold_unfold::fold(expr *e, expr_ref &result, proof_ref &pr) {
        m_rewriter(e, result, pr);
    }

    void fold_unfold::unfold(unsigned n, enode *e, expr_dependency* d, vector<std::pair<expr_ref, expr_dependency*>>& es) {
        if (n == 0) {
            es.push_back({expr_ref(e->get_expr(), m), d});
            return;
        }
        if (es.size() > 10)
            return;
        unsigned count = 0;
        for (auto sib : euf::enode_class(e)) {
            auto sib_e = sib->get_expr();
            if (!is_app(sib_e))
                continue;
            if (is_uninterp_const(sib_e)) {
                auto f = m_find.get(sib->get_id(), nullptr);
                if (f && f != sib)
                    continue;
            }
            ++count;
            expr_ref_vector args(m);
            expr_dependency *d1 = m.mk_join(d, explain_eq(sib, e));
            unfold_arg(n, 0, sib, args, d1, es);
            if (count > 2)
                break;
        }
        // verbose_stream() << "count " << count << "\n";
    }

    void fold_unfold::unfold_arg(unsigned n, unsigned i, enode* e, expr_ref_vector& args, expr_dependency* d,
        vector<std::pair<expr_ref, expr_dependency*>>& es) {
        if (i == e->num_args()) {
            es.push_back({expr_ref(m.mk_app(e->get_decl(), args), m), d});
            return;
        }
        vector<std::pair<expr_ref, expr_dependency *>> es_arg;
        unfold(n - 1, e->get_arg(i), d, es_arg);
        for (auto [arg, dep] : es_arg) {
            args.push_back(arg);
            unfold_arg(n, i + 1, e, args, dep, es);
            args.pop_back();
            if (es.size() > 10)
                return;
        }
    }

    void fold_unfold::insert_subst(expr * v, expr * t, expr_dependency* d) {
        if (!m_subst)
            m_subst = alloc(expr_substitution, m, true, false);   
        m_subst->insert(v, t, d);
    }

    void fold_unfold::apply_subst(vector<dependent_expr> &old_fmls) {
        if (!m.inc())
            return;
        if (!m_subst)
            return;

        scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
        rp->set_substitution(m_subst.get());

        for (unsigned i : indices()) {
            auto [f, p, d] = m_fmls[i]();
            auto [new_f, new_dep] = rp->replace_with_dep(f);
            proof_ref new_pr(m);
            expr_ref tmp(m);
            m_rewriter(new_f, tmp, new_pr);
            if (tmp == f)
                continue;
            new_dep = m.mk_join(d, new_dep);
            old_fmls.push_back(m_fmls[i]);
            m_fmls.update(i, dependent_expr(m, tmp, mp(p, new_pr), new_dep));
        }
        m_fmls.model_trail().push(m_subst.detach(), old_fmls, false);        
    }

    void fold_unfold::set_levels() {
        m_node2level.reset();
        m_level2node.reset();
        m_level_count = 0;
        for (auto n : m_egraph.nodes()) 
            if (n->is_root())
                set_level(n);        
        for (auto n : m_egraph.nodes()) 
            if (n->is_root())
                n->unmark1();    
    }

    void fold_unfold::set_level(enode* n) {
        SASSERT(n->is_root());

        if (m_node2level.get(n->get_id(), UINT_MAX) != UINT_MAX)
            return;

        if (!n->is_marked1()) {
            n->mark1();
            for (auto b : enode_class(n)) {
                for (auto arg : enode_args(b))
                    set_level(arg->get_root());
            }            
        }
        if (m_node2level.get(n->get_id(), UINT_MAX) != UINT_MAX)
            return;
        for (auto a : enode_class(n)) {
            m_node2level.setx(a->get_id(), m_level_count, UINT_MAX);
            m_level2node.setx(m_level_count, a, nullptr);
        }
        ++m_level_count;        
    }

    void fold_unfold::reduce_linear() {
        set_levels();
        m_subst = alloc(expr_substitution, m, true, false);
        scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
        rp->set_substitution(m_subst.get());
        for (auto n : m_level2node) {
            SASSERT(n);
            SASSERT(n->is_root());
            // if a is uninterpreted and is not eliminated, 
            // n is equal to a linear term with lower level argument
            // back-substitute the linear term using existing subst.
            // update subst with a -> linear term
            enode *var = nullptr;
            enode *term = nullptr;
            for (auto a : enode_class(n)) {
                if (m_find.get(a->get_id(), nullptr) != nullptr) // already substituted
                    continue;
                if (is_uninterp_const(a->get_expr()))
                    var = a;
                else if (is_linear_term(a))
                    term = a;
            }            
            if (var && term) {
                m_find.setx(var->get_id(), term, nullptr); // record that var was replaced
                auto dep = explain_eq(var, term);
                auto [new_term, new_dep] = rp->replace_with_dep(term->get_expr());
                expr_ref r(m);
                proof_ref pr(m);
                m_rewriter(new_term, r, pr);
                m_subst->insert(var->get_expr(), r, m.mk_join(dep, new_dep));
            }
        }
        vector<dependent_expr> old_fmls;
        apply_subst(old_fmls);
    }

    bool fold_unfold::is_linear_term(enode *n) {
        unsigned num_vars = 0;
        unsigned level = m_node2level[n->get_root_id()];
        for (auto arg : enode_args(n))         
            if (!m.is_value(arg->get_expr())) {
                if (m_node2level[arg->get_root_id()] >= level)
                    return false;
                ++num_vars;
            }
        return num_vars <= 1;
    }

    void fold_unfold::updt_params(params_ref const &p) {
        m_config.m_enabled = true;
        params_ref p1;
        p1.set_bool("eliminate_mod", false);
        for (auto ex : m_extract_plugins) {
            ex->updt_params(p);
            ex->updt_params(p1);
        }
    }

    void fold_unfold::collect_param_descrs(param_descrs &r) {}

    void fold_unfold::collect_statistics(statistics &st) const {
        st.update("fold-unfold-steps", m_stats.m_num_steps);
        st.update("fold-unfold-elim-vars", m_stats.m_num_elim_vars);
    }

}
