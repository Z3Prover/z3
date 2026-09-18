/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    recfun_finder.cpp

Abstract:

    Detect recursive-function axioms and turn them into recfun definitions.

Author:

    Jean-Frédéric Etienne (etiennejf) 2026-09-16
    Nikolaj Bjorner (nbjorner) 2026-09-16

--*/

#include <functional>
#include <vector>
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/occurs.h"
#include "ast/rewriter/recfun_replace.h"
#include "ast/rewriter/var_subst.h"
#include "ast/simplifiers/recfun_finder.h"
#include "util/uint_set.h"

namespace {

    bool contains_sym(ast_manager& m, expr* e, obj_hashtable<func_decl> const& syms) {
        for (expr* t : subterms::all(expr_ref(e, m)))
            if (is_app(t) && syms.contains(to_app(t)->get_decl()))
                return true;
        return false;
    }

    expr_ref guard_recursion(ast_manager& m, expr* e, obj_hashtable<func_decl> const& syms) {
        expr_ref r(e, m);
        if (!contains_sym(m, e, syms))
            return r;
        if (m.is_ite(e)) {
            app* a = to_app(e);
            expr_ref t = guard_recursion(m, a->get_arg(1), syms);
            expr_ref el = guard_recursion(m, a->get_arg(2), syms);
            return expr_ref(m.mk_ite(a->get_arg(0), t, el), m);
        }
        if (m.is_not(e))
            return expr_ref(m.mk_not(guard_recursion(m, to_app(e)->get_arg(0), syms)), m);
        if (m.is_or(e) || m.is_and(e)) {
            bool is_or = m.is_or(e);
            expr_ref_vector guards(m), recs(m);
            for (expr* arg : *to_app(e))
                (contains_sym(m, arg, syms) ? recs : guards).push_back(guard_recursion(m, arg, syms));
            if (guards.empty())
                return r;
            expr_ref g = is_or ? mk_or(guards) : mk_and(guards);
            expr_ref rest = is_or ? mk_or(recs) : mk_and(recs);
            return expr_ref(is_or ? m.mk_ite(g, m.mk_true(), rest) : m.mk_ite(g, rest, m.mk_false()), m);
        }
        return r;
    }

    bool recursion_guarded(ast_manager& m, expr* e, obj_hashtable<func_decl> const& syms) {
        if (m.is_ite(e))
            return true;
        if (is_app(e)) {
            app* a = to_app(e);
            if (syms.contains(a->get_decl()))
                return false;
            for (expr* arg : *a)
                if (!recursion_guarded(m, arg, syms))
                    return false;
        }
        return true;
    }

}

struct recfun_finder::undo_aliases : public trail {
    recfun_finder& s;
    unsigned sz;
    undo_aliases(recfun_finder& s): s(s), sz(s.m_aliases.size()) {}
    void undo() override {
        while (s.m_aliases.size() > sz) {
            s.m_alias_map.remove(s.m_aliases.back().m_src);
            s.m_aliases.pop_back();
        }
    }
};

void recfun_finder::push() {
    m_trail.push(undo_aliases(*this));
}

void recfun_finder::add_alias(func_decl* src, func_decl* dst) {
    if (m_alias_map.contains(src))
        return;
    m_alias_map.insert(src, dst);
    m_aliases.push_back(alias(m, src, dst));
}

func_decl_replace recfun_finder::mk_replace() const {
    func_decl_replace r(m);
    for (auto const& a : m_aliases)
        r.insert(a.m_src, a.m_dst);
    return r;
}

void recfun_finder::apply_aliases() {
    if (m_aliases.empty())
        return;
    func_decl_replace replace = mk_replace();
    for (unsigned i : indices()) {
        auto [f, p, d] = m_fmls[i]();
        expr_ref r = replace(f);
        if (r != f)
            m_fmls.update(i, dependent_expr(m, r, nullptr, d));
    }
}

bool recfun_finder::has_quantifier() const {
    for (unsigned i = qhead(); i < qtail(); ++i)
        if (is_quantifier(m_fmls[i].fml()))
            return true;
    return false;
}

void recfun_finder::reduce() {
    apply_aliases();
    if (has_quantifier())
        find_recfuns_core();
}

void recfun_finder::find_recfuns_core() {
    if (!m.has_plugin(symbol("recfun")))
        m.register_plugin(symbol("recfun"), alloc(recfun::decl::plugin));
    recfun::util ru(m);
    recfun::decl::plugin& plugin = ru.get_plugin();

    struct candidate {
        quantifier* q;
        app*        head;
        expr_ref    def;
        expr_dependency_ref dep;
        func_decl*  mirror;
        unsigned    fml_idx;
    };

    vector<candidate> cands;
    obj_map<func_decl, unsigned> f2c;
    obj_hashtable<func_decl> ambiguous;

    for (unsigned i : indices()) {
        expr* fml = m_fmls[i].fml();
        if (!is_forall(fml))
            continue;
        quantifier* q = to_quantifier(fml);
        IF_VERBOSE(11, verbose_stream() << "(recfun-finder :axiom " << mk_pp(q->get_expr(), m) << ")\n";);
        unsigned nd = q->get_num_decls();
        app_ref head(m);
        expr_ref defr(m);
        expr* n = q->get_expr();
        expr *a = nullptr, *b = nullptr;
        bool neg = m.is_not(n, n);
        if (m.is_eq(n, a, b) && (!neg || m.is_bool(a))) {
            if (m_macro_util.is_macro_head(a, nd))
                head = to_app(a), defr = neg ? m.mk_not(b) : expr_ref(b, m);
            else if (m_macro_util.is_macro_head(b, nd))
                head = to_app(b), defr = neg ? m.mk_not(a) : expr_ref(a, m);
        }
        if (!head) {
            app_ref ahead(m);
            expr_ref adef(m);
            bool inv = false;
            if (!neg && m_macro_util.is_arith_macro(n, nd, ahead, adef, inv))
                head = ahead, defr = adef;
        }
        if (!head) {
            IF_VERBOSE(11, verbose_stream() << "(recfun-finder :no-head)\n";);
            continue;
        }
        app* head_app = head.get();
        expr* def = defr.get();
        func_decl* f = head_app->get_decl();
        if (m_fmls.frozen(f) || m_alias_map.contains(f) || ru.has_def(f))
            continue;
        if (f2c.contains(f)) {
            ambiguous.insert(f);
            continue;
        }
        expr_ref d(def, m);
        bool has_lam = false;
        for (expr* e : subterms::all(d))
            if (is_lambda(e)) { has_lam = true; break; }
        if (has_lam) {
            IF_VERBOSE(11, verbose_stream() << "(recfun-finder :lambda-in-body " << f->get_name() << ")\n";);
            continue;
        }
        func_decl* mirror = nullptr;
        if (is_app(def) && ru.is_defined(to_app(def)->get_decl()) && ru.has_def(to_app(def)->get_decl()) &&
            to_app(def)->get_num_args() == head_app->get_num_args()) {
            app* ga = to_app(def);
            bool same = !m_fmls.frozen(ga->get_decl());
            for (unsigned k = 0; same && k < ga->get_num_args(); ++k)
                same = ga->get_arg(k) == head_app->get_arg(k);
            recfun::def& gd = ru.get_def(ga->get_decl());
            if (same && gd.get_rhs() && gd.get_vars().size() == ga->get_num_args()) {
                unsigned max_idx = 0;
                for (var* v : gd.get_vars())
                    max_idx = std::max(max_idx, v->get_idx() + 1);
                expr_ref_vector sub(m);
                for (unsigned k = 0; k < max_idx; ++k)
                    sub.push_back(m.mk_var(k, m.mk_bool_sort()));
                for (unsigned k = 0; k < ga->get_num_args(); ++k)
                    sub[gd.get_vars()[k]->get_idx()] = ga->get_arg(k);
                var_subst vs(m, false);
                d = vs(gd.get_rhs(), sub.size(), sub.data());
                mirror = ga->get_decl();
            }
        }
        f2c.insert(f, cands.size());
        cands.push_back(candidate{ q, head_app, d, expr_dependency_ref(m_fmls[i].dep(), m), mirror, i });
        IF_VERBOSE(11, verbose_stream() << "(recfun-finder :candidate " << f->get_name() << (mirror ? " :mirror " : "") << (mirror ? mirror->get_name().str() : std::string()) << ")\n";);
    }

    unsigned n = cands.size();
    obj_map<func_decl, unsigned> sym2c;
    unsigned i = 0;
    for (auto& cand : cands) {
        if (ambiguous.contains(cand.head->get_decl())) {
            ++i;
            continue;
        }
        sym2c.insert(cand.head->get_decl(), i);
        if (cand.mirror)
            sym2c.insert(cand.mirror, i);
        ++i;
    }

    vector<unsigned_vector> succ(n);
    for (unsigned i = 0; i < n; ++i) {
        if (ambiguous.contains(cands[i].head->get_decl()))
            continue;
        for (expr* e : subterms::all(expr_ref(cands[i].def.get(), m))) {
            unsigned j;
            if (is_app(e) && sym2c.find(to_app(e)->get_decl(), j))
                succ[i].push_back(j);
        }
    }

    unsigned_vector index, low, stack;
    svector<bool> on_stack;
    index.resize(n, UINT_MAX);
    low.resize(n, 0);
    on_stack.resize(n, false);
    vector<unsigned_vector> comps;
    unsigned counter = 0;
    std::function<void(unsigned)> strong = [&](unsigned v) {
        index[v] = low[v] = counter++;
        stack.push_back(v);
        on_stack[v] = true;
        for (unsigned w : succ[v]) {
            if (index[w] == UINT_MAX) {
                strong(w);
                low[v] = std::min(low[v], low[w]);
            }
            else if (on_stack[w])
                low[v] = std::min(low[v], index[w]);
        }
        if (low[v] == index[v]) {
            unsigned_vector comp;
            unsigned w;
            do {
                w = stack.back();
                stack.pop_back();
                on_stack[w] = false;
                comp.push_back(w);
            }
            while (w != v);
            comps.push_back(comp);
        }
    };
    for (unsigned v = 0; v < n; ++v)
        if (index[v] == UINT_MAX && !ambiguous.contains(cands[v].head->get_decl()))
            strong(v);

    vector<unsigned_vector> rec_comps;
    for (auto const& comp : comps) {
        bool rec = comp.size() > 1;
        if (!rec)
            for (unsigned w : succ[comp[0]])
                rec |= w == comp[0];
        if (rec)
            rec_comps.push_back(comp);
    }

    svector<bool> accepted;
    accepted.resize(rec_comps.size(), true);
    bool changed = true;
    while (changed) {
        changed = false;
        obj_hashtable<func_decl> mirrors;
        for (unsigned c = 0; c < rec_comps.size(); ++c)
            if (accepted[c])
                for (unsigned i : rec_comps[c])
                    if (cands[i].mirror)
                        mirrors.insert(cands[i].mirror);
        for (unsigned c = 0; c < rec_comps.size(); ++c) {
            if (!accepted[c])
                continue;
            bool blocked = false;
            for (func_decl* g : ru.get_rec_funs()) {
                if (mirrors.contains(g) || !ru.has_def(g))
                    continue;
                if (ru.get_def(g).is_macro())
                    continue;
                expr* rhs = ru.get_def(g).get_rhs();
                for (unsigned i : rec_comps[c])
                    if (rhs && occurs(cands[i].head->get_decl(), rhs)) {
                        blocked = true;
                        IF_VERBOSE(11, verbose_stream() << "(recfun-finder :blocked-by " << g->get_name() << " :head " << cands[i].head->get_decl()->get_name() << ")\n";);
                    }
            }
            if (blocked) {
                accepted[c] = false;
                changed = true;
                IF_VERBOSE(11, verbose_stream() << "(recfun-finder :blocked " << cands[rec_comps[c][0]].head->get_decl()->get_name() << ")\n";);
            }
        }
    }
    {
        vector<unsigned_vector> kept;
        for (unsigned c = 0; c < rec_comps.size(); ++c)
            if (accepted[c])
                kept.push_back(rec_comps[c]);
        rec_comps.swap(kept);
    }

    obj_hashtable<func_decl> rec_syms;
    for (auto const& comp : rec_comps)
        for (unsigned i : comp) {
            rec_syms.insert(cands[i].head->get_decl());
            if (cands[i].mirror)
                rec_syms.insert(cands[i].mirror);
        }

    {
        vector<unsigned_vector> kept;
        for (auto const& comp : rec_comps) {
            uint_set unguarded, in_comp;
            for (unsigned i : comp) {
                in_comp.insert(i);
                cands[i].def = guard_recursion(m, cands[i].def, rec_syms);
                if (!recursion_guarded(m, cands[i].def, rec_syms))
                    unguarded.insert(i);
            }
            unsigned_vector color;
            color.resize(n, 0);
            bool cyclic = false;
            std::function<void(unsigned)> dfs = [&](unsigned v) {
                color[v] = 1;
                for (unsigned w : succ[v]) {
                    if (!in_comp.contains(w) || !unguarded.contains(w))
                        continue;
                    if (color[w] == 1)
                        cyclic = true;
                    else if (color[w] == 0)
                        dfs(w);
                }
                color[v] = 2;
            };
            for (unsigned i : comp)
                if (unguarded.contains(i) && color[i] == 0)
                    dfs(i);
            if (cyclic) {
                IF_VERBOSE(11, verbose_stream() << "(recfun-finder :unguarded-cycle " << cands[comp[0]].head->get_decl()->get_name() << ")\n";);
                continue;
            }
            kept.push_back(comp);
        }
        rec_comps.swap(kept);
    }

    func_decl_replace replace = mk_replace();
    std::vector<std::pair<unsigned, recfun::promise_def>> pdefs;
    uint_set removed;
    vector<std::tuple<func_decl_ref, expr_ref, expr_dependency_ref>> model_defs;

    for (auto const& comp : rec_comps) {
        for (unsigned i : comp) {
            func_decl* f = cands[i].head->get_decl();
            recfun::promise_def pd = plugin.ensure_def(f->get_name(), f->get_arity(), f->get_domain(), f->get_range(), true);
            func_decl* f1 = pd.get_def()->get_decl();
            m_pinned.push_back(f1);
            replace.insert(f, f1);
            add_alias(f, f1);
            if (cands[i].mirror) {
                replace.insert(cands[i].mirror, f1);
                add_alias(cands[i].mirror, f1);
            }
            pdefs.push_back(std::make_pair(i, pd));
        }
    }

    for (auto& [i, pd] : pdefs) {
        candidate& c = cands[i];
        unsigned nargs = c.head->get_num_args();
        expr_ref_vector sub(m);
        var_ref_vector vars(m);
        for (unsigned k = 0; k < nargs; ++k)
            sub.push_back(nullptr);
        for (unsigned k = 0; k < nargs; ++k) {
            var* v = to_var(c.head->get_arg(k));
            var* w = m.mk_var(nargs - 1 - k, v->get_sort());
            sub[v->get_idx()] = w;
            vars.push_back(w);
        }
        var_subst vs(m, false);
        expr_ref body = vs(c.def, sub.size(), sub.data());
        body = replace(body);
        recfun_replace rr(m);
        plugin.set_definition(rr, pd, false, vars.size(), vars.data(), body);
        IF_VERBOSE(11, verbose_stream() << "(recfun-finder :define " << pd.get_def()->get_decl()->get_name() << " := " << body << ")\n";);
        ++m_num_recfuns;
    }

    for (auto& [i, pd] : pdefs) {
        candidate& c = cands[i];
        if (!c.mirror)
            continue;
        func_decl* g = c.mirror;
        func_decl* f1 = pd.get_def()->get_decl();
        unsigned nargs = g->get_arity();
        var_ref_vector vars(m);
        expr_ref_vector args(m);
        for (unsigned k = 0; k < nargs; ++k) {
            var* w = m.mk_var(nargs - 1 - k, g->get_domain(k));
            vars.push_back(w);
            args.push_back(w);
        }
        recfun::promise_def gpd = plugin.ensure_def(g->get_name(), nargs, g->get_domain(), g->get_range(), true);
        expr_ref alias(m.mk_app(f1, args.size(), args.data()), m);
        recfun_replace rr(m);
        plugin.set_definition(rr, gpd, true, vars.size(), vars.data(), alias);
    }

    for (auto& [i, pd] : pdefs) {
        candidate& c = cands[i];
        func_decl* f = c.head->get_decl();
        func_decl* f1 = pd.get_def()->get_decl();
        unsigned nargs = f->get_arity();
        expr_ref_vector args(m);
        for (unsigned k = 0; k < nargs; ++k)
            args.push_back(m.mk_var(nargs - 1 - k, f->get_domain(k)));
        expr_ref rhs(m.mk_app(f1, args.size(), args.data()), m);
        model_defs.push_back(std::make_tuple(func_decl_ref(f, m), rhs, c.dep));
        m_fmls.model_trail().hide(f1);
        removed.insert(c.fml_idx);
    }

    if (pdefs.empty())
        return;

    for (unsigned i : indices()) {
        if (removed.contains(i))
            continue;
        auto [f, p, d] = m_fmls[i]();
        expr_ref r = replace(f);
        if (r != f)
            m_fmls.update(i, dependent_expr(m, r, nullptr, d));
    }

    for (unsigned i = qhead(); i < qtail(); ++i)
        if (removed.contains(i))
            m_fmls.update(i, dependent_expr(m, m.mk_true(), nullptr, m_fmls[i].dep()));

    if (!model_defs.empty())
        m_fmls.model_trail().push(model_defs, {});

    IF_VERBOSE(10, verbose_stream() << "(recfun-finder :num-defs " << pdefs.size() << ")\n";);
}

