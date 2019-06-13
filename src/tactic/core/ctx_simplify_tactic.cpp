/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ctx_simplify_tactic.cpp

Abstract:

    Simple context simplifier for propagating constants.

Author:

    Leonardo (leonardo) 2011-10-26

Notes:

--*/
#include "tactic/core/ctx_simplify_tactic.h"
#include "ast/rewriter/mk_simplified_app.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"


class ctx_propagate_assertions : public ctx_simplify_tactic::simplifier {
    ast_manager&         m;
    obj_map<expr, expr*> m_assertions;
    expr_ref_vector      m_trail;
    unsigned_vector      m_scopes;

    void assert_eq_val(expr * t, app * val, bool mk_scope);
    void assert_eq_core(expr * t, app * val);
public:
    ctx_propagate_assertions(ast_manager& m);
    ~ctx_propagate_assertions() override {}
    bool assert_expr(expr * t, bool sign) override;
    bool simplify(expr* t, expr_ref& result) override;
    void push();
    void pop(unsigned num_scopes) override;
    unsigned scope_level() const override { return m_scopes.size(); }
    simplifier * translate(ast_manager & m) override;
};


ctx_propagate_assertions::ctx_propagate_assertions(ast_manager& m): m(m), m_trail(m) {}

bool ctx_propagate_assertions::assert_expr(expr * t, bool sign) {

    expr * p = t;
    while (m.is_not(t, t)) {
        sign = !sign;
    }
    bool mk_scope = true;
    if (shared(t) || shared(p)) {
        push();
        mk_scope  = false;
        assert_eq_core(t, sign ? m.mk_false() : m.mk_true());
    }
    expr * lhs, * rhs;
    if (!sign && m.is_eq(t, lhs, rhs)) {
        if (m.is_value(rhs))
            assert_eq_val(lhs, to_app(rhs), mk_scope);
        else if (m.is_value(lhs))
            assert_eq_val(rhs, to_app(lhs), mk_scope);
    }
    return true;
}

void ctx_propagate_assertions::assert_eq_val(expr * t, app * val, bool mk_scope) {
    if (shared(t)) {
        if (mk_scope)
            push();
        assert_eq_core(t, val);
    }
}

void ctx_propagate_assertions::assert_eq_core(expr * t, app * val) {
    if (m_assertions.contains(t)) {
        // This branch can only happen when m_max_depth was reached.
        // It can happen when m_assertions contains an entry t->val',
        //  but (= t val) was not simplified to (= val' val)
        //  because the simplifier stopped at depth m_max_depth
        return;
    }

    CTRACE("assert_eq_bug", m_assertions.contains(t),
           tout << "t:\n" << mk_ismt2_pp(t, m) << "\nval:\n" << mk_ismt2_pp(val, m) << "\n";
           expr * old_val = 0;
           m_assertions.find(t, old_val);
           tout << "old_val:\n" << mk_ismt2_pp(old_val, m) << "\n";);
    m_assertions.insert(t, val);
    m_trail.push_back(t);
}


bool ctx_propagate_assertions::simplify(expr* t, expr_ref& result) {
    expr* r;
    return m_assertions.find(t, r) && (result = r, true);
}

void ctx_propagate_assertions::push() {
    m_scopes.push_back(m_trail.size());
}

void ctx_propagate_assertions::pop(unsigned num_scopes) {
    unsigned scope_lvl = m_scopes.size();
    unsigned old_trail_size = m_scopes[scope_lvl - num_scopes];
    unsigned i = m_trail.size();
    while (i > old_trail_size) {
        --i;
        expr * key = m_trail.back();
        m_assertions.erase(key);
        m_trail.pop_back();
    }
    SASSERT(m_trail.size() == old_trail_size);
    m_scopes.shrink(scope_lvl - num_scopes);
}


bool ctx_simplify_tactic::simplifier::shared(expr * t) const {
    SASSERT(m_occs);
    return t->get_ref_count() > 1 && m_occs->get_num_occs(t) > 1;
}


ctx_simplify_tactic::simplifier * ctx_propagate_assertions::translate(ast_manager & m) {
    return alloc(ctx_propagate_assertions, m);
}

tactic * mk_ctx_simplify_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ctx_simplify_tactic, m, alloc(ctx_propagate_assertions, m), p));
}


struct ctx_simplify_tactic::imp {
    struct cached_result {
        expr *          m_to;
        unsigned        m_lvl;
        cached_result * m_next;
        cached_result(expr * t, unsigned lvl, cached_result * next):
            m_to(t),
            m_lvl(lvl),
            m_next(next) {
        }
    };

    struct cache_cell {
        expr *          m_from;
        cached_result * m_result;
        cache_cell():m_from(nullptr), m_result(nullptr) {}
    };

    ast_manager &               m;
    simplifier*                 m_simp;
    small_object_allocator      m_allocator;
    svector<cache_cell>         m_cache;
    vector<ptr_vector<expr> >   m_cache_undo;
    unsigned                    m_depth;
    unsigned                    m_num_steps;
    goal_num_occurs             m_occs;
    mk_simplified_app           m_mk_app;
    unsigned long long          m_max_memory;
    unsigned                    m_max_depth;
    unsigned                    m_max_steps;
    bool                        m_bail_on_blowup;

    imp(ast_manager & _m, simplifier* simp, params_ref const & p):
        m(_m),
        m_simp(simp),
        m_allocator("context-simplifier"),
        m_occs(true, true),
        m_mk_app(m, p) {
        updt_params(p);
        m_simp->set_occs(m_occs);
    }


    ~imp() {
        pop(scope_level());
        SASSERT(scope_level() == 0);
        restore_cache(0);
        dealloc(m_simp);
        DEBUG_CODE({
            for (unsigned i = 0; i < m_cache.size(); i++) {
                CTRACE("ctx_simplify_tactic_bug", m_cache[i].m_from,
                       tout << "i: " << i << "\n" << mk_ismt2_pp(m_cache[i].m_from, m) << "\n";
                       tout << "m_result: " << m_cache[i].m_result << "\n";
                       if (m_cache[i].m_result) tout << "lvl: " << m_cache[i].m_result->m_lvl << "\n";);
                SASSERT(m_cache[i].m_from == 0);
                SASSERT(m_cache[i].m_result == 0);
            }
        });
    }

    void updt_params(params_ref const & p) {
        m_max_memory   = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_max_steps    = p.get_uint("max_steps", UINT_MAX);
        m_max_depth    = p.get_uint("max_depth", 1024);
        m_bail_on_blowup = p.get_bool("bail_on_blowup", false);
        m_simp->updt_params(p);
    }

    void checkpoint() {
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        if (m.canceled())
            throw tactic_exception(m.limit().get_cancel_msg());
    }

    bool shared(expr * t) const {
        TRACE("ctx_simplify_tactic_bug", tout << mk_pp(t, m) << "\n";);
        return t->get_ref_count() > 1 && m_occs.get_num_occs(t) > 1;
    }

    bool check_cache() {
        for (unsigned i = 0; i < m_cache.size(); i++) {
            cache_cell & cell = m_cache[i];
            if (cell.m_from != nullptr) {
                SASSERT(cell.m_result != 0);
                cached_result * curr = cell.m_result;
                while (curr) {
                    SASSERT(curr->m_lvl <= scope_level());
                    curr = curr->m_next;
                }
            }
        }
        return true;
    }

    void cache_core(expr * from, expr * to) {
        unsigned id = from->get_id();
        TRACE("ctx_simplify_tactic_cache", tout << "caching " << id << " @ " << scope_level() << "\n" << mk_ismt2_pp(from, m) << "\n--->\n" << mk_ismt2_pp(to, m) << "\n";);
        m_cache.reserve(id+1);
        cache_cell & cell = m_cache[id];
        void * mem = m_allocator.allocate(sizeof(cached_result));
        if (cell.m_from == nullptr) {
            // new_entry
            cell.m_from   = from;
            cell.m_result = new (mem) cached_result(to, scope_level(), nullptr);
            m.inc_ref(from);
            m.inc_ref(to);
        }
        else {
            // update
            cell.m_result = new (mem) cached_result(to, scope_level(), cell.m_result);
            m.inc_ref(to);
        }
        m_cache_undo.reserve(scope_level()+1);
        m_cache_undo[scope_level()].push_back(from);
    }

    void cache(expr * from, expr * to) {
        if (shared(from))
            cache_core(from, to);
    }

    unsigned scope_level() const {
        return m_simp->scope_level();
    }

    void restore_cache(unsigned lvl) {
        if (lvl >= m_cache_undo.size())
            return;
        ptr_vector<expr> & keys = m_cache_undo[lvl];
        ptr_vector<expr>::iterator it    = keys.end();
        ptr_vector<expr>::iterator begin = keys.begin();
        while (it != begin) {
            --it;
            expr * key        = *it;
            unsigned key_id   = key->get_id();
            cache_cell & cell = m_cache[key_id];
            SASSERT(cell.m_from == key);
            SASSERT(cell.m_result != 0);
            m.dec_ref(cell.m_result->m_to);
            cached_result * to_delete = cell.m_result;
            SASSERT(to_delete->m_lvl == lvl);
            TRACE("ctx_simplify_tactic_cache", tout << "uncaching: " << to_delete->m_lvl << "\n" <<
                  mk_ismt2_pp(key, m) << "\n--->\n" << mk_ismt2_pp(to_delete->m_to, m) << "\nrestoring:\n";
                  if (to_delete->m_next) tout << mk_ismt2_pp(to_delete->m_next->m_to, m); else tout << "<null>";
                  tout << "\n";);
            cell.m_result = to_delete->m_next;
            if (cell.m_result == nullptr) {
                m.dec_ref(cell.m_from);
                cell.m_from = nullptr;
            }
            m_allocator.deallocate(sizeof(cached_result), to_delete);
        }
        keys.reset();
    }

    void pop(unsigned num_scopes) {
        if (num_scopes == 0)
            return;
        SASSERT(num_scopes <= scope_level());

        unsigned lvl = scope_level();
        m_simp->pop(num_scopes);

        // restore cache
        for (unsigned i = 0; i < num_scopes; i++) {
            restore_cache(lvl);
            lvl--;
        }
        CASSERT("ctx_simplify_tactic", check_cache());
    }

    bool assert_expr(expr * t, bool sign) {
        return m_simp->assert_expr(t, sign);
    }

    bool is_cached(expr * t, expr_ref & r) {
        unsigned id = t->get_id();
        if (id >= m_cache.size())
            return false;
        cache_cell & cell = m_cache[id];
        SASSERT(cell.m_result == 0 || cell.m_result->m_lvl <= scope_level());
        if (cell.m_result != nullptr && cell.m_result->m_lvl == scope_level()) {
            SASSERT(cell.m_from == t);
            SASSERT(cell.m_result->m_to != 0);
            r = cell.m_result->m_to;
            return true;
        }
        return false;
    }

    void simplify(expr * t, expr_ref & r) {
        r = nullptr;
        if (m_depth >= m_max_depth || m_num_steps >= m_max_steps || !is_app(t) || !m_simp->may_simplify(t)) {
            r = t;
            return;
        }
        checkpoint();
        TRACE("ctx_simplify_tactic_detail", tout << "processing: " << mk_bounded_pp(t, m) << "\n";);
        if (is_cached(t, r) || m_simp->simplify(t, r)) {
            SASSERT(r.get() != 0);
            return;
        }
        m_num_steps++;
        m_depth++;
        if (m.is_or(t))
            simplify_or_and<true>(to_app(t), r);
        else if (m.is_and(t))
            simplify_or_and<false>(to_app(t), r);
        else if (m.is_ite(t))
            simplify_ite(to_app(t), r);
        else
            simplify_app(to_app(t), r);
        m_depth--;
        SASSERT(r.get() != 0);
        TRACE("ctx_simplify_tactic_detail", tout << "result:\n" << mk_bounded_pp(t, m) << "\n---->\n" << mk_bounded_pp(r, m) << "\n";);
    }

    template<bool OR>
    void simplify_or_and(app * t, expr_ref & r) {
        // go forwards
        expr_ref_buffer new_args(m);
        unsigned old_lvl = scope_level();
        bool modified = false;
        unsigned num_args = t->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = t->get_arg(i);
            expr_ref new_arg(m);
            simplify(arg, new_arg);
            if (new_arg != arg)
                modified = true;
            if (i < num_args - 1 && !m.is_true(new_arg) && !m.is_false(new_arg) && !assert_expr(new_arg, OR))
                new_arg = OR ? m.mk_true() : m.mk_false();

            if ((OR && m.is_false(new_arg)) ||
                (!OR && m.is_true(new_arg))) {
                modified = true;
                continue;
            }
            if ((OR && m.is_true(new_arg)) ||
                (!OR && m.is_false(new_arg))) {
                r = new_arg;
                pop(scope_level() - old_lvl);
                cache(t, r);
                return;
            }
            new_args.push_back(new_arg);
        }
        pop(scope_level() - old_lvl);

        // go backwards
        expr_ref_buffer new_new_args(m);
        unsigned i = new_args.size();
        while (i > 0) {
            --i;
            expr * arg = new_args[i];
            expr_ref new_arg(m);
            simplify(arg, new_arg);
            if (new_arg != arg)
                modified = true;
            if (i > 0 && !m.is_true(new_arg) && !m.is_false(new_arg) && !assert_expr(new_arg, OR))
                new_arg = OR ? m.mk_true() : m.mk_false();

            if ((OR && m.is_false(new_arg)) ||
                (!OR && m.is_true(new_arg))) {
                modified = true;
                continue;
            }
            if ((OR && m.is_true(new_arg)) ||
                (!OR && m.is_false(new_arg))) {
                r = new_arg;
                pop(scope_level() - old_lvl);
                cache(t, r);
                return;
            }
            new_new_args.push_back(new_arg);
        }
        pop(scope_level() - old_lvl);

        if (!modified) {
            r = t;
        }
        else if (new_new_args.empty()) {
            r = OR?m.mk_false():m.mk_true();
        }
        else if (new_new_args.size() == 1) {
            r = new_new_args[0];
        }
        else {
            std::reverse(new_new_args.c_ptr(), new_new_args.c_ptr() + new_new_args.size());
            m_mk_app(t->get_decl(), new_new_args.size(), new_new_args.c_ptr(), r);
        }
        cache(t, r);
    }

    void simplify_ite(app * ite, expr_ref & r) {
        expr * c = ite->get_arg(0);
        expr * t = ite->get_arg(1);
        expr * e = ite->get_arg(2);
        expr_ref new_c(m);
        unsigned old_lvl = scope_level();
        simplify(c, new_c);
        if (m.is_true(new_c)) {
            simplify(t, r);
        }
        else if (m.is_false(new_c)) {
            simplify(e, r);
        }
        else {
            expr_ref new_t(m);
            expr_ref new_e(m);
            if (!assert_expr(new_c, false)) {
                simplify(e, r);
                cache(ite, r);
                return;
            }
            simplify(t, new_t);
            pop(scope_level() - old_lvl);
            if (!assert_expr(new_c, true)) {
                r = new_t;
                cache(ite, r);
                return;
            }
            simplify(e, new_e);
            pop(scope_level() - old_lvl);
            if (c == new_c && t == new_t && e == new_e) {
                r = ite;
            }
            else if (new_t == new_e) {
                r = new_t;
            }
            else {
                expr * args[3] = { new_c.get(), new_t.get(), new_e.get() };
                TRACE("ctx_simplify_tactic_ite_bug",
                      tout << "mk_ite\n" << mk_ismt2_pp(new_c.get(), m) << "\n" << mk_ismt2_pp(new_t.get(), m)
                      << "\n" << mk_ismt2_pp(new_e.get(), m) << "\n";);
                m_mk_app(ite->get_decl(), 3, args, r);
            }
        }
        cache(ite, r);
    }

    void simplify_app(app * t, expr_ref & r) {
        if (t->get_num_args() == 0) {
            r = t;
            return;
        }
        expr_ref_buffer new_args(m);
        bool modified = false;
        unsigned num_args = t->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = t->get_arg(i);
            expr_ref new_arg(m);
            simplify(arg, new_arg);
            CTRACE("ctx_simplify_tactic_bug", new_arg.get() == 0, tout << mk_ismt2_pp(arg, m) << "\n";);
            SASSERT(new_arg);
            if (new_arg != arg)
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified) {
            r     = t;
        }
        else {
            m_mk_app(t->get_decl(), new_args.size(), new_args.c_ptr(), r);
        }
    }

    unsigned expr_size(expr* s) {
        ast_mark visit;
        unsigned sz = 0;
        ptr_vector<expr> todo;
        todo.push_back(s);
        while (!todo.empty()) {
            s = todo.back();
            todo.pop_back();
            if (visit.is_marked(s)) {
                continue;
            }
            visit.mark(s, true);
            ++sz;
            for (unsigned i = 0; is_app(s) && i < to_app(s)->get_num_args(); ++i) {
                todo.push_back(to_app(s)->get_arg(i));
            }
        }
        return sz;
    }

    void process_goal(goal & g) {
        SASSERT(scope_level() == 0);
        // go forwards
        unsigned old_lvl = scope_level();
        unsigned sz = g.size();
        expr_ref r(m);
        for (unsigned i = 0; !g.inconsistent() && i < sz; ++i) {
            m_depth = 0;
            simplify(g.form(i), r);
            if (i < sz - 1 && !m.is_true(r) && !m.is_false(r) && !g.dep(i) && !assert_expr(r, false)) {
                r = m.mk_false();
            }
            g.update(i, r, nullptr, g.dep(i));
        }
        pop(scope_level() - old_lvl);

        m_occs(g);

        // go backwards
        sz = g.size();
        for (unsigned i = sz; !g.inconsistent() && i > 0; ) {
            m_depth = 0;
            --i;
            simplify(g.form(i), r);
            if (i > 0 && !m.is_true(r) && !m.is_false(r) && !g.dep(i) && !assert_expr(r, false)) {
                r = m.mk_false();
            }
            g.update(i, r, nullptr, g.dep(i));
        }
        pop(scope_level() - old_lvl);
        SASSERT(scope_level() == 0);
    }

    void process(expr * s, expr_ref & r) {
        TRACE("ctx_simplify_tactic", tout << "simplifying:\n" << mk_ismt2_pp(s, m) << "\n";);
        SASSERT(scope_level() == 0);
        m_depth = 0;
        simplify(s, r);
        SASSERT(scope_level() == 0);
        SASSERT(m_depth == 0);
        SASSERT(r.get() != 0);
        TRACE("ctx_simplify_tactic", tout << "result\n" << mk_ismt2_pp(r, m) << " :num-steps " << m_num_steps << "\n";
              tout << "old size: " << expr_size(s) << " new size: " << expr_size(r) << "\n";);
        if (m_bail_on_blowup && expr_size(s) < expr_size(r)) {
            r = s;
        }
    }

    void operator()(goal & g) {
        SASSERT(g.is_well_sorted());
        m_occs.reset();
        m_occs(g);
        m_num_steps = 0;
        tactic_report report("ctx-simplify", g);
        if (g.proofs_enabled()) {
            expr_ref r(m);
            unsigned sz = g.size();
            for (unsigned i = 0; !g.inconsistent() && i < sz; ++i) {
                expr * t = g.form(i);
                process(t, r);
                proof* new_pr = m.mk_modus_ponens(g.pr(i), m.mk_rewrite(t, r));
                g.update(i, r, new_pr, g.dep(i));
            }
        }
        else {
            process_goal(g);
        }
        IF_VERBOSE(TACTIC_VERBOSITY_LVL, verbose_stream() << "(ctx-simplify :num-steps " << m_num_steps << ")\n";);
        SASSERT(g.is_well_sorted());
    }

};

ctx_simplify_tactic::ctx_simplify_tactic(ast_manager & m, simplifier* simp, params_ref const & p):
    m_imp(alloc(imp, m, simp, p)),
    m_params(p) {
}

tactic * ctx_simplify_tactic::translate(ast_manager & m) {
    return alloc(ctx_simplify_tactic, m, m_imp->m_simp->translate(m), m_params);
}

ctx_simplify_tactic::~ctx_simplify_tactic() {
    dealloc(m_imp);
}

void ctx_simplify_tactic::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void ctx_simplify_tactic::get_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    insert_max_steps(r);
    r.insert("max_depth", CPK_UINT, "(default: 1024) maximum term depth.");
    r.insert("propagate_eq", CPK_BOOL, "(default: false) enable equality propagation from bounds.");
}

void ctx_simplify_tactic::operator()(goal_ref const & in,
                                     goal_ref_buffer & result) {
    (*m_imp)(*(in.get()));
    in->inc_depth();
    result.push_back(in.get());
}


void ctx_simplify_tactic::cleanup() {
    ast_manager & m   = m_imp->m;
    imp * d = alloc(imp, m, m_imp->m_simp->translate(m), m_params);
    std::swap(d, m_imp);
    dealloc(d);
}

