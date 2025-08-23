/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    ho_matcher

Abstract:

    second and higher-order matcher
    
Author:

    Nikolaj Bjorner (nbjorner) 2025-07-07

--*/

#pragma once

#include "util/trail.h"
#include "util/dlist.h"
#include "util/uint_set.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/array_rewriter.h"
#include "ast/rewriter/var_subst.h"


namespace euf {

    class ho_matcher;

    class work_state {
        enum state {
            init_s,
            project_s,
            app_s, 
            done_s
        };
        state m_state = state::init_s;
        unsigned m_index = 0;
        bool m_in_scope = false;

    public:
        void set_init() {
            m_state = state::init_s;
            m_index = 0;
            m_in_scope = false;
        }
        bool is_init() const { return m_state == state::init_s; }
        bool is_project() const { return m_state == state::project_s; }
        bool is_app() const { return m_state == state::app_s && m_index == 0; }
        bool is_done() const { return m_state == state::done_s; }
        void set_project() { m_state = state::project_s; m_index = 0; }
        void set_app() { m_state = state::app_s; m_index = 0; }
        void set_done() { m_state = state::done_s; }
        void inc_index() { ++m_index; }
        void set_index(unsigned i) { m_index = i; }
        unsigned index() const { return m_index; }
        bool in_scope() const { return m_in_scope; }
        void set_in_scope(bool f = true) { m_in_scope = f; }
    };

    class match_goal : public dll_base<match_goal>, public work_state {
        unsigned base_offset = 0;
        unsigned delta_offset = 0; // offset of term
    public:
        expr_ref pat, t;
        unsigned level = 0; // level backtrack level
       
        void reset() {
            pat.reset();
            t.reset();
            level = 0;
            base_offset = 0;
            delta_offset = 0;
        }

        bool operator==(match_goal const& other) const {
            return pat == other.pat && t == other.t && base_offset == other.base_offset && delta_offset == other.delta_offset;
        }

        bool operator!=(match_goal const& other) const {
            return !(*this == other);
        }

        match_goal(unsigned level, unsigned offset, expr_ref const& pat, expr_ref const& t) noexcept : 
            base_offset(offset), pat(pat), t(t),  level(level)  {}

        unsigned term_offset() const { return base_offset + delta_offset; }
        unsigned pat_offset() const { return base_offset + delta_offset; }

        std::ostream& display(std::ostream& out) const {
            return out << "[" << level << ":" << base_offset + delta_offset << "] " << pat << " ~ " << t << "\n";
        }
    };

    class match_goals {
    protected:
        ast_manager &m;
        ho_matcher& ho;
        
        match_goal* m_expensive = nullptr, *m_cheap = nullptr;
        match_goal* pop(match_goal*& q);
        
    public:
        match_goals(ho_matcher& em, ast_manager &m) : m(m), ho(em) {}
        bool empty() const { return m_cheap == nullptr && m_expensive == nullptr; }
        void reset() { m_cheap = m_expensive = nullptr; }
        void push(unsigned level, unsigned offset, expr_ref const& pat, expr_ref const& t);
        void push(unsigned level, unsigned offset, expr* p, expr* t) { push(level, offset, expr_ref(p, m), expr_ref(t, m)); }
        match_goal* pop();

        std::ostream& display(std::ostream& out) const;

    };

    class ho_subst {
        expr_ref_vector m_subst;
    public:
        ho_subst(ast_manager& m) :
            m_subst(m) {            
        }
        void resize(unsigned n) {
            m_subst.resize(n, nullptr);
        }

        unsigned size() const {
            return m_subst.size();
        }

        void set(unsigned v, expr* t) {
            SASSERT(!m_subst.get(v));
            m_subst[v] = t;
        }

        expr* get(unsigned v) const {
            return m_subst.get(v);
        }

        void unset(unsigned v) {
            SASSERT(m_subst.get(v));
            m_subst[v] = nullptr;
        }

        std::ostream& display(std::ostream& out) const {
            auto& m = m_subst.get_manager();
            for (unsigned i = 0; i < m_subst.size(); ++i) {
                if (m_subst.get(i)) {
                    out << "v" << i << " -> " << mk_pp(m_subst.get(i), m) << "\n";
                }
            }
            return out;
        }
    };

    class unitary_patterns {
        ast_manager& m;
        array_util a;
        vector<expr_ref_vector> m_patterns;
        vector<svector<lbool>>  m_is_unitary;
        svector<std::pair<unsigned, expr*>> m_todo;

        lbool find(unsigned offset, expr* p) const {
            if (offset >= m_is_unitary.size())
                return l_undef;
            if (p->get_id() >= m_is_unitary[offset].size())
                return l_undef;
            return m_is_unitary[offset][p->get_id()];
        }

        void set_unitary(unsigned offset, expr* p, lbool is_unitary) {
            if (offset >= m_is_unitary.size())
                m_is_unitary.resize(offset + 1);
            if (p->get_id() >= m_is_unitary[offset].size())
                m_is_unitary[offset].resize(p->get_id() + 1, l_undef);
            m_is_unitary[offset][p->get_id()] = is_unitary;
        }

    public:
        unitary_patterns(ast_manager& m) : m(m), a(m) {}

        bool is_unitary(unsigned offset, expr* p) const {
            return find(offset, p) == l_true;
        }

        bool is_flex(unsigned offset, expr* e) const {
            bool is_select = false;
            expr* t = e;
            while (a.is_select(t))
                t = to_app(t)->get_arg(0), is_select = true;
            if (is_select && is_var(t) && to_var(t)->get_idx() >= offset) {
                // check if e is a pattern.
                return true;
            }
            return false;
        }

        void add_pattern(expr* p) {
            m_todo.push_back({ 0, p });
            while (!m_todo.empty()) {
                auto [o, p] = m_todo.back();
                if (l_undef != find(o, p)) {
                    m_todo.pop_back();
                    continue;
                }

                // ((M N) K)
                // if M is a meta variable and N, K are not patterns it is non_unitary
                // otherwise we declare it as (locally) unitary. It will be inserted into the "cheap" queue.
                // subterms can be non-unitary.

                if (is_app(p)) {
                    auto a = to_app(p);
                    auto sz = m_todo.size();
                    lbool is_unitary = l_true;
                    for (auto arg : *a) {
                        switch (find(o, arg)) {
                        case l_undef:
                            m_todo.push_back({ o, arg });
                            break;                       
                        default:
                            break;
                        }
                    }
                    if (sz != m_todo.size())
                        continue;
                    if (is_flex(o, p))
                        is_unitary = l_false;
                    set_unitary(o, p, is_unitary);
                    m_todo.pop_back();
                }
                else if (is_var(p)) 
                    set_unitary(o, p, l_true);              
                else {
                    auto q = to_quantifier(p);
                    unsigned nd = q->get_num_decls();
                    auto body = q->get_expr();
                    switch (find(o + nd, body)) {
                    case l_undef:
                        m_todo.push_back({ o + nd, body });
                        break;
                    default:
                        m_todo.pop_back();
                        set_unitary(o, p, l_true);
                        break;
                    }
                }
            }
        }

    };

    struct undo_set : public trail {
        ho_subst& s;
        unsigned v;
        undo_set(ho_subst& s, unsigned v) : s(s), v(v) {}
        void undo() override {
            s.unset(v);
        }
    };

    struct undo_resize : public trail {
        ho_subst& s;
        unsigned old_size;
        undo_resize(ho_subst& s) : s(s), old_size(s.size()) {}
        void undo() override {
            s.resize(old_size);
        }
    };


    template<typename V>
    class update_value : public trail {
        V& lval;
        V  rval;
    public:
        update_value(V& lval, V rval) : lval(lval), rval(rval) {}
        void undo() override {
            lval = rval;
            rval.reset();
        }
    };

    struct remove_dll : public trail {
        match_goal*& m_list;
        match_goal* m_value;
        remove_dll(match_goal*& list, match_goal* value) : m_list(list), m_value(value) {}
        void undo() override {
            dll_base<match_goal>::remove_from(m_list, m_value);
        }
    };

    struct insert_dll : public trail {
        match_goal*& m_list;
        match_goal* m_value;
        insert_dll(match_goal*& list, match_goal* value) : m_list(list), m_value(value) {}
        void undo() override {
            dll_base<match_goal>::push_to_front(m_list, m_value);
        }
    };

    class ho_matcher {
    protected:
        friend class match_goals;
        friend class test_ho_matcher;
        ast_manager &m;
        trail_stack& m_trail;
        ho_subst         m_subst;
        match_goals      m_goals;
        unitary_patterns m_unitary;
        ptr_vector<match_goal> m_backtrack;
        mutable array_rewriter   m_rewriter;
        array_util       m_array;
        obj_map<app, app*>     m_pat2hopat, m_hopat2pat;
        obj_map<quantifier, quantifier*> m_q2hoq, m_hoq2q;
        obj_map<app, expr_free_vars> m_hopat2free_vars;
        obj_map<app, svector<std::pair<unsigned, expr*>>> m_pat2abs;
        expr_ref_vector        m_ho_patterns, m_ho_qs;

    	void resume();

        void push_backtrack();

        void backtrack();

        bool consume_work(match_goal& wi);

        expr_ref whnf(expr* e, unsigned offset) const;
        
        bool is_bound_var(expr* v, unsigned offset) const { return is_var(v) && to_var(v)->get_idx() < offset; }

        bool is_meta_var(expr* v, unsigned offset) const { return is_var(v) && to_var(v)->get_idx() >= offset; }

        bool is_closed(expr* v, unsigned scopes, unsigned offset) const;

        void add_binding(var* v, unsigned offset, expr* t);

        expr_ref mk_project(unsigned num_lambdas, unsigned xi, sort* array_sort);

        void bind_lambdas(unsigned j, sort* s, expr_ref& body);

        lbool are_equal(unsigned o1, expr* p, unsigned o2, expr* t) const;

        bool is_pattern(expr* p, unsigned offset, expr* t);

        expr_ref abstract_pattern(expr* p, unsigned offset, expr* t);

        void reduce(match_goal& wi);

        trail_stack& trail() { return m_trail; }

        std::ostream& display(std::ostream& out) const;

        bool is_cheap(match_goal const& g) const { return m_unitary.is_unitary(g.pat_offset(), g.pat); }

        void add_pattern(expr* p) {
            m_unitary.add_pattern(p);
        }

        void search();

        std::function<void(ho_subst&)> m_on_match;

    public:

        ho_matcher(ast_manager& m, trail_stack &trail) : 
            m(m),
            m_trail(trail),
            m_subst(m),
            m_goals(*this, m),
            m_unitary(m),
            m_rewriter(m),
            m_array(m),
            m_ho_patterns(m),
            m_ho_qs(m)
        {
        }

        void set_on_match(std::function<void(ho_subst&)>& on_match) { m_on_match = on_match; }

        void operator()(expr *pat, expr *t, unsigned num_vars);

        void operator()(expr* pat, expr* t, unsigned num_bound, unsigned num_vars);

        std::pair<quantifier*, app*> compile_ho_pattern(quantifier* q, app* p);

        bool is_ho_pattern(app* p);

        void refine_ho_match(app* p, expr_ref_vector& s);

        bool is_free(app* p, unsigned i) const { return m_hopat2free_vars[p].contains(i); }

        quantifier* hoq2q(quantifier* q) const { return m_hoq2q[q]; }

    };
}
