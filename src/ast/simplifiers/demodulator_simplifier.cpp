/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    demodulator_simplifier.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-12-4

--*/

#include "ast/simplifiers/demodulator_simplifier.h"

demodulator_index::~demodulator_index() {
    reset();
}

void demodulator_index::reset() {
    for (auto& [k, v] : m_fwd_index)
        dealloc(v);
    for (auto& [k, v] : m_bwd_index)
        dealloc(v);
    m_fwd_index.reset();
    m_bwd_index.reset();
}

void demodulator_index::add(func_decl* f, unsigned i, obj_map<func_decl, uint_set*>& map) {
    uint_set* s;
    if (!map.find(f, s)) {
        s = alloc(uint_set);
        map.insert(f, s);
    }
    s->insert(i);
}

void demodulator_index::del(func_decl* f, unsigned i, obj_map<func_decl, uint_set*>& map) {
    uint_set* s;
    if (map.find(f, s))
        s->remove(i);
}

void demodulator_index::insert_bwd(expr* e, unsigned i) {
    struct proc {
        unsigned i;
        demodulator_index& idx;
        proc(unsigned i, demodulator_index& idx) :i(i), idx(idx) {}
        void operator()(app* a) {
            if (a->get_num_args() > 0 && is_uninterp(a))
                idx.add(a->get_decl(), i, idx.m_bwd_index);
        }
        void operator()(expr* e) {}
    };
    proc p(i, *this);
    for_each_expr(p, e);
}

void demodulator_index::remove_bwd(expr* e, unsigned i) {
    struct proc {
        unsigned i;
        demodulator_index& idx;
        proc(unsigned i, demodulator_index& idx) :i(i), idx(idx) {}
        void operator()(app* a) {
            if (a->get_num_args() > 0 && is_uninterp(a))
                idx.del(a->get_decl(), i, idx.m_bwd_index);
        }
        void operator()(expr* e) {}
    };
    proc p(i, *this);
    for_each_expr(p, e);
}

std::ostream& demodulator_index::display(std::ostream& out) const {
    out << "forward\n";
    for (auto& [k, v] : m_fwd_index)
        out << mk_pp(k, m) << " : " << *v << "\n";
    out << "backward\n";
    for (auto& [k, v] : m_bwd_index)
        out << mk_pp(k, m) << " : " << *v << "\n";
    return out;
}


demodulator_simplifier::demodulator_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& st):
    dependent_expr_simplifier(m, st),
    m_index(m),
    m_util(m),
    m_match_subst(m),
    m_rewriter(m),
    m_pinned(m)
{
    std::function<bool(func_decl* f, expr_ref_vector const& args, expr_ref& r)> rw = [&](func_decl* f, expr_ref_vector const& args, expr_ref& r) {
        return rewrite1(f, args, r);
    };
    m_rewriter.set_rewrite1(rw);
}

void demodulator_simplifier::rewrite(unsigned i) {
    if (m_index.empty())
        return;

    m_dependencies.reset();
    expr* f = fml(i);
    expr_ref r = m_rewriter.rewrite(f);
    if (r == f)
        return;
    expr_dependency_ref d(dep(i), m);
    for (unsigned j : m_dependencies)
        d = m.mk_join(d, dep(j));
    m_fmls.update(i, dependent_expr(m, r, nullptr, d));
}

bool demodulator_simplifier::rewrite1(func_decl* f, expr_ref_vector const& args, expr_ref& np) {
    uint_set* set;
    if (!m_index.find_fwd(f, set))
        return false;

    TRACE("demodulator", tout << "trying to rewrite: " << f->get_name() << " args:" << args << "\n"; m_index.display(tout));

    for (unsigned i : *set) {

        auto const& [lhs, rhs] = m_rewrites[i];

        TRACE("demodulator", tout << "Matching with demodulator: " << i << " " << mk_pp(lhs, m) << "\n");

        if (lhs->get_num_args() != args.size())
            continue;

        SASSERT(lhs->get_decl() == f);


        if (m_match_subst(lhs, rhs, args.data(), np)) {
            TRACE("demodulator_bug", tout << "succeeded...\n" << mk_pp(rhs, m) << "\n===>\n" << np << "\n");
            if (dep(i))
                m_dependencies.insert(i);
            return true;
        }
    }

    return false;
}

void demodulator_simplifier::reschedule_processed(func_decl* f) {
    uint_set* set = nullptr;
    if (!m_index.find_bwd(f, set))
        return;
    uint_set tmp;
    for (auto i : *set)
        if (m_processed.contains(i))
            tmp.insert(i);
    for (auto i : tmp) {
        m_processed.remove(i);
        m_index.remove_fwd(f, i);
        m_index.remove_bwd(fml(i), i);
        m_todo.push_back(i);
    }
}

void demodulator_simplifier::reschedule_demodulators(func_decl* f, expr* lhs) {
    uint_set* set;
    if (!m_index.find_bwd(f, set))
        return;
    uint_set all_occurrences(*set);
    for (unsigned i : all_occurrences) {
        app_expr_pair p;
        if (!m_rewrites.find(i, p))
            continue;        
        if (!m_match_subst.can_rewrite(fml(i), lhs))
            continue;
        SASSERT(f == p.first->get_decl());
        m_index.remove_fwd(f, i);
        m_index.remove_bwd(fml(i), i);
        m_todo.push_back(i);
    }
}

void demodulator_simplifier::reset() {
    m_pinned.reset();
    m_index.reset();
    m_processed.reset();
    m_todo.reset();
    unsigned max_vid = 1;
    for (unsigned i : indices())
        max_vid = std::max(max_vid, m_util.max_var_id(fml(i)));
    m_match_subst.reserve(max_vid);
}

void demodulator_simplifier::reduce() {
    reset();
    for (unsigned i : indices())
        m_todo.push_back(i);

    app_ref large(m);
    expr_ref small(m);
    while (!m_todo.empty()) {
        unsigned i = m_todo.back();
        m_todo.pop_back();
        rewrite(i);
        if (m_util.is_demodulator(fml(i), large, small)) {
            func_decl* f = large->get_decl();
            TRACE("demodulator", tout << i << " " << mk_pp(fml(i), m) << ": " << large << " ==> " << small << "\n");
            reschedule_processed(f);
            reschedule_demodulators(f, large);
            m_index.insert_fwd(f, i);
            m_rewrites.insert(i, app_expr_pair(large, small));
            m_pinned.push_back(large);
            m_pinned.push_back(small);
        }
        else
            m_processed.insert(i);
        m_index.insert_bwd(fml(i), i);
    }
}
