/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_ematch.cpp

Abstract:

    E-matching quantifier instantiation plugin

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

Todo:

- clausify
- generations
- insert instantiations into priority queue 
- cache instantiations and substitutions
- nested quantifiers
- non-cnf quantifiers (handled in q_solver)

Done:

- propagate without instantiations, produce explanations for eval

--*/

#include "ast/ast_util.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include "solver/solver.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/q_mam.h"
#include "sat/smt/q_ematch.h"


namespace q {

    struct ematch::scoped_mark_reset {
        ematch& e;
        scoped_mark_reset(ematch& e): e(e) {}
        ~scoped_mark_reset() { e.m_mark.reset(); }
    };

    ematch::ematch(euf::solver& ctx, solver& s):
        ctx(ctx),
        m_qs(s),
        m(ctx.get_manager()),
        m_infer_patterns(m, ctx.get_config())
    {
        std::function<void(euf::enode*, euf::enode*)> _on_merge = 
            [&](euf::enode* root, euf::enode* other) { 
            on_merge(root, other); 
        };
        ctx.get_egraph().set_on_merge(_on_merge);
        m_mam = mam::mk(ctx, *this);
    }

    void ematch::ensure_ground_enodes(expr* e) {
        mam::ground_subterms(e, m_ground);
        for (expr* g : m_ground) 
            m_qs.e_internalize(g);
    }

    void ematch::ensure_ground_enodes(clause const& c) {
        quantifier* q = c.m_q;
        unsigned num_patterns = q->get_num_patterns();
        for (unsigned i = 0; i < num_patterns; i++) 
            ensure_ground_enodes(q->get_pattern(i));
        for (auto lit : c.m_lits) {
            ensure_ground_enodes(lit.lhs);
            ensure_ground_enodes(lit.rhs);
        }
    }

    sat::ext_justification_idx ematch::mk_justification(unsigned idx, clause& c, euf::enode* const* b) {
        void* mem = ctx.get_region().allocate(justification::get_obj_size());
        sat::constraint_base::initialize(mem, &m_qs);
        bool sign = false;
        expr* l = nullptr, *r = nullptr;            
        lit lit(expr_ref(l,m), expr_ref(r, m), sign); 
        if (idx != UINT_MAX)
            lit = c[idx];
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) justification(lit, c, b);
        return constraint->to_index();
    }

    void ematch::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) {
        auto& j = justification::from_index(idx);
        clause& c = j.m_clause;
        unsigned l_idx = 0;
        for (; l_idx < c.size(); ++l_idx) {
            if (c[l_idx].lhs == j.m_lhs && c[l_idx].rhs == j.m_rhs && c[l_idx].sign == j.m_sign)
                break;
        }
        explain(c, l_idx, j.m_binding);
        r.push_back(c.m_literal);
        (void)probing; // ignored
    }

    std::ostream& ematch::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        auto& j = justification::from_index(idx);
        auto& c = j.m_clause;
        out << "ematch: ";
        for (auto const& lit : c.m_lits)
            lit.display(out) << " ";
        unsigned num_decls = c.num_decls();
        for (unsigned i = 0; i < num_decls; ++i)
            out << ctx.bpp(j.m_binding[i]) << " ";
        out << "-> ";
        lit lit(expr_ref(j.m_lhs, m), expr_ref(j.m_rhs, m), j.m_sign);
        if (j.m_lhs) 
            lit.display(out);
        else 
            out << "false";
        return out;
    }

    void ematch::explain(clause& c, unsigned literal_idx, euf::enode* const* b) {
        unsigned n = c.num_decls();
        for (unsigned i = c.size(); i-- > 0; ) {
            if (i == literal_idx) 
                continue;
            auto const& lit = c[i];
            if (lit.sign) 
                explain_eq(n, b, lit.lhs, lit.rhs);
            else 
                explain_diseq(n, b, lit.lhs, lit.rhs);
        }
    }

    void ematch::explain_eq(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        SASSERT(l_true == compare(n, binding, s, t));
        if (s == t)
            return;
        euf::enode* sn = eval(n, binding, s);
        euf::enode* tn = eval(n, binding, t);
        if (sn && tn) {
            SASSERT(sn->get_root() == tn->get_root());
            ctx.add_antecedent(sn, tn);
            return;
        }
        if (!sn && tn) {
            std::swap(sn, tn);
            std::swap(s, t);
        }
        if (sn && !tn) {
            for (euf::enode* s1 : euf::enode_class(sn)) {
                if (l_true == compare_rec(n, binding, t, s1->get_expr())) {
                    ctx.add_antecedent(sn, s1);
                    explain_eq(n, binding, t, s1->get_expr());
                    return;
                }
            }
            UNREACHABLE();
        }
        SASSERT(is_app(s) && is_app(t));
        SASSERT(to_app(s)->get_decl() == to_app(t)->get_decl());
        for (unsigned i = to_app(s)->get_num_args(); i-- > 0; ) 
            explain_eq(n, binding, to_app(s)->get_arg(i), to_app(t)->get_arg(i));
    }

    void ematch::explain_diseq(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        SASSERT(l_false == compare(n, binding, s, t));
        if (m.are_distinct(s, t))
            return;
        euf::enode* sn = eval(n, binding, s);
        euf::enode* tn = eval(n, binding, t);
        if (sn && tn && ctx.get_egraph().are_diseq(sn, tn)) {
            ctx.add_diseq_antecedent(sn, tn);
            return;
        }
        if (!sn && tn) {
            std::swap(sn, tn);
            std::swap(s, t);
        }
        if (sn && !tn) {
            for (euf::enode* s1 : euf::enode_class(sn)) {
                if (l_false == compare_rec(n, binding, t, s1->get_expr())) {
                    ctx.add_antecedent(sn, s1);
                    explain_diseq(n, binding, t, s1->get_expr());
                    return;
                }
            }
            UNREACHABLE();
        }
        SASSERT(is_app(s) && is_app(t));
        app* at = to_app(t);
        app* as = to_app(s);
        SASSERT(as->get_decl() == at->get_decl());
        for (unsigned i = as->get_num_args(); i-- > 0; ) {
            if (l_false == compare_rec(n, binding, as->get_arg(i), at->get_arg(i))) {                
                explain_eq(n, binding, as->get_arg(i), at->get_arg(i));
                return;
            }
        }
        UNREACHABLE();
    }

    struct restore_watch : public trail<euf::solver> {
        vector<unsigned_vector>& v;
        unsigned idx, offset;
        restore_watch(vector<unsigned_vector>& v, unsigned idx):
            v(v), idx(idx), offset(v[idx].size()) {}
        void undo(euf::solver& ctx) override {
            v[idx].shrink(offset);
        }
    };

    void ematch::on_merge(euf::enode* root, euf::enode* other) {
        TRACE("q", tout << "on-merge " << ctx.bpp(root) << " " << ctx.bpp(other) << "\n";);
        SASSERT(root->get_root() == other->get_root());
        unsigned root_id = root->get_expr_id();
        unsigned other_id = other->get_expr_id();
        m_watch.reserve(std::max(root_id, other_id) + 1);

        insert_to_propagate(root_id);
        insert_to_propagate(other_id);

        if (!m_watch[other_id].empty()) {        
            ctx.push(restore_watch(m_watch, root_id));
            m_watch[root_id].append(m_watch[other_id]);
        }
   
        m_mam->on_merge(root, other);
        if (m_lazy_mam)
            m_lazy_mam->on_merge(root, other);
        m_mam->relevant_eh(other, false);
    }

    // watch only nodes introduced in bindings or ground arguments of functions
    // or functions that have been inserted.

    void ematch::add_watch(euf::enode* n, unsigned idx) {
        unsigned root_id = n->get_root_id();
        m_watch.reserve(root_id + 1);
        ctx.push(restore_watch(m_watch, root_id));
        m_watch[root_id].push_back(idx);
    }

    void ematch::init_watch(expr* e, unsigned clause_idx) {
        ptr_buffer<expr> todo;
        scoped_mark_reset _sr(*this);
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            if (m_mark.is_marked(t))
                continue;
            todo.pop_back();
            m_mark.mark(t);
            if (is_ground(t)) {
                add_watch(ctx.get_egraph().find(t), clause_idx);
                continue;
            }
            if (!is_app(t))
                continue;
            for (expr* arg : *to_app(t))
                todo.push_back(arg);
        }
    }

    void ematch::init_watch(clause& c, unsigned idx) {
        for (auto lit : c.m_lits) {
            if (!is_ground(lit.lhs))
                init_watch(lit.lhs, idx);
            if (!is_ground(lit.rhs))
                init_watch(lit.rhs, idx);
        }
    }

    struct ematch::remove_binding : public trail<euf::solver> {
        clause& c;
        binding* b;
        remove_binding(clause& c, binding* b): c(c), b(b) {}
        void undo(euf::solver& ctx) override {
            binding::remove_from(c.m_bindings, b);
        }        
    };

    struct ematch::insert_binding : public trail<euf::solver> {
        clause& c;
        binding* b;
        insert_binding(clause& c, binding* b): c(c), b(b) {}
        void undo(euf::solver& ctx) override {
            binding::push_to_front(c.m_bindings, b);
        }
    };

    ematch::binding* ematch::alloc_binding(unsigned n) {
        unsigned sz = sizeof(binding) + sizeof(euf::enode* const*)*n;
        void* mem = ctx.get_region().allocate(sz);
        return new (mem) binding();
    }

    std::ostream& ematch::lit::display(std::ostream& out) const {
        ast_manager& m = lhs.m();
        if (m.is_true(rhs) && !sign) 
            return out << lhs;
        if (m.is_false(rhs) && !sign) 
            return out << "(not " << lhs << ")";
        return 
            out << mk_bounded_pp(lhs, lhs.m(), 2) 
                << (sign ? " != " : " == ") 
                << mk_bounded_pp(rhs, rhs.m(), 2);
    }


    void ematch::clause::add_binding(ematch& em, euf::enode* const* _binding) {
        unsigned n = num_decls();
        binding* b = em.alloc_binding(n);
        b->init(b);
        for (unsigned i = 0; i < n; ++i)
            b->m_nodes[i] = _binding[i];        
        binding::push_to_front(m_bindings, b);
        em.ctx.push(remove_binding(*this, b));
    }

    void ematch::on_binding(quantifier* q, app* pat, euf::enode* const* _binding) {
        TRACE("q", tout << "on-binding " << mk_pp(q, m) << "\n";);
        clause& c = *m_clauses[m_q2clauses[q]];
        if (!propagate(_binding, c))
            c.add_binding(*this, _binding);
    }

    std::ostream& ematch::clause::display(euf::solver& ctx, std::ostream& out) const {
        out << "clause:\n";
        for (auto const& lit : m_lits)
            lit.display(out) << "\n";
        binding* b = m_bindings;
        if (b) {
            do {
                for (unsigned i = 0; i < num_decls(); ++i)
                    out << ctx.bpp(b->nodes()[i]) << " ";
                out << "\n";            
                b = b->next();
            }
            while (b != m_bindings);
        }
        return out;
    }

    bool ematch::propagate(euf::enode* const* binding, clause& c) {
        TRACE("q", c.display(ctx, tout) << "\n";);
        unsigned clause_idx = m_q2clauses[c.m_q];
        scoped_mark_reset _sr(*this);

        unsigned idx = UINT_MAX;
        unsigned sz = c.m_lits.size();
        unsigned n = c.num_decls();
        m_indirect_nodes.reset();
        for (unsigned i = 0; i < sz; ++i) {
            unsigned lim = m_indirect_nodes.size();
            lit l = c[i];
            lbool cmp = compare(n, binding, l.lhs, l.rhs);
            switch (cmp) {
            case l_false:
                m_indirect_nodes.shrink(lim);
                if (!l.sign)
                    break;
                if (i > 0)
                    std::swap(c[0], c[i]);
                return true;
            case l_true:
                m_indirect_nodes.shrink(lim);
                if (l.sign)
                    break;
                if (i > 0)
                    std::swap(c[0], c[i]);
                return true;
            case l_undef:
                TRACE("q", tout << l.lhs << " ~~ " << l.rhs << " is undef\n";);
                if (idx == 0) {
                    // attach bindings and indirect nodes
                    // to watch
                    for (euf::enode* n : m_indirect_nodes)
                        add_watch(n, clause_idx);
                    for (unsigned j = c.num_decls(); j-- > 0; )
                        add_watch(binding[j], clause_idx);
                    if (i > 1) 
                        std::swap(c[1], c[i]);
                    return false;
                }
                else if (i > 0) 
                    std::swap(c[0], c[i]);
                idx = 0;
                break;
            }
        }
        TRACE("q", tout << "instantiate " << (idx == UINT_MAX ? "clause is false":"unit propagate") << "\n";);

#if 1
        auto j_idx = mk_justification(idx, c, binding);
        if (idx == UINT_MAX) 
            ctx.set_conflict(j_idx);
        else 
            ctx.propagate(instantiate(c, binding, c[idx]), j_idx);
#else
        instantiate(c, binding);
#endif
        return true;
    }

    // vanilla instantiation method.
    void ematch::instantiate(euf::enode* const* binding, clause& c) {
        expr_ref_vector _binding(m);
        quantifier* q = c.m_q;
        for (unsigned i = 0; i < c.num_decls(); ++i)
            _binding.push_back(binding[i]->get_expr());
        var_subst subst(m);
        expr_ref result = subst(q->get_expr(), _binding);
        sat::literal result_l = ctx.mk_literal(result);
        if (is_exists(q))
            result_l.neg();
        m_qs.add_clause(c.m_literal, result_l);
    }

    sat::literal ematch::instantiate(clause& c, euf::enode* const* binding, lit const& l) {
        expr_ref_vector _binding(m);
        quantifier* q = c.m_q;
        for (unsigned i = 0; i < c.num_decls(); ++i)
            _binding.push_back(binding[i]->get_expr());
        var_subst subst(m);
        if (m.is_true(l.rhs)) {
            SASSERT(!l.sign);
            return ctx.mk_literal(subst(l.lhs, _binding));
        }
        else if (m.is_false(l.rhs)) {
            SASSERT(!l.sign);
            return ~ctx.mk_literal(subst(l.lhs, _binding));
        }        
        expr_ref fml(m.mk_eq(l.lhs, l.rhs), m);
        fml = subst(fml, _binding);
        return l.sign ? ~ctx.mk_literal(fml) : ctx.mk_literal(fml);
    }

    lbool ematch::compare(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        euf::enode* sn = eval(n, binding, s);
        euf::enode* tn = eval(n, binding, t);
        if (sn) sn = sn->get_root();
        if (tn) tn = tn->get_root();
        TRACE("q", tout << mk_pp(s, m) << " ~~ " << mk_pp(t, m) << "\n";
              tout << ctx.bpp(sn) << " " << ctx.bpp(tn) << "\n";);
        
        lbool c;
        if (sn && sn == tn)
            return l_true;
        if (sn && tn && ctx.get_egraph().are_diseq(sn, tn))
            return l_false;
        if (sn && tn)
            return l_undef;
        if (!sn && !tn) 
            return compare_rec(n, binding, s, t);
        if (!tn && !sn)
            return l_undef;
        if (!tn && sn) {
            std::swap(tn, sn);
            std::swap(t, s);
        }
        for (euf::enode* t1 : euf::enode_class(tn)) 
            if (c = compare_rec(n, binding, s, t1->get_expr()), c != l_undef)
                return c;
        return l_undef;
    }

    // f(p1) = f(p2)  if p1 = p2
    // f(p1) != f(p2) if p1 != p2 and f is injective
    lbool ematch::compare_rec(unsigned n, euf::enode* const* binding, expr* s, expr* t) {
        if (m.are_equal(s, t))
            return l_true;
        if (m.are_distinct(s, t))
            return l_false;
        if (!is_app(s) || !is_app(t))
            return l_undef;
        if (to_app(s)->get_decl() != to_app(t)->get_decl())
            return l_undef;
        if (to_app(s)->get_num_args() != to_app(t)->get_num_args())
            return l_undef;
        bool is_injective = to_app(s)->get_decl()->is_injective();
        bool has_undef = false;
        for (unsigned i = to_app(s)->get_num_args(); i-- > 0; ) {
            switch (compare(n, binding, to_app(s)->get_arg(i), to_app(t)->get_arg(i))) {
            case l_true:
                break;
            case l_false:
                if (is_injective)
                    return l_false;
                return l_undef;
            case l_undef:
                if (!is_injective)
                    return l_undef;
                has_undef = true;
                break;
            }
        }
        return has_undef ? l_undef : l_true;
    }

    euf::enode* ematch::eval(unsigned n, euf::enode* const* binding, expr* e) {
        if (is_ground(e))
            return ctx.get_egraph().find(e);
        if (m_mark.is_marked(e))
            return m_eval[e->get_id()];
        ptr_buffer<expr> todo;
        ptr_buffer<euf::enode> args;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            SASSERT(!is_ground(t) || ctx.get_egraph().find(t));
            if (is_ground(t)) {
                m_eval.setx(t->get_id(), ctx.get_egraph().find(t), nullptr);
                SASSERT(m_eval[t->get_id()]);
                todo.pop_back();
                continue;
            }
            if (m_mark.is_marked(t)) {
                todo.pop_back();
                continue;
            }
            if (is_var(t)) {
                m_mark.mark(t);
                m_eval.setx(t->get_id(), binding[n - 1 - to_var(t)->get_idx()], nullptr);
                todo.pop_back();
                continue;
            }
            if (!is_app(t))
                return nullptr;
            args.reset();
            for (expr* arg : *to_app(t)) {
                if (m_mark.is_marked(arg))
                    args.push_back(m_eval[arg->get_id()]);
                else
                    todo.push_back(arg);
            }
            if (args.size() == to_app(t)->get_num_args()) {
                euf::enode* n = ctx.get_egraph().find(t, args.size(), args.c_ptr());
                if (!n)
                    return nullptr;
                m_indirect_nodes.push_back(n);
                m_eval.setx(t->get_id(), n, nullptr);
                m_mark.mark(t);
                todo.pop_back();
            }
        }
        return m_eval[e->get_id()];
    }

    void ematch::insert_to_propagate(unsigned node_id) {
        m_node_in_queue.assure_domain(node_id);
        if (m_node_in_queue.contains(node_id))
            return;
        m_node_in_queue.insert(node_id);
        for (unsigned idx : m_watch[node_id]) {
            m_clause_in_queue.assure_domain(idx);
            if (!m_clause_in_queue.contains(idx)) {
                m_clause_in_queue.insert(idx);
                m_queue.push_back(idx);
            }
        }
    }

    bool ematch::propagate() {
        m_mam->propagate();
        if (m_qhead >= m_queue.size())
            return false;
        bool propagated = false;
        ctx.push(value_trail<euf::solver, unsigned>(m_qhead));
        ptr_buffer<binding> to_remove;
        for (; m_qhead < m_queue.size(); ++m_qhead) {
            unsigned idx = m_queue[m_qhead];
            clause& c = *m_clauses[idx];
            binding* b = c.m_bindings;
            if (!b)
                continue;
            do {
                if (propagate(b->m_nodes, c)) 
                    to_remove.push_back(b);                
                b = b->next();
            }
            while (b != c.m_bindings);

            for (binding* b : to_remove) {
                binding::remove_from(c.m_bindings, b);
                ctx.push(insert_binding(c, b));                
            }
            to_remove.reset();
        }
        m_clause_in_queue.reset();
        m_node_in_queue.reset();
        return propagated;
    }

    /**
     * basic clausifier, assumes q has been normalized.
     */
    ematch::clause* ematch::clausify(quantifier* _q) {
        clause* cl = alloc(clause, m);
        cl->m_literal = ctx.mk_literal(_q);
        quantifier_ref q(_q, m);
        if (is_exists(q)) {
            cl->m_literal.neg();
            expr_ref body(mk_not(m, q->get_expr()), m);
            q = m.update_quantifier(q, forall_k, body);
        }        
        expr_ref_vector ors(m);        
        flatten_or(q->get_expr(), ors);
        for (expr* arg : ors) {
            bool sign = m.is_not(arg, arg);
            expr* l, *r;
            if (!m.is_eq(arg, l, r) || is_ground(arg)) {
                l = arg;
                r = sign ? m.mk_false() : m.mk_true();
                sign = false;
            }
            cl->m_lits.push_back(lit(expr_ref(l, m), expr_ref(r, m), sign));
        }
        if (q->get_num_patterns() == 0) {
            expr_ref tmp(m);
            m_infer_patterns(q, tmp); 
            q = to_quantifier(tmp);
        }
        cl->m_q = q;
        SASSERT(ctx.s().value(cl->m_literal) == l_true);
        return cl;
    }

    /**
     * Attach ground subterms of patterns so they appear shared.
     */
    void ematch::attach_ground_pattern_terms(expr* pat) {
        mam::ground_subterms(pat, m_ground);
        for (expr* g : m_ground) { 
            euf::enode* n = ctx.get_egraph().find(g);
            if (!n->is_attached_to(m_qs.get_id())) {
                euf::theory_var v = m_qs.mk_var(n);
                ctx.get_egraph().add_th_var(n, v, m_qs.get_id());
            }
        }
    }

    struct ematch::pop_clause : public trail<euf::solver> {
        ematch& em;
        pop_clause(ematch& em): em(em) {}
        void undo(euf::solver& ctx) override {
            em.m_q2clauses.remove(em.m_clauses.back()->m_q);
            dealloc(em.m_clauses.back());
            em.m_clauses.pop_back();
        }
    };

    void ematch::add(quantifier* q) {
        TRACE("q", tout << "add " << mk_pp(q, m) << "\n";);
        clause* c = clausify(q);
        ensure_ground_enodes(*c);
        unsigned idx = m_clauses.size();
        m_clauses.push_back(c);
        m_q2clauses.insert(q, idx);
        ctx.push(pop_clause(*this));
        init_watch(*c, idx);
        
        bool has_unary_pattern = false;
        unsigned num_patterns = q->get_num_patterns();
        for (unsigned i = 0; i < num_patterns && !has_unary_pattern; i++) 
            has_unary_pattern = (1 == to_app(q->get_pattern(i))->get_num_args());
        unsigned num_eager_multi_patterns = ctx.get_config().m_qi_max_eager_multipatterns;
        if (!has_unary_pattern)
            num_eager_multi_patterns++;
        for (unsigned i = 0, j = 0; i < num_patterns; i++) {
            app * mp = to_app(q->get_pattern(i));
            SASSERT(m.is_pattern(mp));
            bool unary = (mp->get_num_args() == 1);
            TRACE("q", tout << "adding:\n" << expr_ref(mp, m) << "\n";);
            if (!unary && j >= num_eager_multi_patterns) {
                TRACE("q", tout << "delaying (too many multipatterns):\n" << mk_ismt2_pp(mp, m) << "\n";);
                if (!m_lazy_mam)
                    m_lazy_mam = mam::mk(ctx, *this);
                m_lazy_mam->add_pattern(q, mp);
            }
            else 
                m_mam->add_pattern(q, mp);

            attach_ground_pattern_terms(mp);

            if (!unary)
                j++;
        }
    }

    bool ematch::operator()() {
        TRACE("q", m_mam->display(tout););
        if (propagate())
            return true;
        if (m_lazy_mam) {
            m_lazy_mam->propagate();
            if (propagate())
                return true;
        }

        // 
        // loop over pending bindings and instantiate them
        // 
        bool instantiated = false;
        for (auto* c : m_clauses) {
            binding* b = c->m_bindings;
            if (!b) 
                continue;
            instantiated = true;
            do {
                instantiate(b->m_nodes, *c);
                b = b->next();
            }
            while (b != c->m_bindings);
            
            while (b = c->m_bindings) {
                binding::remove_from(c->m_bindings, b);
                ctx.push(insert_binding(*c, b));
            }
        }
        TRACE("q", ctx.display(tout << "instantiated: " << instantiated << "\n"););
        return instantiated;
    }

    std::ostream& ematch::display(std::ostream& out) const {
        for (auto const& c : m_clauses) 
            c->display(ctx, out);
        return out;
    }

}
