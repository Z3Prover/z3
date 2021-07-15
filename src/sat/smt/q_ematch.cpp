/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_ematch.cpp

Abstract:

    E-matching quantifier instantiation plugin
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

Todo:

- nested quantifiers
- non-cnf quantifiers (handled in q_solver)

Done:

- clausify
- propagate without instantiations, produce explanations for eval
- generations
- insert instantiations into priority queue 
- cache instantiations and substitutions

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
        m_eval(ctx),
        m_qstat_gen(m, ctx.get_region()),
        m_inst_queue(*this, ctx),
        m_infer_patterns(m, ctx.get_config())       
    {
        std::function<void(euf::enode*, euf::enode*)> _on_merge = 
            [&](euf::enode* root, euf::enode* other) { 
            on_merge(root, other); 
        };
        std::function<void(euf::enode*)> _on_make = 
            [&](euf::enode* n) {
            m_mam->add_node(n, false);
        };
        ctx.get_egraph().set_on_merge(_on_merge);
        ctx.get_egraph().set_on_make(_on_make);
        m_mam = mam::mk(ctx, *this);
    }

    void ematch::ensure_ground_enodes(expr* e) {
        mam::ground_subterms(e, m_ground);
        for (expr* g : m_ground) 
            m_qs.e_internalize(g);
    }

    void ematch::ensure_ground_enodes(clause const& c) {
        quantifier* q = c.q();
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
        lit lit(expr_ref(l, m), expr_ref(r, m), sign); 
        if (idx != UINT_MAX)
            lit = c[idx];
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) justification(lit, c, b);
        return constraint->to_index();
    }

    void ematch::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) {
        m_eval.explain(l, justification::from_index(idx), r, probing);
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

    struct restore_watch : public trail {
        vector<unsigned_vector>& v;
        unsigned idx, offset;
        restore_watch(vector<unsigned_vector>& v, unsigned idx):
            v(v), idx(idx), offset(v[idx].size()) {}
        void undo() override {
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
    }

    // watch only nodes introduced in bindings or ground arguments of functions
    // or functions that have been inserted.

    void ematch::add_watch(euf::enode* n, unsigned clause_idx) {
        unsigned root_id = n->get_root_id();
        m_watch.reserve(root_id + 1);
        ctx.push(restore_watch(m_watch, root_id));
        m_watch[root_id].push_back(clause_idx);
    }

    void ematch::init_watch(expr* e, unsigned clause_idx) {
        ptr_buffer<expr> todo;
        scoped_mark_reset _sr(*this);
        todo.push_back(e);
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            if (m_mark.is_marked(t))
                continue;
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

    void ematch::init_watch(clause& c) {
        unsigned idx = c.index();
        for (auto lit : c.m_lits) {
            if (!is_ground(lit.lhs))
                init_watch(lit.lhs, idx);
            if (!is_ground(lit.rhs))
                init_watch(lit.rhs, idx);
        }
    }

    struct ematch::remove_binding : public trail {
        euf::solver& ctx;
        clause& c;
        binding* b;
        remove_binding(euf::solver& ctx, clause& c, binding* b): ctx(ctx), c(c), b(b) {}
        void undo() override {            
            SASSERT(binding::contains(c.m_bindings, b));
            binding::remove_from(c.m_bindings, b);
            binding::detach(b);
        }        
    };

    struct ematch::insert_binding : public trail {
        euf::solver& ctx;
        clause& c;
        binding* b;
        insert_binding(euf::solver& ctx, clause& c, binding* b): ctx(ctx), c(c), b(b) {}
        void undo() override {            
            SASSERT(!c.m_bindings || c.m_bindings->invariant());
            binding::push_to_front(c.m_bindings, b);
            SASSERT(!c.m_bindings || c.m_bindings->invariant());
        }
    };

    binding* ematch::alloc_binding(unsigned n, app* pat, unsigned max_generation, unsigned min_top, unsigned max_top) {
        unsigned sz = sizeof(binding) + sizeof(euf::enode* const*)*n;
        void* mem = ctx.get_region().allocate(sz);
        return new (mem) binding(pat, max_generation, min_top, max_top);
    }  

    euf::enode* const* ematch::alloc_binding(clause& c, euf::enode* const* _binding) {
        unsigned sz = sizeof(euf::enode* const*) * c.num_decls();
        euf::enode** binding = (euf::enode**)ctx.get_region().allocate(sz);
        for (unsigned i = 0; i < c.num_decls(); ++i)
            binding[i] = _binding[i];
        return binding;
    }

    void ematch::add_binding(clause& c, app* pat, euf::enode* const* _binding, unsigned max_generation, unsigned min_top, unsigned max_top) {
        unsigned n = c.num_decls();
        binding* b = alloc_binding(n, pat, max_generation, min_top, max_top);
        b->init(b);
        for (unsigned i = 0; i < n; ++i)
            b->m_nodes[i] = _binding[i];        
        binding::push_to_front(c.m_bindings, b);
        ctx.push(remove_binding(ctx, c, b));
    }

    void ematch::on_binding(quantifier* q, app* pat, euf::enode* const* _binding, unsigned max_generation, unsigned min_gen, unsigned max_gen) {
        TRACE("q", tout << "on-binding " << mk_pp(q, m) << "\n";);
        unsigned idx = m_q2clauses[q];
        clause& c = *m_clauses[idx];
        bool new_propagation = false;
        if (!propagate(false, _binding, max_generation, c, new_propagation)) 
            add_binding(c, pat, _binding, max_generation, min_gen, max_gen);
    }

    bool ematch::propagate(bool is_owned, euf::enode* const* binding, unsigned max_generation, clause& c, bool& propagated) {
        TRACE("q", c.display(ctx, tout) << "\n";);
        unsigned idx = UINT_MAX;
        lbool ev = m_eval(binding, c, idx);
        if (ev == l_true) {
            ++m_stats.m_num_redundant;
            return true;
        }
        if (ev == l_undef && idx == UINT_MAX) {
            unsigned clause_idx = c.index();
            for (euf::enode* n : m_eval.get_watch())
                add_watch(n, clause_idx);
            for (unsigned j = c.num_decls(); j-- > 0; )
                add_watch(binding[j], clause_idx);
            return false;
        }
        if (ev == l_undef && max_generation > m_generation_propagation_threshold)
            return false;
        if (!is_owned) 
            binding = alloc_binding(c, binding);        
        auto j_idx = mk_justification(idx, c, binding);       
        if (ev == l_false) {
            ++m_stats.m_num_conflicts;
            ctx.set_conflict(j_idx);
        }
        else {
            ++m_stats.m_num_propagations;
            ctx.propagate(instantiate(c, binding, c[idx]), j_idx);
        }
        propagated = true;
        return true;
    }

    void ematch::instantiate(binding& b, clause& c) {
        if (m_stats.m_num_instantiations > ctx.get_config().m_qi_max_instances) 
            return;
        unsigned max_generation = b.m_max_generation;
        max_generation = std::max(max_generation, c.m_stat->get_generation());
        c.m_stat->update_max_generation(max_generation);
        fingerprint * f = add_fingerprint(c, b, max_generation);
        if (!f)
            return;
        m_inst_queue.insert(f);
        m_stats.m_num_instantiations++;        
    }

    void ematch::add_instantiation(clause& c, binding& b, sat::literal lit) {
        ctx.propagate(lit, mk_justification(UINT_MAX, c, b.nodes()));
    }

    void ematch::set_tmp_binding(fingerprint& fp) {               
        binding& b = *fp.b;
        clause& c = *fp.c;
        if (c.num_decls() > m_tmp_binding_capacity) {
            void* mem = memory::allocate(sizeof(binding) + c.num_decls()*sizeof(euf::enode*));
            m_tmp_binding = new (mem) binding(b.m_pattern, 0, 0, 0);
            m_tmp_binding_capacity = c.num_decls();            
        }

        fp.b = m_tmp_binding.get();
        for (unsigned i = c.num_decls(); i-- > 0; )
            fp.b->m_nodes[i] = b[i];
    }

    fingerprint* ematch::add_fingerprint(clause& c, binding& b, unsigned max_generation) {
        fingerprint fp(c, b, max_generation);        
        if (m_fingerprints.contains(&fp))
            return nullptr;
        set_tmp_binding(fp);
        for (unsigned i = c.num_decls(); i-- > 0; )
            fp.b->m_nodes[i] = fp.b->m_nodes[i]->get_root();
        if (m_fingerprints.contains(&fp))
            return nullptr;
        fingerprint* f = new (ctx.get_region()) fingerprint(c, b, max_generation);
        m_fingerprints.insert(f);
        ctx.push(insert_map<fingerprints, fingerprint*>(m_fingerprints, f));
        return f;
    }

    sat::literal ematch::instantiate(clause& c, euf::enode* const* binding, lit const& l) {
        expr_ref_vector _binding(m);
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

    struct ematch::reset_in_queue : public trail {
        ematch& e;
        reset_in_queue(ematch& e) :e(e) {}

        void undo() override {
            e.m_node_in_queue.reset();
            e.m_clause_in_queue.reset();
            e.m_in_queue_set = false;
        }

        static void insert(ematch& e) {
            if (!e.m_in_queue_set) {
                e.m_in_queue_set = true;
                e.ctx.push(reset_in_queue(e));
            }
        }
    };

    void ematch::insert_to_propagate(unsigned node_id) {
        reset_in_queue::insert(*this);
        m_node_in_queue.assure_domain(node_id);
        if (m_node_in_queue.contains(node_id))
            return;
        m_node_in_queue.insert(node_id);
        for (unsigned idx : m_watch[node_id]) 
            insert_clause_in_queue(idx);       
    }

    void ematch::insert_clause_in_queue(unsigned idx) {
        reset_in_queue::insert(*this);
        m_clause_in_queue.assure_domain(idx);
        if (!m_clause_in_queue.contains(idx)) {
            m_clause_in_queue.insert(idx);
            m_clause_queue.push_back(idx);
            ctx.push(push_back_vector<unsigned_vector>(m_clause_queue));
        }
    }

    /**
     * basic clausifier, assumes q has been normalized.
     */
    clause* ematch::clausify(quantifier* _q) {
        clause* cl = alloc(clause, m, m_clauses.size());
        cl->m_literal = ctx.mk_literal(_q);
        quantifier_ref q(_q, m);
        q = m_qs.flatten(q);
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
            if (m.is_distinct(arg) && to_app(arg)->get_num_args() == 2) {
                l = to_app(arg)->get_arg(0);
                r = to_app(arg)->get_arg(1);
                sign = !sign;
            }
            else if (!m.is_eq(arg, l, r) || is_ground(arg)) {
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
        SASSERT(is_forall(q));
        euf::enode* nq = ctx.get_egraph().find(_q);
        unsigned generation = nq ? nq->generation() : ctx.generation();
        cl->m_stat = m_qstat_gen(_q, generation);
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
            if (!n->is_attached_to(m_qs.get_id())) 
                m_qs.mk_var(n);            
        }
    }

    struct ematch::pop_clause : public trail {
        ematch& em;
        pop_clause(ematch& em): em(em) {}
        void undo() override {
            em.m_q2clauses.remove(em.m_clauses.back()->q());
            dealloc(em.m_clauses.back());
            em.m_clauses.pop_back();
        }
    };

    void ematch::add(quantifier* _q) {
        TRACE("q", tout << "add " << mk_pp(_q, m) << "\n";);
        clause* c = clausify(_q);
        quantifier* q = c->q();
        ensure_ground_enodes(*c);
        m_clauses.push_back(c);
        m_q2clauses.insert(q, c->index());
        ctx.push(pop_clause(*this));
        init_watch(*c);
        
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


    bool ematch::propagate(bool flush) {
        m_mam->propagate();
        bool propagated = false;
        if (m_qhead >= m_clause_queue.size())
            return m_inst_queue.propagate();
        ctx.push(value_trail<unsigned>(m_qhead));
        ptr_buffer<binding> to_remove;
        for (; m_qhead < m_clause_queue.size(); ++m_qhead) {
            unsigned idx = m_clause_queue[m_qhead];
            clause& c = *m_clauses[idx];
            binding* b = c.m_bindings;
            if (!b)
                continue;

            do {
                if (propagate(true, b->m_nodes, b->m_max_generation, c, propagated)) 
                    to_remove.push_back(b);
                else if (flush) {
                    instantiate(*b, c);
                    to_remove.push_back(b);
                }
                b = b->next();
            } 
            while (b != c.m_bindings);

            for (auto* b : to_remove) {
                SASSERT(binding::contains(c.m_bindings, b));
                binding::remove_from(c.m_bindings, b);
                binding::detach(b);
                ctx.push(insert_binding(ctx, c, b));
            }
            to_remove.reset();
        }
        m_clause_in_queue.reset();
        m_node_in_queue.reset();
        m_in_queue_set = true;
        if (m_inst_queue.propagate())
            propagated = true;
        return propagated;
    }

    bool ematch::operator()() {
        TRACE("q", m_mam->display(tout););
        if (propagate(false))
            return true;
        if (m_lazy_mam) {
            m_lazy_mam->propagate();
            if (propagate(false))
                return true;
        }
        unsigned idx = 0;
        for (clause* c : m_clauses) {
            if (c->m_bindings) 
                insert_clause_in_queue(idx);
            idx++;
        }
        if (propagate(true))
            return true;
        return m_inst_queue.lazy_propagate();
    }

    void ematch::collect_statistics(statistics& st) const {
        m_inst_queue.collect_statistics(st);
        st.update("q redundant", m_stats.m_num_redundant);
        st.update("q units",     m_stats.m_num_propagations);
        st.update("q conflicts", m_stats.m_num_conflicts);
    }

    std::ostream& ematch::display(std::ostream& out) const {
        for (auto const& c : m_clauses) 
            c->display(ctx, out);
        return out;
    }

}
