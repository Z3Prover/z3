/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_finite_set.cpp

Abstract:

    Theory solver for finite sets.
    Implements axiom schemas for finite set operations.

--*/

#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_arith_value.h"
#include "ast/ast_pp.h"

namespace smt {

    /**
    * Constructor.
    * Set up callback that adds axiom instantiations as clauses. 
    **/
    theory_finite_set::theory_finite_set(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("finite_set")),
        u(m),
        m_axioms(m), m_rw(m), m_find(*this),
        m_cardinality_solver(*this)
    {
        // Setup the add_clause callback for axioms
        std::function<void(theory_axiom *)> add_clause_fn =
            [this](theory_axiom* ax) {
                this->add_clause(ax);
            };
        m_axioms.set_add_clause(add_clause_fn);
    }

    theory_finite_set::~theory_finite_set() {
        reset_set_members();
    }

    void theory_finite_set::reset_set_members() {
        for (auto [k, s] : m_set_members)
            dealloc(s);
        m_set_members.reset();
    }

    /**
    * When creating a theory variable, we associate extra data structures with it.
    * if n := (set.in x S)
    * then for every T in the equivalence class of S (including S), assert theory axioms for x in T.
    * 
    * if n := (setop T U)
    * then for every (set.in x S) where either S ~ T, S ~ U, assert theory axioms for x in n.
    * Since n is fresh there are no other (set.in x S) with S ~ n in the state.
    * 
    * if n := (set.filter p S)
    * then for every (set.in x T) where S ~ T, assert theory axiom for x in (set.filter p S)
    * 
    * if n := (set.map f S)
    * then for every (set.in x T) where S ~ T, assert theory axiom for (set.in x S) and map.
    * In other words, assert 
    *         (set.in (f x) (set.map f S))
    */
    theory_var theory_finite_set::mk_var(enode *n) {
        TRACE(finite_set, tout << "mk_var: " << enode_pp(n, ctx) << "\n");
        theory_var r = theory::mk_var(n);
        VERIFY(r == static_cast<theory_var>(m_find.mk_var()));
        SASSERT(r == static_cast<int>(m_var_data.size()));
        m_var_data.push_back(alloc(var_data, m));
        ctx.push_trail(push_back_vector<ptr_vector<var_data>>(m_var_data));
        ctx.push_trail(new_obj_trail(m_var_data.back()));
        expr *e = n->get_expr();
        if (u.is_in(e)) {
            auto set = n->get_arg(1);
            auto v = set->get_root()->get_th_var(get_id());
            SASSERT(v != null_theory_var);
            m_var_data[v]->m_parent_in.push_back(n);
            ctx.push_trail(push_back_trail(m_var_data[v]->m_parent_in));
            add_in_axioms(n, m_var_data[v]);  // add axioms x in S x S ~ T, T := setop, or T is arg of setop.
            auto f = to_app(e)->get_decl();
            if (!m_set_in_decls.contains(f)) {
                m_set_in_decls.push_back(f);
                ctx.push_trail(push_back_vector(m_set_in_decls));
            }
        }
        else if (u.is_union(e) || u.is_intersect(e) || 
            u.is_difference(e) || u.is_singleton(e) ||
            u.is_empty(e) || u.is_range(e) || u.is_filter(e) || u.is_map(e)) {            
            m_var_data[r]->m_setops.push_back(n);
            ctx.push_trail(push_back_trail(m_var_data[r]->m_setops));
            for (auto arg : enode::args(n)) {
                expr *e = arg->get_expr();
                if (!u.is_finite_set(e))
                    continue;
                auto v = arg->get_root()->get_th_var(get_id());
                SASSERT(v != null_theory_var);
                // add axioms for x in S, e := setop S T ...
                for (auto in : m_var_data[v]->m_parent_in)
                    add_membership_axioms(in->get_arg(0)->get_expr(), e);
                m_var_data[v]->m_parent_setops.push_back(n);
                ctx.push_trail(push_back_trail(m_var_data[v]->m_parent_setops));
            }
        }
        else if (u.is_range(e)) {
            
        }
        else if (u.is_size(e)) {
            auto f = to_app(e)->get_decl();
            m_cardinality_solver.add_set_size(f);
        }
        return r;
    }

    trail_stack& theory_finite_set::get_trail_stack() {
        return ctx.get_trail_stack();
    }

    /*
     * Merge the equivalence classes of two variables.
     * parent_in := vector of (set.in x S) terms where S is in the equivalence class of r.
     * parent_setops := vector of (set.op S T) where S or T is in the equivalence class of r.
     * setops := vector of (set.op S T) where (set.op S T) is in the equivalence class of r.
     * 
     */
    void theory_finite_set::merge_eh(theory_var root, theory_var other, theory_var, theory_var) {
        // r is the new root
        TRACE(finite_set, tout << "merging v" << root << " v" << other << "\n"; display_var(tout, root);
              tout << " <- " << mk_pp(get_enode(other)->get_expr(), m) << "\n";);
        SASSERT(root == find(root));
        var_data *d_root= m_var_data[root];
        var_data *d_other = m_var_data[other];
        ctx.push_trail(restore_vector(d_root->m_setops));
        ctx.push_trail(restore_vector(d_root->m_parent_setops));
        ctx.push_trail(restore_vector(d_root->m_parent_in));
        add_in_axioms(root, other);
        add_in_axioms(other, root);
        d_root->m_setops.append(d_other->m_setops);
        d_root->m_parent_setops.append(d_other->m_parent_setops);
        d_root->m_parent_in.append(d_other->m_parent_in);
        TRACE(finite_set, tout << "after merge\n"; display_var(tout, root););
    }

    /*
     * for each (set.in x S) in d1->parent_in,
     *     add axioms for (set.in x S)
     */
    void theory_finite_set::add_in_axioms(theory_var v1, theory_var v2) {
        auto d1 = m_var_data[v1];
        auto d2 = m_var_data[v2];
        for (enode *in : d1->m_parent_in) 
            add_in_axioms(in, d2);        
    }

    /*
     *  let (set.in x S) 
     *
     *  for each T := (set.op U V) in d2->parent_setops
     *         then S ~ U or S ~ V by construction
     *              add axioms for (set.in x T)
     *        
     *  for each T := (set.op U V) in d2->setops
     *         then S ~ T by construction
     *              add axioms for (set.in x T)
     * 
    */

    void theory_finite_set::add_in_axioms(enode *in, var_data *d) {
        SASSERT(u.is_in(in->get_expr()));
        auto e = in->get_arg(0)->get_expr();
        auto set1 = in->get_arg(1);
        for (enode *setop : d->m_parent_setops) {
            SASSERT(
                any_of(enode::args(setop), [&](enode *arg) { return in->get_arg(1)->get_root() == arg->get_root(); }));
            add_membership_axioms(e, setop->get_expr());
        }

        for (enode *setop : d->m_setops) {
            SASSERT(in->get_arg(1)->get_root() == setop->get_root());
            add_membership_axioms(e, setop->get_expr());
        }
    }

    /**
    * Boolean atomic formulas for finite sets are one of:
    * (set.in x S)
    * (set.subset S T)
    * When an atomic formula is first created it is to be registered with the solver.
    * The internalize_atom method takes care of this.
    * Atomic formulas are special cases of terms (of non-Boolean type) so they are registered as terms.
    *    
    */
    bool theory_finite_set::internalize_atom(app * atom, bool gate_ctx) {
        return internalize_term(atom);
    }

    /**
     * When terms are registered with the solver , we need to ensure that:
     * - All subterms have an associated E-node
     * - Boolean terms are registered as boolean variables
     *   Registering a Boolean variable ensures that the solver will be notified about its truth value.
     * - Non-Boolean terms have an associated theory variable
     *   Registering a theory variable ensures that the solver will be notified about equalities and disequalites.
     *   The solver can use the theory variable to track auxiliary information about E-nodes.    
    */
    bool theory_finite_set::internalize_term(app * term) {
        TRACE(finite_set, tout << "internalize_term: " << mk_pp(term, m) << "\n";);
        
        // Internalize all arguments first
        for (expr* arg : *term) 
            ctx.internalize(arg, false);
        
        // Create boolean variable for Boolean terms
        if (m.is_bool(term) && !ctx.b_internalized(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
        }
        
        // Create enode for the term if needed
        enode* e = nullptr;
        if (ctx.e_internalized(term)) 
            e = ctx.get_enode(term);         
        else 
            e = ctx.mk_enode(term, false, m.is_bool(term), true);        
        
        // Attach theory variable if this is a set
        if (!is_attached_to_var(e)){            
            ctx.attach_th_var(e, this, mk_var(e));
            TRACE(finite_set, tout << "create_theory_var: " << e->get_th_var(get_id()) << " enode:" << e->get_expr() << "\n";);
        }


        // Assert immediate axioms
        if (!ctx.relevancy())
            add_immediate_axioms(term);
                
        return true;
    }

    void theory_finite_set::relevant_eh(app* t) {
        add_immediate_axioms(t);
    }

    void theory_finite_set::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(u.is_finite_set(s));
        if (!is_attached_to_var(n))
            ctx.attach_th_var(n, this, mk_var(n));
    }

    void theory_finite_set::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE(finite_set, tout << "new_eq_eh: v" << v1 << " = v" << v2 << "\n";);
        auto n1 = get_enode(v1);
        auto n2 = get_enode(v2);
        if (u.is_finite_set(n1->get_expr()) && u.is_finite_set(n2->get_expr())) {
            m_eqs.push_back({v1, v2});
            ctx.push_trail(push_back_vector(m_eqs));
            m_find.merge(v1, v2);  // triggers merge_eh, which triggers incremental generation of theory axioms
        }

        // Check if Z3 has a boolean variable for it
        TRACE(finite_set, tout << "new_eq_eh_r1: " << n1->get_root() << "r2: "<< n2->get_root() <<"\n";);
    }

    /**
    * Every dissequality has to be supported by at distinguishing element.
    * 
    */
    void theory_finite_set::new_diseq_eh(theory_var v1, theory_var v2) {
        TRACE(finite_set, tout << "new_diseq_eh: v" << v1 << " != v" << v2 << "\n");
        auto n1 = get_enode(v1);
        auto n2 = get_enode(v2);
        auto e1 = n1->get_expr();
        auto e2 = n2->get_expr();
        if (u.is_finite_set(e1) && u.is_finite_set(e2)) {
            if (e1->get_id() > e2->get_id())
                std::swap(e1, e2);
            if (!is_new_axiom(e1, e2))
                return;
            if (are_forced_distinct(n1, n2))
                return;
            m_diseqs.push_back({v1, v2});
            ctx.push_trail(push_back_vector(m_diseqs));
            m_axioms.extensionality_axiom(e1, e2);
        }
    }

    //
    // TODO: add implementation that detects sets that are known to be distinct.
    // for example, 
    // . x in a is assigned to true and y in b is assigned to false and x ~ y
    // . or upper-bound(set.size(a)) < lower-bound(set.size(b))
    //   where upper and lower bounds can be queried using arith_value
    // 
    bool theory_finite_set::are_forced_distinct(enode* a, enode* b) {
        return false;
    }

    /**
    * Final check for the finite set theory.
     * The Final Check method is called when the solver has assigned truth values to all Boolean variables.
     * It is responsible for asserting any remaining axioms and checking for inconsistencies.
     * 
     * It ensures saturation with respect to the theory axioms:
     * - membership axioms
     * - assume eqs axioms
    */
    final_check_status theory_finite_set::final_check_eh(unsigned) {
        TRACE(finite_set, tout << "final_check_eh\n";);

        if (activate_unasserted_clause())
            return FC_CONTINUE;

        if (activate_range_local_axioms())
            return FC_CONTINUE;

        if (assume_eqs())
            return FC_CONTINUE;

        switch (m_cardinality_solver.final_check()) {
        case l_true: break;
        case l_false: return FC_CONTINUE;
        case l_undef: return FC_GIVEUP;
        }
        
        return is_fully_solved() ? FC_DONE : FC_GIVEUP;
    }

    /**
    * Determine if the constraints are fully solved.
    * They can be fully solved if:
    * - the model that is going to be produced satisfies all constraints
    * The model will always satisfy the constraints if:
    * - there is no occurrence of set.map
    * - there is not both set.size and set.filter
    */
    bool theory_finite_set::is_fully_solved() {
        bool has_map = false, has_filter = false, has_size = false, has_range = false;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            auto n = get_enode(v);
            auto e = n->get_expr();
            if (u.is_filter(e))
                has_filter = true;
            if (u.is_map(e))
                has_map = true;
            if (u.is_size(e))
                has_size = true;
            if (u.is_range(e))
                has_range = true;
        }
        TRACE(finite_set, tout << "has-map " << has_map << " has-filter-size " << has_filter << has_size << "\n");
        if (has_map)
            return false; // todo use more expensive model check here
        if (has_filter && has_size)
            return false; // todo use more expensive model check here
        if (has_range && has_size)
            return false; // todo use more expensive model check here or even ensure range expressions are handled natively by size.
        return true;
    }


    /**
     * Add immediate axioms that can be asserted when the atom is created.
     * These are unit clauses that can be added immediately.
     * - (set.in x set.empty) is false
     * - (set.subset S T) <=> (= (set.union S T) T)  (or (= (set.intersect S T) S))
     * - (set.singleton x) -> (set.in x (set.singleton x))
     * - (set.range lo hi) -> lo-1,hi+1 not in range, lo, hi in range if lo <= hi     * 
     *
     * Other axioms:
     * - (set.size s)       -> 0 <= (set.size s) <= upper-bound(s)
     */
    void theory_finite_set::add_immediate_axioms(app* term) {
        expr *elem = nullptr, *set = nullptr;
        expr *lo = nullptr, *hi = nullptr;
        unsigned sz = m_clauses.axioms.size();
        if (u.is_in(term, elem, set) && u.is_empty(set))
            add_membership_axioms(elem, set);
        else if (u.is_subset(term))
            m_axioms.subset_axiom(term);
        else if (u.is_singleton(term))
            m_axioms.in_singleton_axiom(term);
        else if (u.is_range(term, lo, hi)) {
            m_axioms.in_range_axiom(term);
            auto range = ctx.get_enode(term);
            auto v = range->get_th_var(get_id());
            // declare lo-1, lo, hi, hi+1 as range local.
            // we don't have to add additional range local variables for them.
            auto &range_local = m_var_data[v]->m_range_local;
            ctx.push_trail(push_back_vector(range_local));
            arith_util a(m);
            range_local.push_back(lo);
            range_local.push_back(hi);
            range_local.push_back(a.mk_add(lo, a.mk_int(-1)));
            range_local.push_back(a.mk_add(hi, a.mk_int(1)));
        }
        else if (u.is_size(term)) {
            m_axioms.size_lb_axiom(term);
            m_axioms.size_ub_axiom(term);
        }
       
        // Assert all new lemmas as clauses
        for (unsigned i = sz; i < m_clauses.axioms.size(); ++i) {
            m_clauses.squeue.push_back(i);
            ctx.push_trail(push_back_vector(m_clauses.squeue));
        }
    }

    void theory_finite_set::assign_eh(bool_var v, bool is_true) {
        TRACE(finite_set, tout << "assign_eh: v" << v << " is_true: " << is_true << "\n";);
        expr *e = ctx.bool_var2expr(v);
        TRACE(finite_set, tout << "assign_eh_expr: " << mk_pp(e, m) << "\n";);

        // retrieve the watch list for clauses where e appears with opposite polarity
        unsigned idx = 2 * e->get_id() + (is_true ? 1 : 0);
        if (idx >= m_clauses.watch.size())
            return;

        // walk the watch list and try to find new watches or propagate
        unsigned j = 0;
        for (unsigned i = 0; i < m_clauses.watch[idx].size(); ++i) {
            TRACE(finite_set, tout << "watch[" << i << "] size: " << m_clauses.watch[i].size() << "\n";);
            auto clause_idx = m_clauses.watch[idx][i];
            auto* ax = m_clauses.axioms[clause_idx];
            auto &clause = ax->clause;
            if (any_of(clause, [&](expr *lit) { return ctx.find_assignment(lit) == l_true; })) {
                TRACE(finite_set, tout << "satisfied\n";);
                m_clauses.watch[idx][j++] = clause_idx;
                continue; // clause is already satisfied
            }
            auto is_complement_to = [&](bool is_true, expr* lit, expr* arg) {
                if (is_true)
                    return m.is_not(lit) && to_app(lit)->get_arg(0) == arg;
                else
                    return lit == arg;
            };
            auto lit1 = clause.get(0);
            auto lit2 = clause.get(1);
            auto position = 0;
            if (is_complement_to(is_true, lit1, e))
                position = 0;
            else {
                SASSERT(is_complement_to(is_true, lit2, e));
                position = 1;
            }
            
            bool found_swap = false;
            for (unsigned k = 2; k < clause.size(); ++k) {
                expr *lit = clause.get(k);
                if (ctx.find_assignment(lit) == l_false)
                    continue;
                // found a new watch     
                clause.swap(position, k);          
                // std::swap(clause[position], clause[k]);
                bool litneg = m.is_not(lit, lit);
                auto litid = 2 * lit->get_id() + litneg;              
                m_clauses.watch.reserve(litid + 1);
                m_clauses.watch[litid].push_back(clause_idx);
                TRACE(finite_set, tout << "new watch for " << mk_pp(lit, m) << "\n";);
                found_swap = true;
                break;
            }
            if (found_swap) 
                continue;  // the clause is removed from this watch list
            // either all literals are false, or the other watch literal is propagating.
            m_clauses.squeue.push_back(clause_idx);
            ctx.push_trail(push_back_vector(m_clauses.squeue));
            TRACE(finite_set, tout << "propagate clause\n";);
            m_clauses.watch[idx][j++] = clause_idx;
            ++i;
            for (; i < m_clauses.watch[idx].size(); ++i)
                m_clauses.watch[idx][j++] = m_clauses.watch[idx][i];
            break;
        }
        m_clauses.watch[idx].shrink(j);
    }

    bool theory_finite_set::can_propagate() {
        return m_clauses.can_propagate();
    }

    void theory_finite_set::propagate() {
        // TRACE(finite_set, tout << "propagate\n";);
        ctx.push_trail(value_trail(m_clauses.aqhead));
        ctx.push_trail(value_trail(m_clauses.sqhead));
        while (can_propagate() && !ctx.inconsistent()) {
            // activate newly created clauses
            while (m_clauses.aqhead < m_clauses.axioms.size()) 
                activate_clause(m_clauses.aqhead++);

            // empty the propagation queue of clauses to assert
            while (m_clauses.sqhead < m_clauses.squeue.size() && !ctx.inconsistent()) {
                auto clause_idx = m_clauses.squeue[m_clauses.sqhead++];
                auto ax = m_clauses.axioms[clause_idx];
                assert_clause(ax);
            }
        }      
    }

    void theory_finite_set::activate_clause(unsigned clause_idx) {
        TRACE(finite_set, tout << "activate_clause: " << clause_idx << "\n";);
        auto* ax = m_clauses.axioms[clause_idx];
        auto &clause = ax->clause;
        if (any_of(clause, [&](expr *e) { return ctx.find_assignment(e) == l_true; }))
            return;
        if (clause.size() <= 1) {
            m_clauses.squeue.push_back(clause_idx);
            ctx.push_trail(push_back_vector(m_clauses.squeue));
            return;
        }
        expr *w1 = nullptr, *w2 = nullptr;
        for (unsigned i = 0; i < clause.size(); ++i) {
            expr *lit = clause.get(i);
            switch (ctx.find_assignment(lit)) {
            case l_true:
                UNREACHABLE();
                 return; 
            case l_false: 
                break;
            case l_undef:
                if (!w1) {
                    w1 = lit;
                    clause.swap(0, i);
                }                                    
                else if (!w2) {
                    w2 = lit;
                    clause.swap(1, i);
                }
                break;
            }
        }
        if (!w2) {
            m_clauses.squeue.push_back(clause_idx);
            ctx.push_trail(push_back_vector(m_clauses.squeue));
            return;
        }
        bool w1neg = m.is_not(w1, w1);
        bool w2neg = m.is_not(w2, w2);  
        unsigned w1id = 2 * w1->get_id() + w1neg;
        unsigned w2id = 2 * w2->get_id() + w2neg;
        unsigned sz = std::max(w1id, w2id) + 1;
        m_clauses.watch.reserve(sz);
        m_clauses.watch[w1id].push_back(clause_idx);
        m_clauses.watch[w2id].push_back(clause_idx);

        struct unwatch_clause : public trail {
            theory_finite_set &th;
            unsigned index;
            unwatch_clause(theory_finite_set &th, unsigned index) : th(th), index(index) {}
            void undo() override {
                auto* ax = th.m_clauses.axioms[index];
                auto &clause = ax->clause;
                expr *w1 = clause.get(0);
                expr *w2 = clause.get(1);
                bool w1neg = th.m.is_not(w1, w1);
                bool w2neg = th.m.is_not(w2, w2);
                unsigned w1id = 2 * w1->get_id() + w1neg;
                unsigned w2id = 2 * w2->get_id() + w2neg;
                auto &watch1 = th.m_clauses.watch[w1id];
                auto &watch2 = th.m_clauses.watch[w2id];
                watch1.erase(index);
                watch2.erase(index);
            }
        };
        ctx.push_trail(unwatch_clause(*this, clause_idx));
    }



    /**
     *  Saturate with respect to equality sharing:
     *  - Sets corresponding to shared variables having the same interpretation should also be congruent
    */
    bool theory_finite_set::assume_eqs() {
        collect_members();
        expr_ref_vector trail(m); // make sure reference counts to union expressions are valid in this scope
        obj_map<expr, enode*> set_reprs;

        auto start = ctx.get_random_value();
        auto sz = get_num_vars();
        for (unsigned w = 0; w < sz; ++w) {
            auto v = (w + start) % sz;
            enode* n = get_enode(v);
            if (!u.is_finite_set(n->get_expr()))
                continue;
            if (!is_relevant_and_shared(n))
                continue;
            auto r = n->get_root();
            // Create a union expression that is canonical (sorted)
            if (!m_set_members.contains(r))
                continue;
            auto& set = *m_set_members[r];
            ptr_vector<expr> elems;
            for (auto [e,b] : set)
                if (b)  
                    elems.push_back(e->get_expr());
            std::sort(elems.begin(), elems.end(), [](expr *a, expr *b) { return a->get_id() < b->get_id(); });
            expr *s = mk_union(elems.size(), elems.data(), n->get_expr()->get_sort());
            trail.push_back(s);
            enode *n2 = nullptr;
            if (!set_reprs.find(s, n2)) {
                set_reprs.insert(s, r);
                continue;
            }
            if (n2->get_root() == r)
                continue;
            if (is_new_axiom(n->get_expr(), n2->get_expr()) && assume_eq(n, n2)) {
                TRACE(finite_set,
                      tout << "assume " << mk_pp(n->get_expr(), m) << " = " << mk_pp(n2->get_expr(), m) << "\n";);
                return true;
            }
        }
        return false;
    }

    app* theory_finite_set::mk_union(unsigned num_elems, expr* const* elems, sort* set_sort) {
        app *s = nullptr;
        for (unsigned i = 0; i < num_elems; ++i)
            s = s ? u.mk_union(s, u.mk_singleton(elems[i])) : u.mk_singleton(elems[i]);
        return s ? s : u.mk_empty(set_sort);
    }


    bool theory_finite_set::is_new_axiom(expr* a, expr* b) {
        struct insert_obj_pair_table : public trail {
            obj_pair_hashtable<expr, expr> &table;
            expr *a, *b;
            insert_obj_pair_table(obj_pair_hashtable<expr, expr> &t, expr *a, expr *b) : table(t), a(a), b(b) {}
            void undo() override {
                table.erase({a, b});
            }
        };
        if (m_clauses.members.contains({a, b}))
            return false;
        m_clauses.members.insert({a, b});
        ctx.push_trail(insert_obj_pair_table(m_clauses.members, a, b));
        return true;
    }

    /**
    * Instantiate axioms for a given element in a set.
    */
    void theory_finite_set::add_membership_axioms(expr *elem, expr *set) {
        TRACE(finite_set, tout << "add_membership_axioms: " << mk_pp(elem, m) << " in " << mk_pp(set, m) << "\n";);

        // Instantiate appropriate axiom based on set structure
        if (!is_new_axiom(elem, set))
            ;
        else if (u.is_empty(set))
            m_axioms.in_empty_axiom(elem);        
        else if (u.is_singleton(set)) 
            m_axioms.in_singleton_axiom(elem, set);        
        else if (u.is_union(set)) 
            m_axioms.in_union_axiom(elem, set);        
        else if (u.is_intersect(set)) 
            m_axioms.in_intersect_axiom(elem, set);        
        else if (u.is_difference(set)) 
            m_axioms.in_difference_axiom(elem, set);        
        else if (u.is_range(set))
            m_axioms.in_range_axiom(elem, set);        
        else if (u.is_map(set)) {
            // sort *elem_sort = u.finte_set_elem_sort(set->get_sort());
            
            // set.map_inverse can loop. need to check instance generation.
            m_axioms.in_map_axiom(elem, set);
            
            // this can also loop:
            m_axioms.in_map_image_axiom(elem, set);
        }
        else if (u.is_filter(set)) {
            m_axioms.in_filter_axiom(elem, set);
        }
    }

    void theory_finite_set::add_clause(theory_axiom* ax) {
        TRACE(finite_set, tout << "add_clause: " << *ax << "\n");
        ctx.push_trail(push_back_vector(m_clauses.axioms));
        ctx.push_trail(new_obj_trail(ax));
        m_clauses.axioms.push_back(ax);
        m_stats.m_num_axioms_created++;
    }

    theory * theory_finite_set::mk_fresh(context * new_ctx) {
        return alloc(theory_finite_set, *new_ctx);
    }

    void theory_finite_set::display(std::ostream & out) const {
        out << "theory_finite_set:\n";
        for (unsigned i = 0; i < m_clauses.axioms.size(); ++i)
            out << "[" << i << "]: " << *m_clauses.axioms[i] << "\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            display_var(out, v);
        for (unsigned i = 0; i < m_clauses.watch.size(); ++i) {
            if (m_clauses.watch[i].empty())
                continue;
            out << "watch[" << i << "] := " << m_clauses.watch[i] << "\n";
        }
        m_cardinality_solver.display(out);
    }

    void theory_finite_set::init_model(model_generator & mg) {
        TRACE(finite_set, tout << "init_model\n";);
        // Model generation will use default interpretation for sets
        // The model will be constructed based on the membership literals that are true
        m_factory = alloc(finite_set_factory, m, u.get_family_id(), mg.get_model());
        mg.register_factory(m_factory);
        collect_members();
        m_cardinality_solver.init_model(mg);
    }
   
    void theory_finite_set::collect_members() {
        // This method can be used to collect all elements that are members of sets
        // and ensure that the model factory has values for them.
        // For now, we rely on the default model construction.
        reset_set_members();

        for (auto f : m_set_in_decls) {
            for (auto n : ctx.enodes_of(f)) {
                if (!ctx.is_relevant(n))
                    continue;
                SASSERT(u.is_in(n->get_expr()));
                auto x = n->get_arg(0)->get_root();
                if (x->is_marked())
                    continue;
                x->set_mark();  // make sure we only do this once per element
                for (auto p : enode::parents(x)) {
                    if (!ctx.is_relevant(p))
                        continue;
                    if (!u.is_in(p->get_expr()))
                        continue;
                    bool b = ctx.find_assignment(p->get_expr()) == l_true;
                    auto set = p->get_arg(1)->get_root();
                    auto elem = p->get_arg(0)->get_root();
                    if (elem != x)
                        continue;
                    if (!m_set_members.contains(set)) {
                        using om = obj_map<enode, bool>;
                        auto m = alloc(om);
                        m_set_members.insert(set, m);
                    }
                    m_set_members.find(set)->insert(x, b);
                }
            }
        }
        for (auto f : m_set_in_decls) {
            for (auto n : ctx.enodes_of(f)) {
                SASSERT(u.is_in(n->get_expr()));
                auto x = n->get_arg(0)->get_root();     
                if (x->is_marked())
                    x->unset_mark();
            }
        }
    }

    // to collect range interpretations for S:
    // walk parents of S that are (set.in x S)
    // evaluate truth value of (set.in x S), evaluate x
    // add (eval(x), eval(set.in x S)) into a vector.
    // sort the vector by eval(x)
    // [(v1, b1), (v2, b2), ..., (vn, bn)]
    // for the first i, with b_i true, add the range [vi, v_{i+1}-1].
    // the last bn should be false by construction.

    void theory_finite_set::add_range_interpretation(enode* s) {
        vector<std::tuple<rational, enode *, bool>> elements;
        arith_value av(m);
        av.init(&ctx);
        for (auto p : enode::parents(s)) {
            if (!ctx.is_relevant(p))
                continue;
            if (u.is_in(p->get_expr())) {
                rational val;
                auto x = p->get_arg(0)->get_root();
                VERIFY(av.get_value_equiv(x->get_expr(), val) && val.is_int());
                elements.push_back({val, x, ctx.find_assignment(p->get_expr()) == l_true});
            }
        }
        std::stable_sort(elements.begin(), elements.end(),
                         [](auto const &a, auto const &b) { return std::get<0>(a) < std::get<0>(b); });


    }

    struct finite_set_value_proc : model_value_proc {    
        theory_finite_set &th;        
        app_ref m_unique_value;
        enode *n = nullptr;
        obj_map<enode, bool>* m_elements = nullptr;

        // use range interpretations if there is a range constraint and the base sort is integer
        bool use_range() {
            auto &m = th.m;
            sort *base_s = nullptr;
            VERIFY(th.u.is_finite_set(n->get_expr()->get_sort(), base_s));
            arith_util a(m);
            if (!a.is_int(base_s))
                return false;
            func_decl_ref range_fn(th.u.mk_range_decl(), m);
            return th.ctx.get_num_enodes_of(range_fn.get()) > 0;
        }

        finite_set_value_proc(theory_finite_set &th, enode *n, obj_map<enode, bool> *elements)
            : th(th), m_unique_value(th.m), n(n), m_elements(elements) {}

                finite_set_value_proc(theory_finite_set &th, app* value)
            : th(th), m_unique_value(value, th.m) {}

        void get_dependencies(buffer<model_value_dependency> &result) override {
            if (m_unique_value)
                return;
            if (!m_elements)
                return;
            bool ur = use_range();
            for (auto [n, b] : *m_elements)
                if (!ur || b)
                    result.push_back(model_value_dependency(n));
        }

        app *mk_value(model_generator &mg, expr_ref_vector const &values) override {   
            if (m_unique_value)
                return m_unique_value;
            auto s = n->get_sort();
            if (values.empty())
                return th.u.mk_empty(s);

            SASSERT(m_elements);            
            if (use_range())
                return mk_range_value(mg, values);
            else 
                return th.mk_union(values.size(), values.data(), s);
        }

        app *mk_range_value(model_generator &mg, expr_ref_vector const &values) {
            unsigned i = 0;
            arith_value av(th.m);
            av.init(&th.ctx);
            vector<std::tuple<rational, enode *, bool>> elems;
            for (auto [n, b] : *m_elements) {
                rational r;
                av.get_value(n->get_expr(), r);               
                elems.push_back({r, n, b});
            }
            std::stable_sort(elems.begin(), elems.end(),
                             [](auto const &a, auto const &b) { return std::get<0>(a) < std::get<0>(b); });
            app *range = nullptr;
            arith_util a(th.m);

            for (unsigned j = 0; j < elems.size(); ++j) {
                auto [r, n, b] = elems[j];
                if (!b)
                    continue;
                rational lo = r;
                rational hi = j + 1 < elems.size() ? std::get<0>(elems[j + 1]) - rational(1) : r;
                while (j + 1 < elems.size() && std::get<0>(elems[j + 1]) == hi + rational(1) && std::get<2>(elems[j + 1])) {
                    hi = std::get<0>(elems[j + 1]);
                    ++j;
                }
                auto new_range = th.u.mk_range(a.mk_int(lo), a.mk_int(hi));
                range = range ? th.u.mk_union(range, new_range) : new_range;
            }
            return range ? range : th.u.mk_empty(n->get_sort());        
        }
    };

    model_value_proc * theory_finite_set::mk_value(enode * n, model_generator & mg) {
        TRACE(finite_set, tout << "mk_value: " << mk_pp(n->get_expr(), m) << "\n";);
        app *value = m_cardinality_solver.get_unique_value(n->get_expr());
        if (value)
            return alloc(finite_set_value_proc, *this, value);
        obj_map<enode, bool>*elements = nullptr;
        n = n->get_root();
        m_set_members.find(n, elements); 
        return alloc(finite_set_value_proc, *this, n, elements);
    }


    /**
    * a theory axiom can be unasserted if it contains two or more literals that have
    * not been internalized yet.
    */
    bool theory_finite_set::activate_unasserted_clause() {
        for (auto const &clause : m_clauses.axioms) {
            if (assert_clause(clause))
                return true;
        }
        return false;
    }

    /*
     * Add x-1, x+1 in range axioms for every x in setop(range, S)
     * then x-1, x+1 will also propagate against setop(range, S).
     */
    bool theory_finite_set::activate_range_local_axioms() {
        bool new_axiom = false;
        func_decl_ref range_fn(u.mk_range_decl(), m);
        for (auto range : ctx.enodes_of(range_fn.get())) {
            SASSERT(u.is_range(range->get_expr()));
            auto v = range->get_th_var(get_id());
            for (auto p : m_var_data[v]->m_parent_setops) {
                auto w = p->get_th_var(get_id());
                for (auto in : m_var_data[w]->m_parent_in) {
                    if (activate_range_local_axioms(in->get_arg(0)->get_expr(), range))
                        new_axiom = true;
                }
            }
        }
        return new_axiom;
    }


    bool theory_finite_set::activate_range_local_axioms(expr* elem, enode* range) {
        auto v = range->get_th_var(get_id());
        auto &range_local = m_var_data[v]->m_range_local;
        auto &parent_in = m_var_data[v]->m_parent_in;

        // simplify elem to canonical form (e.g., (1+1) -> 2)
        expr_ref elem_simplified(elem, m);
        m_rw(elem_simplified);

        if (range_local.contains(elem_simplified))
            return false;
        arith_util a(m);
        expr_ref lo(a.mk_add(elem_simplified, a.mk_int(-1)), m);
        expr_ref hi(a.mk_add(elem_simplified, a.mk_int(1)), m);
        
        // simplify lo and hi to avoid nested expressions like ((1+1)+1)
        m_rw(lo);
        m_rw(hi);
        bool new_axiom = false;
        if (!range_local.contains(lo) && all_of(parent_in, [lo](enode* in) { return in->get_arg(0)->get_expr() != lo; })) {
            // lo is not range local and lo is not already in an expression (lo in range)
            // checking that lo is not in range_local is actually redundant because we will instantiate 
            // membership expressions for every range local expression.
            // but we keep this set and check for now in case we want to change the saturation strategy.
            ctx.push_trail(push_back_vector(range_local));
            range_local.push_back(lo);
            m_axioms.in_range_axiom(lo, range->get_expr());
            new_axiom = true;
        }
        if (!range_local.contains(hi) &&
            all_of(parent_in, [&hi](enode *in) { return in->get_arg(0)->get_expr() != hi; })) {
            ctx.push_trail(push_back_vector(range_local));
            range_local.push_back(hi);
            m_axioms.in_range_axiom(hi, range->get_expr());
            new_axiom = true;
        }
        return new_axiom;
    }

    bool theory_finite_set::assert_clause(theory_axiom const *ax) {
        expr *unit = nullptr;
        unsigned undef_count = 0;
        auto &clause = ax->clause;
        for (auto e : clause) {
            switch (ctx.find_assignment(e)) {
            case l_true:
                return false; // clause is already satisfied
            case l_false:
                break;
            case l_undef:
                ++undef_count;
                unit = e;
                break;
            }
        }

        if (undef_count == 1) {
            TRACE(finite_set, tout << "propagate unit:" << clause << "\n";);
            auto lit = mk_literal(unit);
            literal_vector antecedent;
            for (auto e : clause) {
                if (e != unit)
                    antecedent.push_back(~mk_literal(e));
            }
            m_stats.m_num_axioms_propagated++;
            enode_pair_vector eqs;
            auto just = ext_theory_propagation_justification(get_id(), ctx, antecedent.size(), antecedent.data(), eqs.size(), eqs.data(), 
                lit, ax->params.size(), ax->params.data());
            auto bjust = ctx.mk_justification(just);
            if (ctx.clause_proof_active()) {
                // assume all justifications is a non-empty list of symbol parameters
                // proof logging is basically broken: it doesn't log propagations, but instead
                // only propagations that are processed by conflict resolution. 
                // this misses conflicts at base level.
                proof_ref pr(m);
                proof_ref_vector args(m);
                for (auto a : antecedent) 
                    args.push_back(m.mk_hypothesis(ctx.literal2expr(a)));          
                pr = m.mk_th_lemma(get_id(), unit, args.size(), args.data(), ax->params.size(), ax->params.data());
                justification_proof_wrapper jp(ctx, pr.get(), false);
                ctx.get_clause_proof().propagate(lit, &jp, antecedent);
                jp.del_eh(m);
            }
            ctx.assign(lit, bjust);                                
            return true;
        }
        bool is_conflict = (undef_count == 0);
        if (is_conflict)
            m_stats.m_num_axioms_conflicts++;
        else
            m_stats.m_num_axioms_case_splits++;
        TRACE(finite_set, tout << "assert " << (is_conflict ? "conflict" : "case split") << clause << "\n";);
        literal_vector lclause;
        for (auto e : clause)
            lclause.push_back(mk_literal(e));
        ctx.mk_th_axiom(get_id(), lclause, ax->params.size(), ax->params.data());
        return true;
    }

    std::ostream& theory_finite_set::display_var(std::ostream& out, theory_var v) const {
        out << "v" << v << " := " << enode_pp(get_enode(v), ctx) << "\n";
        auto d = m_var_data[v];
        if (!d->m_setops.empty()) {
            out << "  setops: ";
            for (auto n : d->m_setops)
                out << enode_pp(n, ctx) << " ";
            out << "\n";
        }
        if (!d->m_parent_setops.empty()) {
            out << "  parent_setops: ";
            for (auto n : d->m_parent_setops)
                out << enode_pp(n, ctx) << " ";
            out << "\n";
        }
        if (!d->m_parent_in.empty()) {
            out << "  parent_in: ";
            for (auto n : d->m_parent_in)
                out << enode_pp(n, ctx) << " ";
            out << "\n";
        }

        return out;
    }

}  // namespace smt
