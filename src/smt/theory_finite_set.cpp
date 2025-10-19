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
#include "ast/ast_pp.h"

namespace smt {

    /**
    * Constructor.
    * Set up callback that adds axiom instantiations as clauses. 
    **/
    theory_finite_set::theory_finite_set(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("finite_set")),
        u(m),
        m_axioms(m), m_find(*this)
    {
        // Setup the add_clause callback for axioms
        std::function<void(theory_axiom const &)> add_clause_fn =
            [this](theory_axiom const &ax) {
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
        theory_var r = theory::mk_var(n);
        VERIFY(r == static_cast<theory_var>(m_find.mk_var()));
        SASSERT(r == static_cast<int>(m_var_data.size()));
        m_var_data.push_back(alloc(var_data));
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
            u.is_empty(e) || u.is_range(e)) {            
            m_var_data[r]->m_setops.push_back(n);
            ctx.push_trail(push_back_trail(m_var_data[r]->m_setops));
            for (auto arg : enode::args(n)) {
                if (!u.is_finite_set(arg->get_expr()))
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
        else if (u.is_map(e) || u.is_filter(e)) {
            NOT_IMPLEMENTED_YET();
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
        if (!is_attached_to_var(e))             
            ctx.attach_th_var(e, this, mk_var(e));

        // Assert immediate axioms
        // if (!ctx.relevancy())
        add_immediate_axioms(term);
                
        return true;
    }

    void theory_finite_set::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(u.is_finite_set(s));
        if (!is_attached_to_var(n))
            ctx.attach_th_var(n, this, mk_var(n));
    }

    void theory_finite_set::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE(finite_set, tout << "new_eq_eh: v" << v1 << " = v" << v2 << "\n";);
        m_find.merge(v1, v2); // triggers merge_eh, which triggers incremental generation of theory axioms
    }

    /**
    * Every dissequality has to be supported by at distinguishing element.
    * 
    * TODO: we can avoid instantiating the extensionality axiom if we know statically that e1, e2
    * can never be equal (say, they have different cardinalities or they are finite sets by construction
    * with elements that can differentiate the sets)
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
            m_axioms.extensionality_axiom(e1, e2);
        }
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
    final_check_status theory_finite_set::final_check_eh() {
        TRACE(finite_set, tout << "final_check_eh\n";);

        if (activate_unasserted_clause())
            return FC_CONTINUE;

        if (assume_eqs())
            return FC_CONTINUE;
        
        return FC_DONE;
    }


    /**
     * Add immediate axioms that can be asserted when the atom is created.
     * These are unit clauses that can be added immediately.
     * - (set.in x set.empty) is false
     * - (set.subset S T) <=> (= (set.union S T) T)  (or (= (set.intersect S T) S))
     * 
     * Other axioms:
     * - (set.singleton x) -> (set.in x (set.singleton x))
     * - (set.singleton x) -> (set.size (set.singleton x)) = 1
     * - (set.empty)       -> (set.size (set.empty)) = 0
     */
    void theory_finite_set::add_immediate_axioms(app* term) {
        expr *elem = nullptr, *set = nullptr;
        unsigned sz = m_clauses.axioms.size();
        if (u.is_in(term, elem, set) && u.is_empty(set))
            add_membership_axioms(elem, set);
        else if (u.is_subset(term))
            m_axioms.subset_axiom(term);
        else if (u.is_singleton(term, elem))
            m_axioms.in_singleton_axiom(elem, term);
       
        // Assert all new lemmas as clauses
        for (unsigned i = sz; i < m_clauses.axioms.size(); ++i)
            m_clauses.squeue.push_back(i);
    }

    void theory_finite_set::assign_eh(bool_var v, bool is_true) {
        TRACE(finite_set, tout << "assign_eh: v" << v << " is_true: " << is_true << "\n";);
        expr *e = ctx.bool_var2expr(v);
        // retrieve the watch list for clauses where e appears with opposite polarity
        unsigned idx = 2 * e->get_id() + (is_true ? 1 : 0);
        if (idx >= m_clauses.watch.size())
            return;

        // walk the watch list and try to find new watches or propagate
        unsigned j = 0;
        for (unsigned i = 0; i < m_clauses.watch[idx].size(); ++i) {
            TRACE(finite_set, tout << " watch[" << i << "] size: " << m_clauses.watch[i].size() << "\n";);
            auto clause_idx = m_clauses.watch[idx][i];
            auto &ax = m_clauses.axioms[clause_idx];
            auto &clause = ax.clause;
            if (any_of(clause, [&](expr *lit) { return ctx.find_assignment(lit) == l_true; })) {
                TRACE(finite_set, tout << "  satisfied\n";);
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
                TRACE(finite_set, tout << "  new watch for " << mk_pp(lit, m) << "\n";);
                found_swap = true;
                break;
            }
            if (found_swap) 
                continue;  // the clause is removed from this watch list
            // either all literals are false, or the other watch literal is propagating.
            m_clauses.squeue.push_back(clause_idx);
            TRACE(finite_set, tout << "  propagate clause\n";);
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
        TRACE(finite_set, tout << "propagate\n";);
        ctx.push_trail(value_trail(m_clauses.aqhead));
        ctx.push_trail(value_trail(m_clauses.sqhead));
        while (can_propagate() && !ctx.inconsistent()) {
            // activate newly created clauses
            while (m_clauses.aqhead < m_clauses.axioms.size()) 
                activate_clause(m_clauses.aqhead++);

            // empty the propagation queue of clauses to assert
            while (m_clauses.sqhead < m_clauses.squeue.size() && !ctx.inconsistent()) {
                auto index = m_clauses.squeue[m_clauses.sqhead++];
                auto const &clause = m_clauses.axioms[index];
                assert_clause(clause);
            }
        }      
    }

    void theory_finite_set::activate_clause(unsigned clause_idx) {
        TRACE(finite_set, tout << "activate_clause: " << clause_idx << "\n";);
        auto &ax = m_clauses.axioms[clause_idx];
        auto &clause = ax.clause;
        if (any_of(clause, [&](expr *e) { return ctx.find_assignment(e) == l_true; }))
            return;
        if (clause.size() <= 1) {
            m_clauses.squeue.push_back(clause_idx);
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
                auto &ax = th.m_clauses.axioms[index];
                auto &clause = ax.clause;
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
            auto& set = *m_set_members[r];
            ptr_vector<expr> elems;
            for (auto e : set)
                elems.push_back(e->get_expr());
            std::sort(elems.begin(), elems.end(), [](expr *a, expr *b) { return a->get_id() < b->get_id(); });
            expr *s = mk_union(elems.size(), elems.data(), n->get_expr()->get_sort());
            trail.push_back(s);
            enode *n2 = nullptr;
            if (!set_reprs.find(s, n2)) {
                set_reprs.insert(s, n2);
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

        if (!is_new_axiom(elem, set))
            return;

        // Instantiate appropriate axiom based on set structure
        if (u.is_empty(set)) {
            m_axioms.in_empty_axiom(elem);
        }
        else if (u.is_singleton(set)) {
            m_axioms.in_singleton_axiom(elem, set);
        }
        else if (u.is_union(set)) {
            m_axioms.in_union_axiom(elem, set);
        }
        else if (u.is_intersect(set)) {
            m_axioms.in_intersect_axiom(elem, set);
        }
        else if (u.is_difference(set)) {
            m_axioms.in_difference_axiom(elem, set);
        }
        else if (u.is_range(set)) {
            m_axioms.in_range_axiom(elem, set);
        }
        else if (u.is_map(set)) {
            m_axioms.in_map_axiom(elem, set);
            m_axioms.in_map_image_axiom(elem, set);
        }
        else if (u.is_filter(set)) {
            m_axioms.in_filter_axiom(elem, set);
        }        
    }

    void theory_finite_set::add_clause(theory_axiom const& ax) {
        TRACE(finite_set, tout << "add_clause: " << ax << "\n");
        ctx.push_trail(push_back_vector(m_clauses.axioms));
        m_clauses.axioms.push_back(ax);
        m_stats.m_num_axioms_created++;
    }

    theory * theory_finite_set::mk_fresh(context * new_ctx) {
        return alloc(theory_finite_set, *new_ctx);
    }

    void theory_finite_set::display(std::ostream & out) const {
        out << "theory_finite_set:\n";
        for (unsigned i = 0; i < m_clauses.axioms.size(); ++i)
            out << "[" << i << "]: " << m_clauses.axioms[i] << "\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            display_var(out, v);
        for (unsigned i = 0; i < m_clauses.watch.size(); ++i) {
            if (m_clauses.watch[i].empty())
                continue;
            out << "watch[" << i << "] := " << m_clauses.watch[i] << "\n";
        }
    }

    void theory_finite_set::init_model(model_generator & mg) {
        TRACE(finite_set, tout << "init_model\n";);
        // Model generation will use default interpretation for sets
        // The model will be constructed based on the membership literals that are true
        m_factory = alloc(finite_set_factory, m, u.get_family_id(), mg.get_model());
        mg.register_factory(m_factory);
        collect_members();
    }

    void theory_finite_set::collect_members() {
        // This method can be used to collect all elements that are members of sets
        // and ensure that the model factory has values for them.
        // For now, we rely on the default model construction.
        reset_set_members();
        for (auto f : m_set_in_decls) {
            for (auto n : ctx.enodes_of(f)) {
                SASSERT(u.is_in(n->get_expr()));
                auto x = n->get_arg(0);
                if (!ctx.is_relevant(x))
                    continue;
                x = x->get_root();
                if (x->is_marked())
                    continue;
                x->set_mark();  // make sure we only do this once per element
                for (auto p : enode::parents(x)) {
                    if (!ctx.is_relevant(p))
                        continue;
                    if (!u.is_in(p->get_expr()))
                        continue;
                    if (ctx.get_assignment(p->get_expr()) != l_true)
                        continue;
                    auto set = p->get_arg(1)->get_root();
                    auto elem = p->get_arg(0)->get_root();
                    if (elem != x)
                        continue;
                    if (!m_set_members.contains(set))
                        m_set_members.insert(set, alloc(obj_hashtable<enode>));
                    m_set_members.find(set)->insert(x);
                }
            }
        }
        for (auto f : m_set_in_decls) {
            for (auto n : ctx.enodes_of(f)) {
                SASSERT(u.is_in(n->get_expr()));
                auto x = n->get_arg(0);
                x = x->get_root();
                if (x->is_marked())
                    x->unset_mark();
            }
        }
    }

    struct finite_set_value_proc : model_value_proc {    
        theory_finite_set &th;        
        sort *s = nullptr;
        obj_hashtable<enode>* m_elements = nullptr;

        finite_set_value_proc(theory_finite_set &th, sort *s, obj_hashtable<enode> *elements)
            : th(th), s(s), m_elements(elements) {}

        void get_dependencies(buffer<model_value_dependency> &result) override {
            if (!m_elements)
                return;
            for (auto v : *m_elements)
                result.push_back(model_value_dependency(v));
        }

        app *mk_value(model_generator &mg, expr_ref_vector const &values) override {            
            SASSERT(values.empty() == !m_elements);
            if (values.empty()) 
                return th.u.mk_empty(s);

            SASSERT(m_elements);
            SASSERT(values.size() == m_elements->size());
            return th.mk_union(values.size(), values.data(), s);
        }
    };

    model_value_proc * theory_finite_set::mk_value(enode * n, model_generator & mg) {
        TRACE(finite_set, tout << "mk_value: " << mk_pp(n->get_expr(), m) << "\n";);       
        obj_hashtable<enode>*elements = nullptr;
        sort *s = n->get_expr()->get_sort();
        m_set_members.find(n->get_root(), elements); 
        return alloc(finite_set_value_proc, *this, s, elements);
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

    bool theory_finite_set::assert_clause(theory_axiom const &ax) {
        auto const &clause = ax.clause;
        expr *unit = nullptr;
        unsigned undef_count = 0;
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
            TRACE(finite_set, tout << " propagate unit: " << mk_pp(unit, m) << "\n" << clause << "\n";);
            auto lit = mk_literal(unit);
            literal_vector antecedent;
            for (auto e : clause) {
                if (e != unit)
                    antecedent.push_back(~mk_literal(e));
            }
            m_stats.m_num_axioms_propagated++;
            enode_pair_vector eqs;
            auto just = ext_theory_propagation_justification(get_id(), ctx, antecedent.size(), antecedent.data(), eqs.size(), eqs.data(), lit, ax.params.size(),
                                                       ax.params.data());
            auto bjust = ctx.mk_justification(just);
            if (ctx.clause_proof_active()) {
                // assume all justifications is a non-empty list of symbol parameters
                // proof logging is basically broken: it doesn't log propagations, but instead
                // only propagations that are processed by conflict resolution. 
                // this misses conflicts at base level.
                proof_ref pr(m);
                expr_ref_vector args(m);
                for (auto const& p : ax.params)
                    args.push_back(m.mk_const(p.get_symbol(), m.mk_proof_sort()));                  
                pr = m.mk_app(m.get_family_name(get_family_id()), args.size(), args.data(), m.mk_proof_sort());
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
        TRACE(finite_set, tout << " assert " << (is_conflict ? "conflict" : "case split") << clause << "\n";);
        literal_vector lclause;
        for (auto e : clause)
            lclause.push_back(mk_literal(e));
        ctx.mk_th_axiom(get_id(), lclause, ax.params.size(), ax.params.data());
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
