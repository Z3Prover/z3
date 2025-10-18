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
    Constructor.
    Set up callback that adds axiom instantiations as clauses. 
    **/
    theory_finite_set::theory_finite_set(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("finite_set")),
        u(m),
        m_axioms(m)
    {
        // Setup the add_clause callback for axioms
        std::function<void(expr_ref_vector const &)> add_clause_fn = 
            [this](expr_ref_vector const& clause) {
                this->add_clause(clause);
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
    * Boolean atomic formulas for finite sets are one of:
    * (set.in x S)
    * (set.subset S T)
    * When an atomic formula is first created it is to be registered with the solver.
    * The internalize_atom method takes care of this.
    * Atomic formulas are special cases of terms (of non-Boolean type) so the first 
    * effect is to register the atom as a term.
    * The second effect is to set up tracking and assert axioms.
    * Tracking:
    *    For every occurrence (set.in x_i S_i) we track x_i. 
    * Axioms that can be added immediately.
    *    
    */
    bool theory_finite_set::internalize_atom(app * atom, bool gate_ctx) {
        TRACE(finite_set, tout << "internalize_atom: " << mk_pp(atom, m) << "\n";);

        internalize_term(atom);
        
        // Track membership elements (set.in)
        expr* elem = nullptr, *set = nullptr;
        if (u.is_in(atom, elem, set)) {
            auto n = ctx.get_enode(elem);
            if (!m_elements.contains(n)) {
                m_elements.insert(n);
                ctx.push_trail(insert_obj_trail(m_elements, n));
            }
        }

        // Assert immediate axioms
        // if (!ctx.relevancy())
        add_immediate_axioms(atom);
        
        return true;
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
                
        return true;
    }

    void theory_finite_set::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(u.is_finite_set(s));
        if (!is_attached_to_var(n))
            ctx.attach_th_var(n, this, mk_var(n));
    }

    void theory_finite_set::new_eq_eh(theory_var v1, theory_var v2) {
        TRACE(finite_set, tout << "new_eq_eh: v" << v1 << " = v" << v2 << "\n";);
        //    x = y, y in S
        // -------------------
        //  axioms for x in S

        auto n1 = get_enode(v1);
        auto n2 = get_enode(v2);
        auto e1 = n1->get_expr();
        auto e2 = n2->get_expr();
    }

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

        if (add_membership_axioms())
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
        unsigned sz = m_theory_axioms.size();
        if (u.is_in(term, elem, set) && u.is_empty(set))
            add_membership_axioms(elem, set);
        else if (u.is_subset(term))
            m_axioms.subset_axiom(term);
        else if (u.is_singleton(term, elem))
            m_axioms.in_singleton_axiom(elem, term);

        // Assert all new lemmas as clauses
        for (unsigned i = sz; i < m_theory_axioms.size(); ++i) 
            assert_clause(m_theory_axioms[i]);


        // TODO also add axioms for x in S u T, x in S n T, etc to the stack of m_theory_axioms.
        // The axioms are then instantiated if they are propagating.
    }

    /**
     *   Set membership is saturated with respect to set operations.
     *    For every (set.in x S) where S is a union, assert (or propagate) (set.in x S1) or (set.in x S2)
     */
    bool theory_finite_set::add_membership_axioms() {
        expr *elem1 = nullptr, *set1 = nullptr;

        // walk all parents of elem in congruence table.
        // if a parent is of the form elem' in S u T, or similar.
        // create clauses for elem in S u T.

        for (auto elem : m_elements) {
            if (!ctx.is_relevant(elem))
                continue;
            for (auto p : enode::parents(elem)) {
                if (!u.is_in(p->get_expr(), elem1, set1))
                    continue;
                if (elem->get_root() != p->get_arg(0)->get_root())
                    continue;  // elem is then equal to set1 but not elem1. This is a different case.
                if (!ctx.is_relevant(p))
                    continue;
                for (auto sib : *p->get_arg(1))
                    add_membership_axioms(elem->get_expr(), sib->get_expr());
            }
        }
        if (instantiate_false_lemma())
            return true;
        if (instantiate_unit_propagation())
            return true;
        if (instantiate_free_lemma())
            return true;
        return false;
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
        if (m_theory_axiom_exprs.contains({a, b}))
            return false;
        m_theory_axiom_exprs.insert({a, b});
        ctx.push_trail(insert_obj_pair_table(m_theory_axiom_exprs, a, b));
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

    void theory_finite_set::add_clause(expr_ref_vector const& clause) {
        TRACE(finite_set, tout << "add_clause: " << clause << "\n");
        ctx.push_trail(push_back_vector(m_theory_axioms));
        m_theory_axioms.push_back(clause);        
    }

    theory * theory_finite_set::mk_fresh(context * new_ctx) {
        return alloc(theory_finite_set, *new_ctx);
    }

    void theory_finite_set::display(std::ostream & out) const {
        out << "theory_finite_set:\n";
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
        for (auto x : m_elements) {
            if (!ctx.is_relevant(x))
                continue;
            x = x->get_root();
            if (x->is_marked())
                continue;
            x->set_mark();  // make sure we only do this once per element
            // TODO: use marking of x to avoid duplicate work
            for (auto p : enode::parents(x)) {
                if (!ctx.is_relevant(p))
                    continue;
                if (!u.is_in(p->get_expr()))
                    continue;
                if (ctx.get_assignment(p->get_expr()) != l_true)
                    continue;
                enode *elem = nullptr, *set = nullptr;
                set = p->get_arg(1)->get_root();
                elem = p->get_arg(0)->get_root();
                if (elem != x)
                    continue; 
                if (!m_set_members.contains(set)) 
                    m_set_members.insert(set, alloc(obj_hashtable<enode>));                
                m_set_members.find(set)->insert(x);
            }
        }
        for (auto x : m_elements) {
            x = x->get_root();
            if (x->is_marked())
                x->unset_mark();
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
            SASSERT(values.size() == m_elements->size());
            if (values.empty()) 
                return th.u.mk_empty(s);
            SASSERT(m_elements);
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
    * Lemmas that are currently assinged to false are conflicts. 
    * They should be asserted as soon as possible.
    * Only the first conflict needs to be asserted.
    * 
    */
    bool theory_finite_set::instantiate_false_lemma() {
        for (auto const& clause : m_theory_axioms) {
            bool all_false = all_of(clause, [&](expr *e) { return ctx.find_assignment(e) == l_false; });
            if (!all_false)
                continue;
            assert_clause(clause);
            return true;
        }
        return false;
    }

    /**
     * Lemmas that are unit propagating should be asserted as possible and can be asserted in a batch.
     * It is possible to assert a unit propagating lemma as a clause.
     * A more efficient approach is to add a Theory propagation with the solver.
     * A theory propagation gets recorded on the assignment trail and the overhead of undoing it is baked in to backtracking.
     * A theory axiom is also removed during backtracking.
    */
    bool theory_finite_set::instantiate_unit_propagation() {
        bool propagated = false;
        for (auto const &clause : m_theory_axioms) {
            expr *undef = nullptr;
            bool is_unit_propagating = true;
            for (auto e : clause) {
                switch (ctx.find_assignment(e)) {
                case l_false: continue;
                case l_true: is_unit_propagating = false; break;
                case l_undef:
                    if (undef != nullptr) 
                        is_unit_propagating = false;                    
                    undef = e;
                    break;
                }
                if (!is_unit_propagating)
                    break;
            }
            if (!is_unit_propagating || undef == nullptr)
                continue;      
            assert_clause(clause);
            propagated = true;
        }
        return propagated;
    }

    /**
     * We assume the lemmas in the queue are necessary for completeness.
     * So they all have to be enforced through case analysis.
     * Lemmas with more than one unassigned literal are asserted here.
     * The solver will case split on the unassigned literals to satisfy the lemma.
    */
    bool theory_finite_set::instantiate_free_lemma() {
        for (auto const& clause : m_theory_axioms) {
            if (any_of(clause, [&](expr *e) { return ctx.find_assignment(e) == l_true; }))
                continue;
            assert_clause(clause);
            return true;
        }
        return false;
    }

    void theory_finite_set::assert_clause(expr_ref_vector const &clause) {
        literal_vector lclause;
        for (auto e : clause)
            lclause.push_back(mk_literal(e));
        ctx.mk_th_axiom(get_id(), lclause);
    }

}  // namespace smt
