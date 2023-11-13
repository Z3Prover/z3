/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_ac_plugin.cpp

Abstract:

    plugin structure for ac functions

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11

Completion modulo AC
    
  E set of eqs
  pick critical pair xy = z by j1 xu = v by j2 in E
  Add new equation zu = xyu = vy by j1, j2


  Notes: 
  - Some equalities come from shared terms, so do not.
  

More notes:

  Justifications for new equations are joined (requires extension to egraph/justification)
  
  Process new merges so use list is updated
  Justifications for processed merges are recorded
    
  Updated equations are recorded for restoration on backtracking

  Keep track of foreign / shared occurrences of AC functions.
  - use register_shared to accumulate shared occurrences.

  Shared occurrences are rewritten modulo completion.
  When equal to a different shared occurrence, propagate equality.

--*/

#include "ast/euf/euf_ac_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    ac_plugin::ac_plugin(egraph& g, unsigned fid, unsigned op):
        plugin(g), m_fid(fid), m_op(op)
    {}

    void ac_plugin::register_node(enode* n) {
        
    }

    void ac_plugin::register_shared(enode* n) {
        auto m = to_monomial(n);
        auto const& ns = monomial(m);
        for (auto arg : ns) {
            arg->shared.push_back(m);
            m_node_trail.push_back(arg);
            push_undo(is_add_shared);
        }
        m_shared_trail.push_back(m);
        push_undo(is_register_shared);
    }

    void ac_plugin::undo() {
        auto k = m_undo.back();
        m_undo.pop_back();
        switch (k) {
        case is_add_eq: {
            auto const& eq = m_eqs.back();
            for (auto* n : monomial(eq.l))
                n->lhs.pop_back();
            for (auto* n : monomial(eq.r))
                n->rhs.pop_back();
            m_eqs.pop_back();
            break;
        }
        case is_add_node: {
            auto* n = m_node_trail.back();
            m_node_trail.pop_back();
            m_nodes[n->n->get_id()] = nullptr;
            n->~node();
            break;
        }
        case is_add_monomial: {         
            m_monomials.pop_back();
            m_monomial_enodes.pop_back();
            break;
        }
        case is_merge_node: {
            auto [other, old_shared, old_lhs, old_rhs] = m_merge_trail.back();
            auto* root = other->root;
            std::swap(other->next, root->next);
            root->shared.shrink(old_shared);
            root->lhs.shrink(old_lhs);
            root->rhs.shrink(old_rhs);
            m_merge_trail.pop_back();
            break;
        }
        case is_update_eq: {
            auto const & [idx, eq] = m_update_eq_trail.back();            
            m_eqs[idx] = eq;
            m_update_eq_trail.pop_back();
            break;
        }
        case is_add_shared: {
            auto n = m_node_trail.back();
            m_node_trail.pop_back();
            n->shared.pop_back();
            break;
        }
        case is_register_shared: {
            m_shared_trail.pop_back();
            break;
        }
        case is_join_justification: {
            m_dep_manager.pop_scope(1);
            break;
        }
        default:
            UNREACHABLE();
        }
    }
        
    std::ostream& ac_plugin::display(std::ostream& out) const {
        unsigned i = 0;
        for (auto const& eq : m_eqs) {
            out << i << ": " << eq.l << " == " << eq.r << ": ";
            for (auto n : monomial(eq.l))
                out << g.bpp(n->n) << " ";
            out << "== ";
            for (auto n : monomial(eq.r))
                out << g.bpp(n->n) << " ";
            out << "\n";
            ++i;
        }
        i = 0;
        for (auto m : m_monomials) {
            out << i << ": ";
            for (auto n : m)
                out << g.bpp(n->n) << " ";
            out << "\n";
            ++i;
        }
        for (auto n : m_nodes) {
            out << g.bpp(n->n) << " r: " << n->root_id() << "\n";
            out << "lhs ";
            for (auto l : n->lhs)
                out << l << " ";
            out << "rhs ";
            for (auto r : n->rhs)
                out << r << " ";
            out << "shared ";
            for (auto s : n->shared)
                out << s << " ";
            out << "\n";
        }
        return out;
    }

    void ac_plugin::merge_eh(enode* l, enode* r, justification j) {
        if (l == r)
            return;
        if (!is_op(l) && !is_op(r)) 
            merge(mk_node(l), mk_node(r), j);
        else 
            init_equation({ to_monomial(l), to_monomial(r), false, j });        
    }

    void ac_plugin::init_equation(eq const& e) {
        m_eqs.push_back(e);
        auto& eq = m_eqs.back();
        if (orient_equation(eq)) {
            push_undo(is_add_eq);
            unsigned eq_id = m_eqs.size() - 1;
            for (auto n : monomial(eq.l))
                n->lhs.push_back(eq_id);
            for (auto n : monomial(eq.r))
                n->rhs.push_back(eq_id);
        }
        else
            m_eqs.pop_back();
    }

    bool ac_plugin::orient_equation(eq& e) {
        auto& ml = monomial(e.l);
        auto& mr = monomial(e.r);
        if (ml.size() > mr.size())
            return true;
        if (ml.size() < mr.size()) {
            std::swap(e.l, e.r);
            return true;
        }
        else {
            std::sort(ml.begin(), ml.end(), [&](node* a, node* b) { return a->root_id() < b->root_id(); });
            std::sort(mr.begin(), mr.end(), [&](node* a, node* b) { return a->root_id() < b->root_id(); });
            for (unsigned i = ml.size(); i-- > 0;) {
                if (ml[i] == mr[i])
                    continue;
                if (ml[i]->root_id() < mr[i]->root_id())
                    std::swap(e.l, e.r);
                return true;
            }
            return false;
        }
    }

    void ac_plugin::merge(node* root, node* other, justification j) {
        for (auto n : equiv(other))
            n->root = root;
        m_merge_trail.push_back({ other, root->shared.size(), root->lhs.size(), root->rhs.size()});
        for (auto eq_id : other->lhs)
            set_processed(eq_id, false);
        for (auto eq_id : other->rhs)
            set_processed(eq_id, false);
        root->shared.append(other->shared);
        root->lhs.append(other->lhs);
        root->rhs.append(other->rhs);
        std::swap(root->next, other->next);
        push_undo(is_merge_node);
    }

    void ac_plugin::push_undo(undo_kind k) {
        m_undo.push_back(k);
        push_plugin_undo(get_id());
        m_undo_notify(); // tell main plugin to dispatch undo to this module.
    }

    unsigned ac_plugin::to_monomial(enode* n) {
        enode_vector& ns = m_todo;
        ns.reset();
        ptr_vector<node> ms;
        ns.push_back(n);
        for (unsigned i = 0; i < ns.size(); ++i) {
            n = ns[i];
            if (is_op(n)) {
                ns.append(n->num_args(), n->args());
                ns[i] = ns.back();
                ns.pop_back();
                --i;
            }
            else {
                ms.push_back(mk_node(n));
            }
        }
        return to_monomial(n, ms);
    }

    unsigned ac_plugin::to_monomial(enode* e, ptr_vector<node> const& ms) {
        unsigned id = m_monomials.size();
        m_monomials.push_back(ms);
        m_monomial_enodes.push_back(e);
        push_undo(is_add_monomial);
        return id;
    }

    ac_plugin::node* ac_plugin::node::mk(region& r, enode* n) {
        auto* mem = r.allocate(sizeof(node));
        node* res = new (mem) node();
        res->n = n;
        res->root = res;
        res->next = res;
        return res;
    }

    ac_plugin::node* ac_plugin::mk_node(enode* n) {
        unsigned id = n->get_id();
        if (m_nodes.size() > id && m_nodes[id])
            return m_nodes[id];
        auto* r = node::mk(get_region(), n);
        push_undo(is_add_node);
        m_nodes.setx(id, r, nullptr);
        m_node_trail.push_back(r);
        return r;
    }

    void ac_plugin::propagate() {
        while (true) {
            unsigned eq_id = pick_next_eq();
            if (eq_id == UINT_MAX)
                break;

            // simplify eq using processed
            for (auto other_eq : backward_iterator(eq_id))
                if (is_processed(other_eq)) 
                    backward_simplify(eq_id, other_eq);
            if (m_backward_simplified)
                continue;            

            // simplify processed using eq
            for (auto other_eq : forward_iterator(eq_id))
                if (is_processed(other_eq))
                    forward_simplify(other_eq, eq_id);

            // superpose, create new equations
            for (auto other_eq : superpose_iterator(eq_id))
                if (is_processed(other_eq))
                    superpose(eq_id, other_eq);

            // simplify to_simplify using eq
            for (auto other_eq : forward_iterator(eq_id))
                if (is_to_simplify(other_eq))
                    forward_simplify(other_eq, eq_id);

            set_processed(eq_id, true);
        }
        propagate_shared();
    }

    unsigned ac_plugin::pick_next_eq() {         
        for (unsigned i = 0, n = m_eqs.size(); i < n; ++i) {
            unsigned id = (i + m_next_eq_index) % n;
            auto const& eq = m_eqs[id];
            if (eq.is_processed)
                continue;
            ++m_next_eq_index;
            return id;
        }
        return UINT_MAX;       
    }

    void ac_plugin::set_processed(unsigned id, bool f) {
        auto& eq = m_eqs[id];
        if (eq.is_processed == f)
            return;
        m_update_eq_trail.push_back({ id, eq });
        eq.is_processed = f;
        push_undo(is_update_eq);
    }

    //
    // superpose iterator enumerates all equations where lhs of eq have element in common.
    //  
    unsigned_vector const& ac_plugin::superpose_iterator(unsigned eq_id) {
        auto const& eq = m_eqs[eq_id];
        m_src_r.reset();
        m_src_r.append(monomial(eq.r));
        init_ids_counts(eq_id, eq.l, m_src_ids, m_src_count);
        init_overlap_iterator(eq_id, eq.l);
        return m_lhs_eqs;
    }

    //
    // backward iterator allows simplification of eq
    // The rhs of eq is a super-set of lhs of other eq.
    // 
    unsigned_vector const& ac_plugin::backward_iterator(unsigned eq_id) {
        auto const& eq = m_eqs[eq_id];
        init_ids_counts(eq_id, eq.r, m_dst_ids, m_dst_count);
        init_overlap_iterator(eq_id, eq.r);
        m_backward_simplified = false;
        return m_lhs_eqs;
    }

    void ac_plugin::init_overlap_iterator(unsigned eq_id, unsigned monomial_id) {
        m_lhs_eqs.reset();
        for (auto n : monomial(monomial_id))
            m_lhs_eqs.append(n->root->lhs);

        // prune m_lhs_eqs to single occurrences
        unsigned j = 0;
        for (unsigned i = 0; i < m_lhs_eqs.size(); ++i) {
            unsigned id = m_lhs_eqs[i];
            m_eq_seen.reserve(id + 1, false);
            if (m_eq_seen[id])
                continue;
            if (id == eq_id)
                continue;
            m_lhs_eqs[j++] = id;
            m_eq_seen[id] = true;
        }
        m_lhs_eqs.shrink(j);
        for (auto id : m_lhs_eqs)
            m_eq_seen[id] = false;
    }

    //
    // forward iterator simplifies other eqs where their rhs is a superset of lhs of eq
    // 
    unsigned_vector const& ac_plugin::forward_iterator(unsigned eq_id) {
        auto& eq = m_eqs[eq_id];
        m_src_r.reset();
        m_src_r.append(monomial(eq.r));
        init_ids_counts(eq_id, eq.l, m_src_ids, m_src_count);
        unsigned min_r = UINT_MAX;
        node* min_n = nullptr;
        for (auto n : monomial(eq.l))
            if (n->root->rhs.size() < min_r)
                min_n = n, min_r = n->root->rhs.size();
        // found node that occurs in fewest rhs
        VERIFY(min_n);
        return min_n->rhs;
    }

    void ac_plugin::init_ids_counts(unsigned eq_id, unsigned monomial_id, unsigned_vector& ids, unsigned_vector& counts) {
        auto& eq = m_eqs[eq_id];
        reset_ids_counts(ids, counts);
        for (auto n : monomial(monomial_id)) {
            unsigned id = n->root_id();
            counts.setx(id, counts.get(id, 0) + 1, 0);
            ids.push_back(id);
        }
    }

    void ac_plugin::reset_ids_counts(unsigned_vector& ids, unsigned_vector& counts) {
        for (auto id : ids)
            counts[id] = 0;
        ids.reset();
    }

    void ac_plugin::forward_simplify(unsigned dst_eq, unsigned src_eq) { 

        if (src_eq == dst_eq)
            return;

        // check that left src.l is a subset of dst.r
        // dst = A -> BC 
        // src = B -> D  
        // post(dst) := A -> CD
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];

        reset_ids_counts(m_dst_ids, m_dst_count);

        unsigned src_l_size = monomial(src.l).size();
        unsigned src_r_size = m_src_r.size();

        // subtract src.l from dst.r if src.l is a subset of dst.r
        // new_rhs := old_rhs - src_lhs + src_rhs
        unsigned num_overlap = 0;
        for (auto n : monomial(dst.r)) {
            unsigned id = n->root_id();
            unsigned count = m_src_count.get(id, 0);
            if (count == 0) 
                m_src_r.push_back(n);
            else {
                unsigned dst_count = m_dst_count.get(id, 0);
                if (dst_count >= count)
                    m_src_r.push_back(n);
                else
                    m_dst_count.set(id, dst_count + 1), m_dst_ids.push_back(id), ++num_overlap;
            }
        }
        // The dst.r has to be a superset of src.l, otherwise simplification does not apply
        if (num_overlap == src_l_size) {
            auto new_r = to_monomial(nullptr, m_src_r);
            m_update_eq_trail.push_back({ dst_eq, m_eqs[dst_eq] });
            m_eqs[dst_eq].r = new_r;
            m_eqs[dst_eq].j = justify_rewrite(src_eq, dst_eq);
            push_undo(is_update_eq);
        }
        m_src_r.shrink(src_r_size);
    }

    void ac_plugin::backward_simplify(unsigned dst_eq, unsigned src_eq) {
        if (src_eq == dst_eq)
            return;

        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];
        //
        // dst_ids, dst_count contain rhs of dst_eq
        //  

        // check that src.l is a subset of dst.r
        reset_ids_counts(m_src_ids, m_src_count);

        bool is_subset = true;
        for (auto n : monomial(src.l)) {
            unsigned id = n->root_id();
            unsigned dst_count = m_dst_count.get(id, 0);
            if (dst_count == 0) {
                is_subset = false;
                break;
            }
            else {
                unsigned src_count = m_src_count.get(id, 0);
                if (src_count >= dst_count) {
                    is_subset = false;
                    break;
                }
                else
                    m_src_count.set(id, src_count + 1), m_src_ids.push_back(id);
            }
        }
        
        if (is_subset) {
            // dst_rhs := dst_rhs - src_lhs + src_rhs
            m_src_r.reset();
            m_src_r.append(monomial(src.r));
            // add to m_src_r elements of dst.r that are not in src.l
            for (auto n : monomial(dst.r)) {
                unsigned id = n->root_id();
                unsigned count = m_src_count.get(id, 0);
                if (count == 0) 
                    m_src_r.push_back(n);                
                else 
                    --m_src_count[id];                
            }
            auto new_r = to_monomial(nullptr, m_src_r);
            m_update_eq_trail.push_back({ dst_eq, m_eqs[dst_eq] });
            m_eqs[dst_eq].r = new_r;
            m_eqs[dst_eq].j = justify_rewrite(src_eq, dst_eq);
            push_undo(is_update_eq);
            m_backward_simplified = true;
        }
    }

    void ac_plugin::superpose(unsigned src_eq, unsigned dst_eq) {
        if (src_eq == dst_eq)
            return;
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];

        // AB -> C, AD -> E => BE ~ CD
        // m_src_ids, m_src_counts contains information about src (call it AD -> E)
        reset_ids_counts(m_dst_ids, m_dst_count);

        m_dst_r.reset();
        m_dst_r.append(monomial(dst.r));
        unsigned src_r_size = m_src_r.size();
        SASSERT(src_r_size == monomial(src.r).size());
        // dst_r contains C
        // src_r contains E

        // compute BE, initialize dst_ids, dst_counts
        for (auto n : monomial(dst.l)) {
            unsigned id = n->root_id();
            unsigned src_count = m_src_count.get(id, 0);
            unsigned dst_count = m_dst_count.get(id, 0);
            m_dst_count.set(id, dst_count + 1);
            m_dst_ids.push_back(id);
            if (src_count < dst_count)
                m_src_r.push_back(n);            
        }
        // compute CD
        for (auto n : monomial(src.l)) {
            unsigned id = n->root_id();
            unsigned dst_count = m_dst_count.get(id, 0);
            if (dst_count > 0)
                --m_dst_count[id];
            else
                m_dst_r.push_back(n);
        }

        justification j = justify_rewrite(src_eq, dst_eq);
        if (m_src_r.size() == 1 && m_dst_r.size() == 1) 
            push_merge(m_src_r[0]->n, m_dst_r[0]->n, j);        
        else 
            init_equation({ to_monomial(nullptr, m_src_r), to_monomial(nullptr, m_dst_r), false, j });

        m_src_r.shrink(src_r_size);
    }


    void ac_plugin::propagate_shared() {
        for (auto m : m_shared_trail)
            simplify_shared(m);
        // check for collisions, push_merge when there is a collision.
    }

    void ac_plugin::simplify_shared(unsigned monomial_id) {
        // apply processed as a set of rewrites
    }

    justification ac_plugin::justify_rewrite(unsigned eq1, unsigned eq2) {
        auto const& e1 = m_eqs[eq1];
        auto const& e2 = m_eqs[eq2];
        auto* j = m_dep_manager.mk_join(m_dep_manager.mk_leaf(e1.j), m_dep_manager.mk_leaf(e2.j));        
        j = justify_monomial(j, monomial(e1.l));
        j = justify_monomial(j, monomial(e1.r));
        j = justify_monomial(j, monomial(e2.l));
        j = justify_monomial(j, monomial(e2.r));
        m_dep_manager.push_scope();
        push_undo(is_join_justification);
        return justification::dependent(j);
    }

    justification::dependency* ac_plugin::justify_monomial(justification::dependency* j, ptr_vector<node> const& m) {
        for (auto n : m)
            if (n->root->n != n->n)
                j = m_dep_manager.mk_join(j, m_dep_manager.mk_leaf(justification::equality(n->root->n, n->n)));
        return j;
    }
}
