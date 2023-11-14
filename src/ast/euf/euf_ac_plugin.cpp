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
  
  - V2 can use multiplicities of elements to handle larger domains.
    - e.g. 3x + 100000y

More notes:

  Justifications for new equations are joined (requires extension to egraph/justification)
  
  Process new merges so use list is updated
  Justifications for processed merges are recorded
    
  Updated equations are recorded for restoration on backtracking

  Keep track of foreign / shared occurrences of AC functions.
  - use register_shared to accumulate shared occurrences.

  Shared occurrences are rewritten modulo completion.
  When equal to a different shared occurrence, propagate equality.

TODOs:
- Establish / fix formal termination properties in the presence of union-find.
  The formal interactions between union find and orienting the equations need to be established.  
  - Union-find merges can change the orientation of an equation and break termination.
  - For example, rules are currently not re-oriented if there is a merge. The rules could be re-oriented during propagation.
- Elimination of redundant rules.
  - superposition uses a stop-gap to avoid some steps. It should be revisited.
  -> forward and backward subsumption
     - apply forward subsumption when simplifying equality using processed
     - apply backward subsumption when simplifying processed and to_simplify
- Efficiency of handling shared terms.
  - The shared terms hash table is not incremental. 
    It could be made incremental by updating it on every merge similar to how the egraph handles it.
- V2 using multiplicities instead of repeated values in monomials.

--*/

#include "ast/euf/euf_ac_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    ac_plugin::ac_plugin(egraph& g, unsigned fid, unsigned op):
        plugin(g), m_fid(fid), m_op(op),
        m_dep_manager(get_region()),
        m_hash(*this), m_eq(*this), m_monomial_table(m_hash, m_eq)
    {}

    void ac_plugin::register_node(enode* n) {
        // no-op
    }

    void ac_plugin::register_shared(enode* n) {
        auto m = to_monomial(n);
        auto const& ns = monomial(m);
        for (auto arg : ns) {
            arg->shared.push_back(m);
            m_node_trail.push_back(arg);
            push_undo(is_add_shared);
        }
        sort(monomial(m));
        m_shared.push_back({ n, m, justification::axiom() });
        m_shared_todo.insert(m);
        push_undo(is_register_shared);
    }

    void ac_plugin::undo() {
        auto k = m_undo.back();
        m_undo.pop_back();
        switch (k) {
        case is_add_eq: {
            auto const& eq = m_eqs.back();
            for (auto* n : monomial(eq.l))
                n->eqs.pop_back();
            for (auto* n : monomial(eq.r))
                n->eqs.pop_back();
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
            break;
        }
        case is_merge_node: {
            auto [other, old_shared, old_eqs] = m_merge_trail.back();
            auto* root = other->root;
            std::swap(other->next, root->next);
            root->shared.shrink(old_shared);
            root->eqs.shrink(old_eqs);
            m_merge_trail.pop_back();
            ++m_tick;
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
            m_shared.pop_back();
            break;
        }
        case is_update_shared: {
            auto [id, s] = m_update_shared_trail.back();
            m_shared[id] = s;
            m_update_shared_trail.pop_back();
            break;
        }
        default:
            UNREACHABLE();
        }
    }

    std::ostream& ac_plugin::display_monomial(std::ostream& out, monomial_t const& m) const {
        for (auto n : m)
            out << g.bpp(n->n) << " ";
        return out;
    }

    std::ostream& ac_plugin::display_equation(std::ostream& out, eq const& e) const {
        display_monomial(out, monomial(e.l));
        out << " == ";
        display_monomial(out, monomial(e.r));
        return out;
    }
        
    std::ostream& ac_plugin::display(std::ostream& out) const {
        unsigned i = 0;
        for (auto const& eq : m_eqs) {
            out << i << ": " << eq.l << " == " << eq.r << ": ";
            display_equation(out, eq);
            out << "\n";
            ++i;
        }
        i = 0;
        for (auto m : m_monomials) {
            out << i << ": ";
            display_monomial(out, m);
            out << "\n";
            ++i;
        }
        for (auto n : m_nodes) {
            if (!n)
                continue;
            out << g.bpp(n->n) << " r: " << n->root_id() << " ";
            if (!n->eqs.empty()) {
                out << "eqs ";
                for (auto l : n->eqs)
                    out << l << " ";
            }
            if (!n->shared.empty()) {
                out << "shared ";
                for (auto s : n->shared)
                    out << s << " ";
            }
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
            init_equation(eq(to_monomial(l), to_monomial(r), j));        
    }

    void ac_plugin::init_equation(eq const& e) {
        m_eqs.push_back(e);
        auto& eq = m_eqs.back();
        if (orient_equation(eq)) {
            push_undo(is_add_eq);
            unsigned eq_id = m_eqs.size() - 1;
            for (auto n : monomial(eq.l))
                n->eqs.push_back(eq_id);
            for (auto n : monomial(eq.r))
                n->eqs.push_back(eq_id);
            m_to_simplify_todo.insert(eq_id);
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
            sort(ml);
            sort(mr);
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

    void ac_plugin::sort(monomial_t& m) {
        std::sort(m.begin(), m.end(), [&](node* a, node* b) { return a->root_id() < b->root_id(); });
    }

    bool ac_plugin::is_sorted(monomial_t const& m) const {
        if (m.m_filter.m_tick == m_tick)
            return true;
        for (unsigned i = m.size(); i-- > 1; ) 
            if (m[i-1]->root_id() > m[i]->root_id())
                return false;        
        return true;
    }

    uint64_t ac_plugin::filter(monomial_t& m) {
        auto& filter = m.m_filter;
        if (filter.m_tick == m_tick)
            return filter.m_filter;
        filter.m_filter = 0;
        for (auto n : m)
            filter.m_filter |= (1ull << (n->root_id() % 64ull));
        if (!is_sorted(m))
            sort(m);
        filter.m_tick = m_tick;
        return filter.m_filter;
    }

    bool ac_plugin::can_be_subset(monomial_t& subset, monomial_t& superset) {
        auto f1 = filter(subset);
        auto f2 = filter(superset);
        return (f1 | f2) == f2;
    }

    void ac_plugin::merge(node* root, node* other, justification j) {
        for (auto n : equiv(other))
            n->root = root;
        m_merge_trail.push_back({ other, root->shared.size(), root->eqs.size()});
        for (auto eq_id : other->eqs)
            set_processed(eq_id, false);
        for (auto m : other->shared)
            m_shared_todo.insert(m);
        root->shared.append(other->shared);
        root->eqs.append(other->eqs);
        std::swap(root->next, other->next);
        push_undo(is_merge_node);
        ++m_tick;
    }

    void ac_plugin::push_undo(undo_kind k) {
        m_undo.push_back(k);
        push_plugin_undo(get_id());
        m_undo_notify(); // tell main plugin to dispatch undo to this module.
    }

    unsigned ac_plugin::to_monomial(enode* n) {
        enode_vector& ns = m_todo;
        ns.reset();
        ptr_vector<node> m;
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
                m.push_back(mk_node(n));
            }
        }
        return to_monomial(n, m);
    }

    unsigned ac_plugin::to_monomial(enode* e, ptr_vector<node> const& ms) {
        unsigned id = m_monomials.size();
        m_monomials.push_back({ ms, bloom() });
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
        TRACE("plugin", display(tout));
        while (true) {
            unsigned eq_id = pick_next_eq();
            TRACE("plugin", tout << "propagate " << eq_id << "\n");
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
        while (!m_to_simplify_todo.empty()) {
            unsigned id = *m_to_simplify_todo.begin();          
            if (id < m_eqs.size() && is_to_simplify(id))
                return id;
            m_to_simplify_todo.remove(id);
        }
        return UINT_MAX;
    }

    void ac_plugin::set_processed(unsigned id, bool f) {
        auto& eq = m_eqs[id];
        if (eq.is_processed == f)
            return;
        if (f)
            m_to_simplify_todo.remove(id);
        else
            m_to_simplify_todo.insert(id);
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
        m_src_r.append(monomial(eq.r).m_nodes);
        init_ids_counts(monomial(eq.l), m_src_ids, m_src_count);
        init_overlap_iterator(eq_id, monomial(eq.l));
        return m_eq_occurs;
    }

    //
    // backward iterator allows simplification of eq
    // The rhs of eq is a super-set of lhs of other eq.
    // 
    unsigned_vector const& ac_plugin::backward_iterator(unsigned eq_id) {
        auto const& eq = m_eqs[eq_id];
        init_ids_counts(monomial(eq.r), m_dst_ids, m_dst_count);
        init_overlap_iterator(eq_id, monomial(eq.r));
        m_backward_simplified = false;
        return m_eq_occurs;
    }

    void ac_plugin::init_overlap_iterator(unsigned eq_id, monomial_t const& m) {
        m_eq_occurs.reset();
        for (auto n : m)
            m_eq_occurs.append(n->root->eqs);

        // prune m_eq_occurs to single occurrences
        unsigned j = 0;
        for (unsigned i = 0; i < m_eq_occurs.size(); ++i) {
            unsigned id = m_eq_occurs[i];
            m_eq_seen.reserve(id + 1, false);
            if (m_eq_seen[id])
                continue;
            if (id == eq_id)
                continue;
            m_eq_occurs[j++] = id;
            m_eq_seen[id] = true;
        }
        m_eq_occurs.shrink(j);
        for (auto id : m_eq_occurs)
            m_eq_seen[id] = false;
    }

    //
    // forward iterator simplifies other eqs where their rhs is a superset of lhs of eq
    // 
    unsigned_vector const& ac_plugin::forward_iterator(unsigned eq_id) {
        auto& eq = m_eqs[eq_id];
        m_src_r.reset();
        m_src_r.append(monomial(eq.r).m_nodes);
        init_ids_counts(monomial(eq.l), m_src_ids, m_src_count);
        unsigned min_r = UINT_MAX;
        node* min_n = nullptr;
        for (auto n : monomial(eq.l))
            if (n->root->eqs.size() < min_r)
                min_n = n, min_r = n->root->eqs.size();
        // found node that occurs in fewest rhs
        VERIFY(min_n);
        return min_n->eqs;
    }

    void ac_plugin::init_ids_counts(monomial_t const& monomial, unsigned_vector& ids, unsigned_vector& counts) {
        reset_ids_counts(ids, counts);
        for (auto n : monomial) {
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

        if (!can_be_subset(monomial(src.l), monomial(dst.r)))
            return;

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
        if (!can_be_subset(monomial(src.l), monomial(dst.r)))
            return;
        if (!is_subset(monomial(src.l)))
            return;

        // dst_rhs := dst_rhs - src_lhs + src_rhs
        auto new_r = rewrite(monomial(src.r), monomial(dst.r));
        m_update_eq_trail.push_back({ dst_eq, m_eqs[dst_eq] });
        m_eqs[dst_eq].r = new_r;
        m_eqs[dst_eq].j = justify_rewrite(src_eq, dst_eq);
        push_undo(is_update_eq);
        m_backward_simplified = true;
    }

    bool ac_plugin::subsumes(unsigned src_eq, unsigned dst_eq) {
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];
        if (!can_be_subset(monomial(src.l), monomial(dst.l)))
            return false;
        if (!can_be_subset(monomial(src.r), monomial(dst.r)))
            return false;

        NOT_IMPLEMENTED_YET();
        // dst.l \ src.l = dst.r \ dst.r
        return false;
    }

    unsigned ac_plugin::rewrite(monomial_t const& src_r, monomial_t const& dst_r) {
        // pre-condition: is-subset is invoked so that m_src_count is initialized.
        // pre-condition: m_dst_count is also initialized (once).
        m_src_r.reset();
        m_src_r.append(src_r.m_nodes);
        // add to m_src_r elements of dst.r that are not in src.l
        for (auto n : dst_r) {
            unsigned id = n->root_id();
            unsigned count = m_src_count.get(id, 0);
            if (count == 0)
                m_src_r.push_back(n);
            else
                --m_src_count[id];
        }
        return to_monomial(nullptr, m_src_r);
    }

    bool ac_plugin::is_subset(monomial_t const& dst) {
        reset_ids_counts(m_src_ids, m_src_count);
        for (auto n : dst) {
            unsigned id = n->root_id();
            unsigned dst_count = m_dst_count.get(id, 0);
            if (dst_count == 0)
                return false;
            else {
                unsigned src_count = m_src_count.get(id, 0);
                if (src_count >= dst_count) 
                    return false;                                    
                else
                    m_src_count.set(id, src_count + 1), m_src_ids.push_back(id);
            }
        }
        return true;
    }

    void ac_plugin::superpose(unsigned src_eq, unsigned dst_eq) {
        if (src_eq == dst_eq)
            return;
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];

        TRACE("plugin", tout << "superpose: "; display_equation(tout, src); tout << " "; display_equation(tout, dst); tout << "\n";);
        // AB -> C, AD -> E => BE ~ CD
        // m_src_ids, m_src_counts contains information about src (call it AD -> E)
        reset_ids_counts(m_dst_ids, m_dst_count);

        m_dst_r.reset();
        m_dst_r.append(monomial(dst.r).m_nodes);
        unsigned src_r_size = m_src_r.size();
        unsigned dst_r_size = m_dst_r.size();
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
        // one side is a proper subset of the other
        if (m_src_r.size() == src_r_size || m_dst_r.size() == dst_r_size) {
            m_src_r.shrink(src_r_size);
            return;
        }
        if (m_src_r.size() == m_dst_r.size()) {
            reset_ids_counts(m_dst_ids, m_dst_count);
            bool are_equal = true;
            for (auto n : m_dst_r) {
                unsigned id = n->root_id();
                unsigned dst_count = m_dst_count.get(id, 0);
                m_dst_count.set(id, dst_count + 1);
            }            
            for (auto n : m_src_r) {
                unsigned id = n->root_id();
                unsigned dst_count = m_dst_count.get(id, 0);
                if (dst_count > 0)
                    m_dst_count[id]--;
                else {
                    are_equal = false;
                    break;
                }
            }
            if (are_equal) {
                m_src_r.shrink(src_r_size);
                return;
            }                
        }

        TRACE("plugin", for (auto n : m_src_r) tout << g.bpp(n->n) << " "; tout << "== "; for (auto n : m_dst_r) tout << g.bpp(n->n) << " "; tout << "\n";);
        

        justification j = justify_rewrite(src_eq, dst_eq);
        if (m_src_r.size() == 1 && m_dst_r.size() == 1) 
            push_merge(m_src_r[0]->n, m_dst_r[0]->n, j);        
        else 
            init_equation(eq(to_monomial(nullptr, m_src_r), to_monomial(nullptr, m_dst_r), j));

        m_src_r.shrink(src_r_size);
    }

    //
    // simple version based on propagating all shared
    // todo: version touching only newly processed shared, and maintaining incremental data-structures.
    //       - hash-tables for shared monomials similar to the ones used for euf_table.
    //         the tables have to be updated (and re-sorted) whenever a child changes root.
    // 

    void ac_plugin::propagate_shared() {
        if (m_shared_todo.empty())
            return;
        while (!m_shared_todo.empty()) {
            auto idx = *m_shared_todo.begin();
            m_shared_todo.remove(idx);
            if (idx < m_shared.size()) 
                simplify_shared(idx, m_shared[idx]);
        }
        m_monomial_table.reset();
        for (auto const& s1 : m_shared) {
            shared s2;
            if (m_monomial_table.find(s1.m, s2)) {
                if (s2.n->get_root() != s1.n->get_root())
                    push_merge(s1.n, s2.n, justification::dependent(m_dep_manager.mk_join(m_dep_manager.mk_leaf(s1.j), m_dep_manager.mk_leaf(s2.j))));
            }
            else 
                m_monomial_table.insert(s1.m, s1);
        }
    }

    void ac_plugin::simplify_shared(unsigned idx, shared s) {
        bool change = true;
        while (change) {
            change = false;
            auto & m = monomial(s.m);
            init_ids_counts(m, m_dst_ids, m_dst_count);
            init_overlap_iterator(UINT_MAX, m);
            for (auto eq : m_eq_occurs) {
                auto& src = m_eqs[eq];
                if (!can_be_subset(monomial(src.l), m))
                    continue;
                if (!is_subset(monomial(src.l)))
                    continue;
                m_update_shared_trail.push_back({ idx, s });
                push_undo(is_update_shared);
                unsigned new_m = rewrite(monomial(src.r), m);
                m_shared[idx].m = new_m;
                m_shared[idx].j = justification::dependent(m_dep_manager.mk_join(m_dep_manager.mk_leaf(s.j), justify_equation(eq)));
                
                // update shared occurrences for members of the new monomial that are not already in the old monomial.
                for (auto n : monomial(s.m))
                    n->root->n->mark1();
                for (auto n : monomial(new_m))
                    if (!n->root->n->is_marked1()) {
                        n->root->shared.push_back(s.m);
                        m_shared_todo.insert(s.m);
                        m_node_trail.push_back(n->root);
                        push_undo(is_add_shared);
                    }
                for (auto n : monomial(s.m))
                    n->root->n->unmark1();

                s = m_shared[idx];
                change = true;
                break;
            }
        }
    }

    justification ac_plugin::justify_rewrite(unsigned eq1, unsigned eq2) {
        auto* j = m_dep_manager.mk_join(justify_equation(eq1), justify_equation(eq2));
        return justification::dependent(j);
    }

    justification::dependency* ac_plugin::justify_equation(unsigned eq) {
        auto const& e = m_eqs[eq];
        auto* j = m_dep_manager.mk_leaf(e.j);
        j = justify_monomial(j, monomial(e.l));
        j = justify_monomial(j, monomial(e.r));
        return j;
    }

    justification::dependency* ac_plugin::justify_monomial(justification::dependency* j, monomial_t const& m) {
        for (auto n : m)
            if (n->root->n != n->n)
                j = m_dep_manager.mk_join(j, m_dep_manager.mk_leaf(justification::equality(n->root->n, n->n)));
        return j;
    }
}
