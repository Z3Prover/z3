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
  - Some equalities come from shared terms, some do not.
  
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

  - Elimination of redundant rules.
  -> forward and backward subsumption
     - apply forward subsumption when simplifying equality using processed
     - apply backward subsumption when simplifying processed and to_simplify

   Rewrite rules are reoriented after a merge of enodes.
   It simulates creating a critical pair:
   n -> n'
   n + k = j + k
   after merge
   n' + k = j + k, could be that n' + k < j + k < n + k in term ordering because n' < j, m < n

TODOs:

- Efficiency of handling shared terms.
  - The shared terms hash table is not incremental. 
    It could be made incremental by updating it on every merge similar to how the egraph handles it.
- V2 using multiplicities instead of repeated values in monomials.
- Squash trail updates when equations or monomials are modified within the same epoch.
  - by an epoch counter that can be updated by the egraph class whenever there is a push/pop.
  - store the epoch as a tick on equations and possibly when updating monomials on equations.

--*/

#include "ast/euf/euf_ac_plugin.h"
#include "ast/euf/euf_egraph.h"
#include "ast/ast_pp.h"

namespace euf {

    ac_plugin::ac_plugin(egraph& g, unsigned fid, unsigned op) :
        plugin(g), m_fid(fid), m_op(op),
        m_dep_manager(get_region()),
        m_hash(*this), m_eq(*this), m_monomial_table(m_hash, m_eq)
    {
        g.set_th_propagates_diseqs(m_fid);
    }

    ac_plugin::ac_plugin(egraph& g, func_decl* f) :
        plugin(g), m_fid(f->get_family_id()), m_decl(f),
        m_dep_manager(get_region()),
        m_hash(*this), m_eq(*this), m_monomial_table(m_hash, m_eq)
    {
        if (m_fid != null_family_id)
            g.set_th_propagates_diseqs(m_fid);
    }

    void ac_plugin::register_node(enode* n) {
        if (is_op(n))
            return;
        for (auto arg : enode_args(n))
            if (is_op(arg))
                register_shared(arg); // TODO optimization to avoid registering shared terms twice
    }

    void ac_plugin::register_shared(enode* n) {
        if (m_shared_nodes.get(n->get_id(), false))
            return;
        auto m = to_monomial(n);
        auto const& ns = monomial(m);
        for (auto arg : ns) {
            arg->shared.push_back(m);
            m_node_trail.push_back(arg);
            push_undo(is_add_shared_index);
        }
        m_shared_nodes.setx(n->get_id(), true, false);
        sort(monomial(m));
        m_shared_todo.insert(m_shared.size());
        m_shared.push_back({ n, m, justification::axiom(get_id()) });
        push_undo(is_register_shared);
    }

    void ac_plugin::undo() {
        auto k = m_undo.back();
        m_undo.pop_back();
        switch (k) {
        case is_add_eq: {
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
            auto const& [idx, eq] = m_update_eq_trail.back();
            m_eqs[idx] = eq;
            m_update_eq_trail.pop_back();
            break;
        }
        case is_add_shared_index: {
            auto n = m_node_trail.back();
            m_node_trail.pop_back();
            n->shared.pop_back();
            break;
        }
        case is_add_eq_index: {
            auto n = m_node_trail.back();
            m_node_trail.pop_back();
            n->eqs.pop_back();
            break;
        }
        case is_register_shared: {
            auto s = m_shared.back();   
            m_shared_nodes[s.n->get_id()] = false;
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

    std::ostream& ac_plugin::display_monomial(std::ostream& out, ptr_vector<node> const& m) const {
        for (auto n : m) {
            if (n->n->num_args() == 0)
                out << mk_pp(n->n->get_expr(), g.get_manager()) << " ";
            else
                out << g.bpp(n->n) << " ";
        }
        return out;
    }

    std::ostream& ac_plugin::display_equation(std::ostream& out, eq const& e) const {
        display_status(out, e.status) << " ";
        display_monomial(out, monomial(e.l));
        out << "== ";
        display_monomial(out, monomial(e.r));
        return out;
    }

    std::ostream& ac_plugin::display_status(std::ostream& out, eq_status s) const {
        switch (s) {
        case eq_status::is_dead: out << "d"; break;
        case eq_status::processed: out << "p"; break;
        case eq_status::to_simplify: out << "s"; break;
        }
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
            if (n->eqs.empty() && n->shared.empty())
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

    void ac_plugin::merge_eh(enode* l, enode* r) {
        if (l == r)
            return;
        auto j = justification::equality(l, r);
        if (!is_op(l) && !is_op(r))
            merge(mk_node(l), mk_node(r), j);
        else
            init_equation(eq(to_monomial(l), to_monomial(r), j));
    }

    void ac_plugin::diseq_eh(enode* eq) {
        SASSERT(g.get_manager().is_eq(eq->get_expr()));
        enode* a = eq->get_arg(0), * b = eq->get_arg(1);
        a = a->get_closest_th_node(m_fid);
        b = b->get_closest_th_node(m_fid);
        SASSERT(a && b);
        register_shared(a);
        register_shared(b);
    }

    void ac_plugin::init_equation(eq const& e) {
        m_eqs.push_back(e);
        auto& eq = m_eqs.back();
        if (orient_equation(eq)) {
            
            unsigned eq_id = m_eqs.size() - 1;

            for (auto n : monomial(eq.l)) {
                if (!n->root->n->is_marked1()) {
                    n->root->eqs.push_back(eq_id);
                    n->root->n->mark1();
                    push_undo(is_add_eq_index);
                    m_node_trail.push_back(n->root);
                }
            }

            for (auto n : monomial(eq.r)) {
                if (!n->root->n->is_marked1()) {
                    n->root->eqs.push_back(eq_id);
                    n->root->n->mark1();
                    push_undo(is_add_eq_index);
                    m_node_trail.push_back(n->root);
                }
            }

            for (auto n : monomial(eq.l)) 
                n->root->n->unmark1();

            for (auto n : monomial(eq.r))
                n->root->n->unmark1();

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
                if (ml[i]->root_id() == mr[i]->root_id())
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
        if (m.m_bloom.m_tick == m_tick)
            return true;
        for (unsigned i = m.size(); i-- > 1; )
            if (m[i - 1]->root_id() > m[i]->root_id())
                return false;
        return true;
    }

    uint64_t ac_plugin::filter(monomial_t& m) {
        auto& bloom = m.m_bloom;
        if (bloom.m_tick == m_tick)
            return bloom.m_filter;
        bloom.m_filter = 0;
        for (auto n : m)
            bloom.m_filter |= (1ull << (n->root_id() % 64ull));
        if (!is_sorted(m))
            sort(m);
        bloom.m_tick = m_tick;
        return bloom.m_filter;
    }

    bool ac_plugin::can_be_subset(monomial_t& subset, monomial_t& superset) {
        if (subset.size() > superset.size())
            return false;
        auto f1 = filter(subset);
        auto f2 = filter(superset);
        return (f1 | f2) == f2;
    }

    bool ac_plugin::can_be_subset(monomial_t& subset, ptr_vector<node> const& m, bloom& bloom) {
        if (subset.size() > m.size())
            return false;
        if (bloom.m_tick != m_tick) {
            bloom.m_filter = 0;
            for (auto n : m)
                bloom.m_filter |= (1ull << (n->root_id() % 64ull));
            bloom.m_tick = m_tick;
        }
        auto f2 = bloom.m_filter;
        return (filter(subset) | f2) == f2;
    }

    void ac_plugin::merge(node* root, node* other, justification j) {
        for (auto n : equiv(other))
            n->root = root;
        m_merge_trail.push_back({ other, root->shared.size(), root->eqs.size() });
        for (auto eq_id : other->eqs)
            set_status(eq_id, eq_status::to_simplify);
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
            if (is_op(n)) 
                ns.append(n->num_args(), n->args());            
            else 
                m.push_back(mk_node(n));            
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
        while (true) {
            loop_start:
            unsigned eq_id = pick_next_eq();
            if (eq_id == UINT_MAX)
                break;

            TRACE("plugin", tout << "propagate " << eq_id << ": " << eq_pp(*this, m_eqs[eq_id]) << "\n");

            // simplify eq using processed
            TRACE("plugin", 
                  for (auto other_eq : backward_iterator(eq_id))
                      tout << "backward iterator " << eq_id << " vs " << other_eq << " " << is_processed(other_eq) << "\n");
            for (auto other_eq : backward_iterator(eq_id))
                if (is_processed(other_eq) && backward_simplify(eq_id, other_eq))
                    goto loop_start;

            set_status(eq_id, eq_status::processed);

            // simplify processed using eq
            for (auto other_eq : forward_iterator(eq_id))
                if (is_processed(other_eq))
                    forward_simplify(eq_id, other_eq);

            // superpose, create new equations
            for (auto other_eq : superpose_iterator(eq_id))
                if (is_processed(other_eq))
                    superpose(eq_id, other_eq);

            // simplify to_simplify using eq
            for (auto other_eq : forward_iterator(eq_id))
                if (is_to_simplify(other_eq))
                    forward_simplify(eq_id, other_eq);
        }
        propagate_shared();

        CTRACE("plugin", !m_shared.empty() || !m_eqs.empty(), display(tout));
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

    // reorient equations when the status of equations are set to to_simplify.
    void ac_plugin::set_status(unsigned id, eq_status s) {
        auto& eq = m_eqs[id];
        if (eq.status == eq_status::is_dead)
            return;
        if (s == eq_status::to_simplify && are_equal(monomial(eq.l), monomial(eq.r))) 
            s = eq_status::is_dead;
        
        if (eq.status != s) {
            m_update_eq_trail.push_back({ id, eq });
            eq.status = s;
            push_undo(is_update_eq);
        }
        switch (s) {
        case eq_status::processed:
        case eq_status::is_dead:
            m_to_simplify_todo.remove(id);
            break;
        case eq_status::to_simplify:
            m_to_simplify_todo.insert(id);
            orient_equation(eq);
            break;
        }        
    }

    //
    // superpose iterator enumerates all equations where lhs of eq have element in common.
    //  
    unsigned_vector const& ac_plugin::superpose_iterator(unsigned eq_id) {
        auto const& eq = m_eqs[eq_id];
        m_src_r.reset();
        m_src_r.append(monomial(eq.r).m_nodes);
        init_ref_counts(monomial(eq.l), m_src_l_counts);
        init_overlap_iterator(eq_id, monomial(eq.l));
        return m_eq_occurs;
    }

    //
    // backward iterator allows simplification of eq
    // The rhs of eq is a super-set of lhs of other eq.
    // 
    unsigned_vector const& ac_plugin::backward_iterator(unsigned eq_id) {
        auto const& eq = m_eqs[eq_id];
        init_ref_counts(monomial(eq.r), m_dst_r_counts);
        init_ref_counts(monomial(eq.l), m_dst_l_counts);
        m_dst_r.reset();
        m_dst_r.append(monomial(eq.r).m_nodes);
        init_subset_iterator(eq_id, monomial(eq.r));
        return m_eq_occurs;
    }

    void ac_plugin::init_overlap_iterator(unsigned eq_id, monomial_t const& m) {
        m_eq_occurs.reset();
        for (auto n : m)
            m_eq_occurs.append(n->root->eqs);
        compress_eq_occurs(eq_id);
    }

    //
    // add all but one of the use lists. Identify the largest use list and skip it.
    // The rationale is that [a, b] is a subset of [a, b, c, d, e] if
    // it has at least two elements (otherwise it would not apply as a rewrite over AC).
    // then one of the two elements has to be in the set of [a, b, c, d, e] \ { x }
    // where x is an arbitrary value from a, b, c, d, e. Not a two-element watch list, but still.
    //
    void ac_plugin::init_subset_iterator(unsigned eq_id, monomial_t const& m) {
        unsigned max_use = 0;
        node* max_n = nullptr;
        bool has_two = false;
        for (auto n : m)
            if (n->root->eqs.size() >= max_use)
                has_two |= max_n && (max_n != n->root), max_n = n->root, max_use = n->root->eqs.size();
        m_eq_occurs.reset();
        if (has_two) {
            for (auto n : m)
                if (n->root != max_n)
                    m_eq_occurs.append(n->root->eqs);
        }
        else {
            for (auto n : m) {
                m_eq_occurs.append(n->root->eqs);
                break;
            }
        }
        compress_eq_occurs(eq_id);
    }

    // prune m_eq_occurs to single occurrences
    void ac_plugin::compress_eq_occurs(unsigned eq_id) {
        unsigned j = 0;
        m_eq_seen.reserve(m_eqs.size() + 1, false);
        for (unsigned i = 0; i < m_eq_occurs.size(); ++i) {
            unsigned id = m_eq_occurs[i];            
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
        init_ref_counts(monomial(eq.l), m_src_l_counts);
        init_ref_counts(monomial(eq.r), m_src_r_counts);
        unsigned min_r = UINT_MAX;
        node* min_n = nullptr;
        for (auto n : monomial(eq.l))
            if (n->root->eqs.size() < min_r)
                min_n = n, min_r = n->root->eqs.size();
        // found node that occurs in fewest eqs
        VERIFY(min_n);
        return min_n->eqs;
    }

    void ac_plugin::init_ref_counts(monomial_t const& monomial, ref_counts& counts) const {
        init_ref_counts(monomial.m_nodes, counts);       
    }

    void ac_plugin::init_ref_counts(ptr_vector<node> const& monomial, ref_counts& counts) const {
        counts.reset();
        for (auto n : monomial)
            counts.inc(n->root_id(), 1);
    }

    bool ac_plugin::is_correct_ref_count(monomial_t const& m, ref_counts const& counts) const {
        return is_correct_ref_count(m.m_nodes, counts);
    }

    bool ac_plugin::is_correct_ref_count(ptr_vector<node> const& m, ref_counts const& counts) const {
        ref_counts check;
        init_ref_counts(m, check);
        return
            all_of(counts, [&](unsigned i) { return check[i] == counts[i]; }) &&
            all_of(check, [&](unsigned i) { return check[i] == counts[i]; });
    }

    void ac_plugin::forward_simplify(unsigned src_eq, unsigned dst_eq) {

        if (src_eq == dst_eq)
            return;

        // check that left src.l is a subset of dst.r
        // dst = A -> BC 
        // src = B -> D  
        // post(dst) := A -> CD
        auto& src = m_eqs[src_eq];  // src_r_counts, src_l_counts are initialized
        auto& dst = m_eqs[dst_eq];

        TRACE("plugin", tout << "forward simplify " << eq_pp(*this, src) << " " << eq_pp(*this, dst) << "\n");


        if (forward_subsumes(src_eq, dst_eq)) {
            TRACE("plugin", tout << "forward subsumed\n");
            set_status(dst_eq, eq_status::is_dead);
            return;
        }

        if (!can_be_subset(monomial(src.l), monomial(dst.r)))
            return;


        m_dst_r_counts.reset();

        unsigned src_l_size = monomial(src.l).size();
        unsigned src_r_size = m_src_r.size();

        SASSERT(is_correct_ref_count(monomial(src.l), m_src_l_counts));
        // subtract src.l from dst.r if src.l is a subset of dst.r
        // dst_rhs := dst_rhs - src_lhs + src_rhs
        //         := src_rhs + (dst_rhs - src_lhs)
        //         := src_rhs + elements from dst_rhs that are in excess of src_lhs
        unsigned num_overlap = 0;
        for (auto n : monomial(dst.r)) {
            unsigned id = n->root_id();
            unsigned dst_count = m_dst_r_counts[id];
            unsigned src_count = m_src_l_counts[id];
            if (dst_count > src_count) {
                m_src_r.push_back(n);
                m_dst_r_counts.dec(id, 1);
            }
            else if (dst_count < src_count) {
                m_src_r.shrink(src_r_size);
                return;             
            }
            else
                ++num_overlap;            
        }
        // The dst.r has to be a superset of src.l, otherwise simplification does not apply
        if (num_overlap != src_l_size) {
            m_src_r.shrink(src_r_size);
            return;
        }
        auto j = justify_rewrite(src_eq, dst_eq);
        reduce(m_src_r, j);
        auto new_r = to_monomial(m_src_r);
        index_new_r(dst_eq, monomial(m_eqs[dst_eq].r), monomial(new_r));
        m_update_eq_trail.push_back({ dst_eq, m_eqs[dst_eq] });
        m_eqs[dst_eq].r = new_r;
        m_eqs[dst_eq].j = j;
        push_undo(is_update_eq);
        m_src_r.reset();
        m_src_r.append(monomial(src.r).m_nodes);
        TRACE("plugin", tout << "rewritten to " << m_pp(*this, monomial(new_r)) << "\n");
    }

    bool ac_plugin::backward_simplify(unsigned dst_eq, unsigned src_eq) {
        if (src_eq == dst_eq)
            return false;

        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq]; // pre-computed dst_r_counts, dst_l_counts 
        //
        // dst_ids, dst_count contain rhs of dst_eq
        //
        TRACE("plugin", tout << "backward simplify " << eq_pp(*this, src) << " " << eq_pp(*this, dst) << " can-be-subset: " << can_be_subset(monomial(src.l), monomial(dst.r)) << "\n");

        if (backward_subsumes(src_eq, dst_eq)) {
            TRACE("plugin", tout << "backward subsumed\n");
            set_status(dst_eq, eq_status::is_dead);
            return true;
        }
        // check that src.l is a subset of dst.r
        if (!can_be_subset(monomial(src.l), monomial(dst.r)))
            return false;
        if (!is_subset(m_dst_r_counts, m_src_l_counts, monomial(src.l))) {
            TRACE("plugin", tout << "not subset\n");
            return false;
        }

        SASSERT(is_correct_ref_count(monomial(dst.r), m_dst_r_counts));

        ptr_vector<node> m(m_dst_r);
        init_ref_counts(monomial(src.l), m_src_l_counts);
        
        rewrite1(m_src_l_counts, monomial(src.r), m_dst_r_counts, m);
        auto j = justify_rewrite(src_eq, dst_eq);
        reduce(m, j);
        auto new_r = to_monomial(m);
        index_new_r(dst_eq, monomial(m_eqs[dst_eq].r), monomial(new_r));
        m_update_eq_trail.push_back({ dst_eq, m_eqs[dst_eq] });
        m_eqs[dst_eq].r = new_r;
        m_eqs[dst_eq].j = j;
        TRACE("plugin", tout << "rewritten to " << m_pp(*this, monomial(new_r)) << "\n");
        push_undo(is_update_eq);
        return true;
    }

    // dst_eq is fixed, dst_l_count is pre-computed for monomial(dst.l)
    // dst_r_counts is pre-computed for monomial(dst.r).
    // is dst_eq subsumed by src_eq?
    bool ac_plugin::backward_subsumes(unsigned src_eq, unsigned dst_eq) {
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];
        SASSERT(is_correct_ref_count(monomial(dst.l), m_dst_l_counts));
        SASSERT(is_correct_ref_count(monomial(dst.r), m_dst_r_counts));
        if (!can_be_subset(monomial(src.l), monomial(dst.l)))
            return false;
        if (!can_be_subset(monomial(src.r), monomial(dst.r)))
            return false;
        unsigned size_diff = monomial(dst.l).size() - monomial(src.l).size();
        if (size_diff != monomial(dst.r).size() - monomial(src.r).size())
            return false;
        if (!is_subset(m_dst_l_counts, m_src_l_counts, monomial(src.l)))
            return false;
        if (!is_subset(m_dst_r_counts, m_src_r_counts, monomial(src.r)))
            return false;  
        SASSERT(is_correct_ref_count(monomial(src.l), m_src_l_counts));
        SASSERT(is_correct_ref_count(monomial(src.r), m_src_r_counts));
        // add difference betwen dst.l and src.l to both src.l, src.r
        for (auto n : monomial(dst.l)) {
            unsigned id = n->root_id();
            SASSERT(m_dst_l_counts[id] >= m_src_l_counts[id]);
            unsigned diff = m_dst_l_counts[id] - m_src_l_counts[id];
            if (diff > 0) {
                m_src_l_counts.inc(id, diff);
                m_src_r_counts.inc(id, diff);
            }
        }
        // now dst.r and src.r should align and have the same elements.
        // since src.r is a subset of dst.r we iterate over dst.r
        return all_of(monomial(dst.r), [&](node* n) { unsigned id = n->root_id(); return m_src_r_counts[id] == m_dst_r_counts[id]; });
    }

    // src_l_counts, src_r_counts are initialized for src.l, src.r
    bool ac_plugin::forward_subsumes(unsigned src_eq, unsigned dst_eq) {
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];
        SASSERT(is_correct_ref_count(monomial(src.l), m_src_l_counts));
        SASSERT(is_correct_ref_count(monomial(src.r), m_src_r_counts));
        if (!can_be_subset(monomial(src.l), monomial(dst.l)))
            return false;
        if (!can_be_subset(monomial(src.r), monomial(dst.r)))
            return false;
        unsigned size_diff = monomial(dst.l).size() - monomial(src.l).size();
        if (size_diff != monomial(dst.r).size() - monomial(src.r).size())
            return false;         
        if (!is_superset(m_src_l_counts, m_dst_l_counts, monomial(dst.l)))
            return false;
        if (!is_superset(m_src_r_counts, m_dst_r_counts, monomial(dst.r)))
            return false;
        SASSERT(is_correct_ref_count(monomial(dst.l), m_dst_l_counts));
        SASSERT(is_correct_ref_count(monomial(dst.r), m_dst_r_counts));
        for (auto n : monomial(src.l)) {
            unsigned id = n->root_id();
            SASSERT(m_src_l_counts[id] <= m_dst_l_counts[id]);
            unsigned diff = m_dst_l_counts[id] - m_src_l_counts[id];
            if (diff == 0)
                continue;
            m_dst_l_counts.dec(id, diff);
            if (m_dst_r_counts[id] < diff)
                return false;
            m_dst_r_counts.dec(id, diff);
        }

        return all_of(monomial(dst.r), [&](node* n) { unsigned id = n->root_id(); return m_src_r_counts[id] == m_dst_r_counts[id]; });
    }

    void ac_plugin::rewrite1(ref_counts const& src_l, monomial_t const& src_r, ref_counts& dst_counts, ptr_vector<node>& dst) {
        // pre-condition: is-subset is invoked so that src_l is initialized.
        // pre-condition: dst_count is also initialized.
        // remove from dst elements that are in src_l   
        // add elements from src_r  
        SASSERT(is_correct_ref_count(dst, dst_counts));
        SASSERT(&src_r.m_nodes != &dst);
        unsigned sz = dst.size(), j = 0;
        for (unsigned i = 0; i < sz; ++i) {
            auto* n = dst[i];
            unsigned id = n->root_id();
            unsigned dst_count = dst_counts[id];
            unsigned src_count = src_l[id];
            SASSERT(dst_count > 0);
            if (src_count == 0)
                dst[j++] = n;
            else if (src_count < dst_count) {
                dst[j++] = n;
                dst_counts.dec(id, 1);
            }          
        }
        dst.shrink(j);
        dst.append(src_r.m_nodes);
    }

    // rewrite monomial to normal form.
    bool ac_plugin::reduce(ptr_vector<node>& m, justification& j) {
        bool change = false;
        do {
        init_loop:
            if (m.size() == 1)
                return change;
            bloom b;            
            init_ref_counts(m, m_m_counts);
            for (auto n : m) {
                for (auto eq : n->root->eqs) {
                    if (!is_processed(eq))
                        continue;
                    auto& src = m_eqs[eq];
                   
                    if (!can_be_subset(monomial(src.l), m, b))
                        continue;
                    if (!is_subset(m_m_counts, m_eq_counts, monomial(src.l)))
                        continue;
                    TRACE("plugin", display_equation(tout << "reduce ", src) << "\n");
                    SASSERT(is_correct_ref_count(monomial(src.l), m_eq_counts));
                    rewrite1(m_eq_counts, monomial(src.r), m_m_counts, m);
                    j = join(j, eq);
                    change = true;
                    goto init_loop;
                }
            }            
        }
        while (false);
        return change;
    }

    // check that src is a subset of dst, where dst_counts are precomputed
    bool ac_plugin::is_subset(ref_counts const& dst_counts, ref_counts& src_counts, monomial_t const& src) {
        SASSERT(&dst_counts != &src_counts);
        init_ref_counts(src, src_counts);
        return all_of(src_counts, [&](unsigned idx) { return src_counts[idx] <= dst_counts[idx]; });
    }

    // check that dst is a superset of src, where src_counts are precomputed
    bool ac_plugin::is_superset(ref_counts const& src_counts, ref_counts& dst_counts, monomial_t const& dst) {
        SASSERT(&dst_counts != &src_counts);
        init_ref_counts(dst, dst_counts);
        return all_of(src_counts, [&](unsigned idx) { return src_counts[idx] <= dst_counts[idx]; });
    }

    void ac_plugin::index_new_r(unsigned eq, monomial_t const& old_r, monomial_t const& new_r) {
        for (auto n : old_r)
            n->root->n->mark1();
        for (auto n : new_r)
            if (!n->root->n->is_marked1()) {
                n->root->eqs.push_back(eq);
                m_node_trail.push_back(n->root);
                n->root->n->mark1();
                push_undo(is_add_eq_index);
            }
        for (auto n : old_r)
            n->root->n->unmark1();
        for (auto n : new_r)
            n->root->n->unmark1();
    }


    void ac_plugin::superpose(unsigned src_eq, unsigned dst_eq) {
        if (src_eq == dst_eq)
            return;
        auto& src = m_eqs[src_eq];
        auto& dst = m_eqs[dst_eq];

        TRACE("plugin", tout << "superpose: "; display_equation(tout, src); tout << " "; display_equation(tout, dst); tout << "\n";);
        // AB -> C, AD -> E => BE ~ CD
        // m_src_ids, m_src_counts contains information about src (call it AD -> E)
        m_dst_l_counts.reset();

        m_dst_r.reset();
        m_dst_r.append(monomial(dst.r).m_nodes);
        unsigned src_r_size = m_src_r.size();
        SASSERT(src_r_size == monomial(src.r).size());
        // dst_r contains C
        // src_r contains E

        // compute BE, initialize dst_ids, dst_counts
        bool overlap = false;
        for (auto n : monomial(dst.l)) {
            unsigned id = n->root_id();
            m_dst_l_counts.inc(id, 1);
            if (m_src_l_counts[id] < m_dst_l_counts[id])
                m_src_r.push_back(n);
            overlap |= m_src_l_counts[id] > 0;
        }

        if (!overlap) {
            m_src_r.shrink(src_r_size);
            return;
        }
        
        // compute CD
        for (auto n : monomial(src.l)) {
            unsigned id = n->root_id();
            if (m_dst_l_counts[id] > 0)
                m_dst_l_counts.dec(id, 1);
            else
                m_dst_r.push_back(n);
        }

        if (are_equal(m_src_r, m_dst_r)) {
            m_src_r.shrink(src_r_size);
            return;
        }

        TRACE("plugin", tout << m_pp(*this, m_src_r) << "== " << m_pp(*this, m_dst_r) << "\n";);

        justification j = justify_rewrite(src_eq, dst_eq);
        reduce(m_dst_r, j);
        reduce(m_src_r, j);
        if (m_src_r.size() == 1 && m_dst_r.size() == 1)
            push_merge(m_src_r[0]->n, m_dst_r[0]->n, j);
        else
            init_equation(eq(to_monomial(m_src_r), to_monomial(m_dst_r), j));

        m_src_r.reset();
        m_src_r.append(monomial(src.r).m_nodes);
    }

    bool ac_plugin::are_equal(monomial_t& a, monomial_t& b) {
        return filter(a) == filter(b) && are_equal(a.m_nodes, b.m_nodes);
    }

    bool ac_plugin::are_equal(ptr_vector<node> const& a, ptr_vector<node> const& b) {
        if (a.size() != b.size())
            return false;
        m_eq_counts.reset();
        for (auto n : a) 
            m_eq_counts.inc(n->root_id(), 1);
        
        for (auto n : b) {
            unsigned id = n->root_id();
            if (m_eq_counts[id] == 0)
                return false;
            m_eq_counts.dec(id, 1);
        }
        return true;
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
            TRACE("plugin", tout << "shared " << m_pp(*this, monomial(s1.m)) << "\n");
            if (!m_monomial_table.find(s1.m, s2)) 
                m_monomial_table.insert(s1.m, s1);
            else if (s2.n->get_root() != s1.n->get_root()) {
                TRACE("plugin", tout << m_pp(*this, monomial(s1.m)) << " == " << m_pp(*this, monomial(s2.m)) << "\n");
                push_merge(s1.n, s2.n, justification::dependent(m_dep_manager.mk_join(m_dep_manager.mk_leaf(s1.j), m_dep_manager.mk_leaf(s2.j))));
            }
        }
    }

    void ac_plugin::simplify_shared(unsigned idx, shared s) {
        auto j = s.j;
        auto old_m = s.m;
        ptr_vector<node> m1(monomial(old_m).m_nodes);
        TRACE("plugin", tout << "simplify " << m_pp(*this, monomial(old_m)) << "\n");
        if (!reduce(m1, j))
            return;

        auto new_m = to_monomial(m1);
        // update shared occurrences for members of the new monomial that are not already in the old monomial.
        for (auto n : monomial(old_m))
            n->root->n->mark1();
        for (auto n : m1)
            if (!n->root->n->is_marked1()) {
                n->root->shared.push_back(idx);
                m_shared_todo.insert(idx);
                m_node_trail.push_back(n->root);
                push_undo(is_add_shared_index);
            }
        for (auto n : monomial(old_m))
            n->root->n->unmark1();  
        m_update_shared_trail.push_back({ idx, s });
        push_undo(is_update_shared);
        m_shared[idx].m = new_m;
        m_shared[idx].j = j;
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

    justification ac_plugin::join(justification j, unsigned eq) {
        return justification::dependent(m_dep_manager.mk_join(m_dep_manager.mk_leaf(j), justify_equation(eq)));
    }

}
