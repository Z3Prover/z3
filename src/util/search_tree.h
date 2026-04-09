/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    search_tree.h

Abstract:

    A binary search tree for managing the search space of a DPLL(T) solver.
    It supports splitting on atoms, backtracking on conflicts, and activating nodes.

    Nodes can be in one of three states: open, closed, or active.
    - Closed nodes are fully explored (both children are closed).
    - Active nodes are currently assigned to a worker.
    - Open nodes are unsolved and available for future activation.

    Tree activation follows an SMTS-style policy: prefer nodes in lower
    accumulated-attempts bands, and then prefer deeper nodes within the same band.

    Tree expansion is also SMTS-inspired: a timeout does not force an immediate
    split. Instead, expansion is gated to avoid overgrowing the tree and prefers
    shallow timed-out leaves so that internal nodes can be revisited.

    Backtracking on a conflict closes all nodes below the last node whose atom is in the conflict set.

    Activation selects a best-ranked open node using accumulated attempts and depth.

Author:

    Ilana Shapiro   2025-9-06

--*/

#include "util/util.h"
#include "util/vector.h"
#pragma once

namespace search_tree {

    enum class status { open, closed, active };

    template <typename Config> class node {
        typedef typename Config::literal literal;
        literal m_literal;
        node *m_left = nullptr, *m_right = nullptr, *m_parent = nullptr;
        status m_status;
        vector<literal> m_core;
        unsigned m_num_activations = 0;
        unsigned m_effort_spent = 0;

    public:
        node(literal const &l, node *parent) : m_literal(l), m_parent(parent), m_status(status::open) {}
        ~node() {
            dealloc(m_left);
            dealloc(m_right);
        }

        status get_status() const {
            return m_status;
        }
        void set_status(status s) {
            m_status = s;
        }
        literal const &get_literal() const {
            return m_literal;
        }
        bool literal_is_null() const {
            return Config::is_null(m_literal);
        }
        void split(literal const &a, literal const &b) {
            SASSERT(!Config::literal_is_null(a));
            SASSERT(!Config::literal_is_null(b));
            if (m_status != status::active)
                return;
            SASSERT(!m_left);
            SASSERT(!m_right);
            m_left = alloc(node<Config>, a, this);
            m_right = alloc(node<Config>, b, this);
        }

        node* left() const { return m_left; }
        node* right() const { return m_right; }
        node* parent() const { return m_parent; }
        bool is_leaf() const { return !m_left && !m_right; }

        unsigned depth() const {
            unsigned d = 0;
            node* p = m_parent;
            while (p) {
                ++d;
                p = p->parent();
            }
            return d;
        }

        node *find_active_node() {
            if (m_status == status::active)
                return this;
            if (m_status == status::closed)
                return nullptr;
            node *nodes[2] = {m_left, m_right};
            for (unsigned i = 0; i < 2; ++i) {
                auto res = nodes[i] ? nodes[i]->find_active_node() : nullptr;
                if (res)
                    return res;
            }
            if (m_left->get_status() == status::closed && m_right->get_status() == status::closed)
                m_status = status::closed;
            return nullptr;
        }

        void display(std::ostream &out, unsigned indent) const {
            for (unsigned i = 0; i < indent; ++i)
                out << " ";
            Config::display_literal(out, m_literal);
            out << (get_status() == status::open ? " (o)" : get_status() == status::closed ? " (c)" : " (a)");
            out << "\n";
            if (m_left)
                m_left->display(out, indent + 2);
            if (m_right)
                m_right->display(out, indent + 2);
        }

        void set_core(vector<literal> const &core) {
            m_core = core;
        }
        vector<literal> const &get_core() const {
            return m_core;
        }
        void clear_core() {
            m_core.clear();
        }
        unsigned num_activations() const {
            return m_num_activations;
        }
        void mark_new_activation() {
            set_status(status::active);
            ++m_num_activations;
        }
        unsigned effort_spent() const {
            return m_effort_spent;
        }
        void add_effort(unsigned effort) {
            m_effort_spent += effort;
        }
    };

    template <typename Config> class tree {
        typedef typename Config::literal literal;
        scoped_ptr<node<Config>> m_root = nullptr;
        literal m_null_literal;
        random_gen m_rand;
        unsigned m_expand_factor = 2;
        unsigned m_effort_unit = 1000;
        
        // Used for tree expansion throttling policy in should_split()
        // SMTS says set to num workers, but our experiments show a big regression
        // Leaving at 0 for now, but making it confirgurable for future experimentation
        unsigned m_min_tree_size = 0; 

        struct candidate {
            node<Config>* n = nullptr;
            unsigned effort_band = UINT64_MAX;
            unsigned depth = 0;
        };

        // A measure of how much effort has been spent on the node, used for activation prioritization and expansion decisions
        // The effort unit is the workers' initial conflict budget, and effort spent grows by a factor defined in smt_parallel.h on each split attempt
        unsigned effort_band(node<Config> const* n) const {
            return n->effort_spent() / std::max<unsigned>(1, m_effort_unit);
        }

        // Node selection policy: prefer lower effort bands, then deeper nodes within the same band, and break ties randomly
        bool better(candidate const& a, candidate const& b) const {
            if (!a.n)
                return false;
            if (!b.n)
                return true;
            if (a.effort_band != b.effort_band)
                return a.effort_band < b.effort_band;
            if (a.depth != b.depth)
                return a.depth > b.depth;
            return false;
        }

        void select_next_node(node<Config>* cur, status target_status, candidate& best) const {
            if (!cur || cur->get_status() == status::closed)
                return;

            if (cur->get_status() == target_status) {
                candidate cand;
                cand.n = cur;
                cand.effort_band = effort_band(cur);
                cand.depth = cur->depth();

                if (better(cand, best))
                    best = cand;
            }

            select_next_node(cur->left(), target_status, best);
            select_next_node(cur->right(), target_status, best);
        }

        node<Config>* activate_best_node() {
            candidate best;
            select_next_node(m_root.get(), status::open, best);
            if (!best.n) {
                IF_VERBOSE(1, verbose_stream() << "NO OPEN NODES, trying active nodes for portfolio solving\n";);
                select_next_node(m_root.get(), status::active, best); // If no open nodes, only then consider active nodes for selection
            }

            if (!best.n)
                return nullptr;
            best.n->mark_new_activation();
            return best.n;
        }

        bool has_unvisited_open_node(node<Config>* cur) const {
            if (!cur || cur->get_status() == status::closed)
                return false;
            if (cur->get_status() == status::open && cur->num_activations() == 0)
                return true;
            return has_unvisited_open_node(cur->left()) || has_unvisited_open_node(cur->right());
        }

        unsigned count_unsolved_nodes(node<Config>* cur) const {
            if (!cur || cur->get_status() == status::closed)
                return 0;
            return 1 + count_unsolved_nodes(cur->left()) + count_unsolved_nodes(cur->right());
        }

        unsigned count_active_nodes(node<Config>* cur) const {
            if (!cur || cur->get_status() == status::closed)
                return 0;
            return (cur->get_status() == status::active ? 1 : 0) +
                   count_active_nodes(cur->left()) +
                   count_active_nodes(cur->right());
        }

        // Find the shallowest leaf node that at least 1 worker has visited
        // Used for tree expansion policy
        void find_shallowest_timed_out_leaf_depth(node<Config>* cur, unsigned& best_depth) const {
            if (!cur || cur->get_status() == status::closed)
                return;

            if (cur->is_leaf() && cur->effort_spent() > 0)
                best_depth = std::min(best_depth, cur->depth());

            find_shallowest_timed_out_leaf_depth(cur->left(), best_depth);
            find_shallowest_timed_out_leaf_depth(cur->right(), best_depth);
        }

        bool should_split(node<Config>* n) {
            if (!n || n->get_status() != status::active || !n->is_leaf())
                return false;

            unsigned num_active_nodes = count_active_nodes(m_root.get());
            unsigned unsolved_tree_size = count_unsolved_nodes(m_root.get());

            // If the tree is already large compared to the number of active nodes, be more aggressive about splitting to encourage exploration 
            if (unsolved_tree_size >= num_active_nodes * m_expand_factor)
                return false;

            // ONLY throttle when tree is "large enough" 
            if (unsolved_tree_size >= m_min_tree_size) {
                if (has_unvisited_open_node(m_root.get())) // Do not expand if there are still unvisited open nodes (prioritize exploration before expansion)
                    return false;
                if (m_rand(2) != 0) // Random throttling (50% rejection)
                    return false;
            }

            unsigned shallowest_timed_out_leaf_depth = UINT_MAX;
            find_shallowest_timed_out_leaf_depth(m_root.get(), shallowest_timed_out_leaf_depth);
            return n->depth() == shallowest_timed_out_leaf_depth;
        }

        // Bubble to the highest ancestor where ALL literals in the resolvent
        // are present somewhere on the path from that ancestor to root
        node<Config>* find_highest_attach(node<Config>* p, vector<literal> const& resolvent) {
            node<Config>* candidate = p;
            node<Config>* attach_here = p;

            while (candidate) {
                bool all_found = true;

                for (auto const& r : resolvent) {
                    bool found = false;
                    for (node<Config>* q = candidate; q; q = q->parent()) {
                        if (q->get_literal() == r) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        all_found = false;
                        break;
                    }
                }

                if (all_found) {
                    attach_here = candidate;  // bubble up to this node
                }

                candidate = candidate->parent();
            }

            return attach_here;
        }

        // Propagate closure upward via sibling resolution starting at node `cur`.
        // Returns true iff global UNSAT was detected.
        bool propagate_closure_upward(node<Config>* cur) {
            while (true) {
                node<Config>* parent = cur->parent();
                if (!parent)
                    return false;

                auto left  = parent->left();
                auto right = parent->right();
                if (!left || !right)
                    return false;

                if (left->get_status() != status::closed ||
                    right->get_status() != status::closed)
                    return false;

                if (left->get_core().empty() ||
                    right->get_core().empty())
                    return false;

                auto res = compute_sibling_resolvent(left, right);

                if (res.empty()) {
                    close(m_root.get(), res);   // global UNSAT
                    return true;
                }

                close(parent, res);
                cur = parent;  // keep bubbling
            }
        }

        void close(node<Config> *n, vector<literal> const &C) {
            if (!n || n->get_status() == status::closed)
                return;
            n->set_status(status::closed);
            n->set_core(C);
            close(n->left(), C);
            close(n->right(), C);
        }

        // Invariants:
        // Cores labeling nodes are subsets of the literals on the path to the node and the (external) assumption
        // literals. If a parent is open, then the one of the children is open.
        void close_with_core(node<Config> *n, vector<literal> const &C) {
            if (!n)
                return;

            // If the node is closed AND has a stronger or equal core, we are done. 
            // Otherwise, closed nodes may still accept a different (stronger) core to enable pruning/resolution higher in the tree.
            auto subseteq = [](vector<literal> const& A, vector<literal> const& B) {
                return all_of(A, [&](auto const &a) { return B.contains(a); });
            };
            if (n->get_status() == status::closed && subseteq(n->get_core(), C))
                return;

            node<Config> *p = n->parent();

            // The conflict does NOT depend on the decision literal at node n, so n’s split literal is irrelevant to this conflict
            // thus the entire subtree under n is closed regardless of the split, so the conflict should be attached higher, at the nearest ancestor that does participate
            if (p && all_of(C, [n](auto const &l) { return l != n->get_literal(); })) {
                close_with_core(p, C);
                return;
            }
            
            // Close descendants WITHOUT resolving
            close(n, C);

            if (!p)
                return;
            auto left = p->left();
            auto right = p->right();
            if (!left || !right)
                return;

            // only attempt when both children are closed and each has a *non-empty* core
            if (left->get_status() != status::closed || right->get_status() != status::closed) return;
            if (left->get_core().empty() || right->get_core().empty()) return;

            auto resolvent = compute_sibling_resolvent(left, right);
            if (resolvent.empty()) { // empty resolvent => global UNSAT
                close(m_root.get(), resolvent);
                return;
            }

            auto attach = find_highest_attach(p, resolvent);
            close(attach, resolvent);

            // try to propagate the highest attach node upward *with sibling resolution*
            // this handles the case when non-chronological backjumping takes us to a node whose sibling was closed by another thread
            node<Config>* cur = attach;
            propagate_closure_upward(cur);
        }

        // Given complementary sibling nodes for literals x and ¬x, sibling resolvent = (core_left ∪ core_right) \ {x,
        // ¬x}
        vector<literal> compute_sibling_resolvent(node<Config> *left, node<Config> *right) {
            vector<literal> res;

            auto &core_l = left->get_core();
            auto &core_r = right->get_core();

            if (core_l.empty() || core_r.empty() || left->parent() != right->parent())
                return res;

            auto lit_l = left->get_literal();
            auto lit_r = right->get_literal();

            for (auto const &lit : core_l)
                if (lit != lit_l && !res.contains(lit))
                    res.push_back(lit);
            for (auto const &lit : core_r)
                if (lit != lit_r && !res.contains(lit))
                    res.push_back(lit);
            return res;
        }

    public:
        tree(literal const &null_literal) : m_null_literal(null_literal) {
            reset();
        }

        void set_seed(unsigned seed) {
            m_rand.set_seed(seed);
        }

        void set_effort_unit(unsigned effort_unit) {
            m_effort_unit = std::max<unsigned>(1, effort_unit);
        }

        void reset() {
            m_root = alloc(node<Config>, m_null_literal, nullptr);
            m_root->mark_new_activation();
        }

        // On timeout, either expand the current leaf or reopen the node for a
        // later revisit, depending on the tree-expansion heuristic.
        bool try_split(node<Config> *n, literal const &a, literal const &b, unsigned effort) {
            if (!n || n->get_status() != status::active)
                return false;

            n->add_effort(effort);
            bool did_split = false;

            if (should_split(n)) {
                n->split(a, b);
                did_split = true;
            }

            // Reopen immediately on timeout, even if other workers are still active.
            // This keeps scheduling asynchronous: timeouts act as signals to reconsider
            // the search, not barriers requiring all workers to finish.
            //
            // Early reopening also creates a soft penalty (via accumulated effort),
            // reducing over-concentration while still allowing revisits.
            //
            // Waiting for all workers would introduce per-node synchronization, delay
            // diversification, and let a slow worker stall progress.
            n->set_status(status::open);
            
            return did_split;
        }

        // conflict is given by a set of literals.
        // they are subsets of the literals on the path from root to n AND the external assumption literals
        void backtrack(node<Config> *n, vector<literal> const &conflict) {
            if (conflict.empty()) {
                close_with_core(m_root.get(), conflict);
                return;
            }
            SASSERT(n != m_root.get());
            // all literals in conflict are on the path from root to n
            // remove assumptions from conflict to ensure this.
            DEBUG_CODE(auto on_path =
                           [&](literal const &a) {
                               node<Config> *p = n;
                               while (p) {
                                   if (p->get_literal() == a)
                                       return true;
                                   p = p->parent();
                               }
                               return false;
                           };
                       SASSERT(all_of(conflict, [&](auto const &a) { return on_path(a); })););

            // Walk upward to find the nearest ancestor whose decision participates in the conflict
            while (n) {
                if (any_of(conflict, [&](auto const &a) { return a == n->get_literal(); })) {
                    // close the subtree under n (preserves core attached to n), and attempt to resolve upwards
                    close_with_core(n, conflict);
                    return;
                }

                n = n->parent();
            }
            UNREACHABLE();
        }

        // return an active node in the tree, or nullptr if there is none
        // first check if there is a node to activate under n,
        // if not, go up the tree and try to activate a sibling subtree
        node<Config> *activate_node(node<Config> *n) {
            if (!n) {
                if (m_root->get_status() == status::active) {
                    m_root->mark_new_activation();
                    return m_root.get();
                }
            }
            return activate_best_node();
        }

        node<Config>* find_node_with_literal(literal const& lit) {
            return find_node_with_literal_rec(m_root.get(), lit);
        }

        node<Config>* find_node_with_literal_rec(node<Config>* n, literal const& lit) {
            if (!n)
                return nullptr;

            if (!Config::literal_is_null(n->get_literal()) &&
                n->get_literal() == lit)
                return n;

            if (auto* l = find_node_with_literal_rec(n->left(), lit))
                return l;

            return find_node_with_literal_rec(n->right(), lit);
        }

        vector<literal> const &get_core_from_root() const {
            return m_root->get_core();
        }

        bool is_closed() const {
            return m_root->get_status() == status::closed;
        }

        std::ostream &display(std::ostream &out) const {
            m_root->display(out, 0);
            return out;
        }
    };
}  // namespace search_tree
