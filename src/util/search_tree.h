/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    search_tree.h

Abstract:

    A binary search tree for managing the search space of a DPLL(T) solver.
    It supports splitting on atoms, backtracking on conflicts, and activating nodes.

    Nodes can be in one of three states: open, closed, or active.
    - Closed nodes are fully explored (both children are closed).
    - Active nodes have no children and are currently being explored.
    - Open nodes either have children that are open or are leaves.
    
    A node can be split if it is active. After splitting, it becomes open and has two open children.

    Backtracking on a conflict closes all nodes below the last node whose atom is in the conflict set.

    Activation searches an open node closest to a seed node.

Author:

    Ilana Shapiro   2025-9-06

--*/

#include "util/util.h"
#include "util/vector.h"
#pragma once

namespace search_tree {

    enum class status { open, closed, active };

    template<typename Config>
    class node {
        typedef typename Config::literal literal;
        literal m_literal;
        node* m_left = nullptr, * m_right = nullptr, * m_parent = nullptr;
        status m_status;
        vector<literal> m_core;
    public:
        node(literal const& l, node* parent) :
            m_literal(l), m_parent(parent), m_status(status::open) {}
        ~node() {
            dealloc(m_left);
            dealloc(m_right);
        }

        status get_status() const { return m_status; }
        void set_status(status s) { m_status = s; }
        literal const& get_literal() const { return m_literal; }
        bool literal_is_null() const { return Config::is_null(m_literal); }
        void split(literal const& a, literal const& b) {
            SASSERT(!Config::literal_is_null(a));
            SASSERT(!Config::literal_is_null(b));
            if (m_status != status::active)
                return;
            SASSERT(!m_left);
            SASSERT(!m_right);
            m_left = alloc(node<Config>, a, this);
            m_right = alloc(node<Config>, b, this);
            m_status = status::open;
        }

        node* left() const { return m_left; }
        node* right() const { return m_right; }
        node* parent() const { return m_parent; }

        node* find_active_node() {
            if (m_status == status::active)
                return this;
            if (m_status != status::open)
                return nullptr;
            node* nodes[2] = { m_left, m_right };
            for (unsigned i = 0; i < 2; ++i) {
                auto res = nodes[i] ? nodes[i]->find_active_node() : nullptr;
                if (res)
                    return res;
            }
            if (m_left->get_status() == status::closed && m_right->get_status() == status::closed)
                m_status = status::closed;
            return nullptr;
        }

        void display(std::ostream& out, unsigned indent) const {
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

        bool has_core() const { return !m_core.empty(); }
        void set_core(vector<literal> const &core) { 
            m_core = core;  // just copy the Z3 vector
            // no sort, no deduplication
        }
        vector<literal> const & get_core() const { return m_core; }
        void clear_core() { m_core.clear(); }
    };

    template<typename Config>
    class tree {
        typedef typename Config::literal literal;
        scoped_ptr<node<Config>> m_root = nullptr;
        literal m_null_literal;
        random_gen m_rand;

        // return an active node in the subtree rooted at n, or nullptr if there is none
        // close nodes that are fully explored (whose children are all closed)
        node<Config>* activate_from_root(node<Config>* n) {
            if (!n)
                return nullptr;
            if (n->get_status() != status::open)
                return nullptr;
            auto left = n->left();
            auto right = n->right();
            if (!left && !right) {
                n->set_status(status::active);
                return n;
            }
            node<Config>* nodes[2] = { left, right };
            unsigned index = m_rand(2);
            auto child = activate_from_root(nodes[index]);
            if (child)
                return child;
            child = activate_from_root(nodes[1 - index]);
            if (child)
                return child;
            if (left && right && left->get_status() == status::closed && right->get_status() == status::closed) 
                n->set_status(status::closed);            
            return nullptr;
        }

        void close_node(node<Config>* n) {
            if (!n)
                return;
            if (n->get_status() == status::closed)
                return;
            n->set_status(status::closed);
            close_node(n->left());
            close_node(n->right());
            while (n) {
                auto p = n->parent();
                if (!p)
                    return;
                if (p->get_status() != status::open)
                    return;
                if (p->left()->get_status() != status::closed)
                    return;
                if (p->right()->get_status() != status::closed)
                    return;
                p->set_status(status::closed);
                n = p;
            }
        }

        vector<literal> compute_resolvent(node<Config>* left, node<Config>* right) {
          vector<literal> res;

          if (!left->has_core() || !right->has_core()) return res;

          bool are_sibling_complements = left->parent() == right->parent();
          if (!are_sibling_complements)
              return res;

          auto &core_l = left->get_core();
          auto &core_r = right->get_core();

          // Helper to check if a literal is already in the vector
          auto contains = [](vector<literal> const &v, literal const &l) {
              for (unsigned i = 0; i < v.size(); ++i)
                  if (v[i] == l) return true;
              return false;
          };

          auto lit_l = left->get_literal();
          auto lit_r = right->get_literal();

          // Add literals from left core, skipping lit_l
          for (unsigned i = 0; i < core_l.size(); ++i) {
              if (core_l[i] != lit_l && !contains(res, core_l[i]))
                  res.push_back(core_l[i]);
          }

          // Add literals from right core, skipping lit_r
          for (unsigned i = 0; i < core_r.size(); ++i) {
              if (core_r[i] != lit_r && !contains(res, core_r[i]))
                  res.push_back(core_r[i]);
          }

          return res;
      }

      void try_resolve_upwards(node<Config>* p) {
        while (p) {
            auto left = p->left();
            auto right = p->right();
            if (!left || !right) return;
            // only attempt when both children are closed and at least one has a core
            if (left->get_status() != status::closed || right->get_status() != status::closed) return;
            if (!left->has_core() || !right->has_core()) return;

            // compute resolvent
            auto resolvent = compute_resolvent(left, right);
            if (resolvent.empty()) {
                // resolvent empty => unsat at root-subtree under p
                p->set_core(resolvent); // empty core
                close_node(p);
                // mark root closed if p == m_root?
                if (p == m_root.get()) {
                    m_root->set_status(status::closed);
                }
                // continue upward in case parent's sibling can now resolve
                p = p->parent();
                continue;
            }
            // If resolvent is identical to existing core at p we are done.
            if (p->has_core()) {
                // if new core doesn't strengthen, stop.
                if (resolvent == p->get_core()) return;
                // if new core subsumes old, replace; else maybe keep both (choose policy).
            }
            // attach resolvent to parent p and close p
            p->set_core(resolvent);
            close_node(p);
            // continue upward to see if parent can further resolve
            p = p->parent();
      }
    }

    public:

        tree(literal const& null_literal) : m_null_literal(null_literal) {
            reset();
        }

        void set_seed(unsigned seed) {
            m_rand.set_seed(seed);
        }

        void reset() {
            m_root = alloc(node<Config>, m_null_literal, nullptr);
            m_root->set_status(status::active);
        }
        
        // Split current node if it is active.
        // After the call, n is open and has two children.
        void split(node<Config>* n, literal const& a, literal const& b) {           
            n->split(a, b);
        }

        // conflict is given by a set of literals.
        // they are a subset of literals on the path from root to n
        void backtrack(node<Config>* n, vector<literal> const& conflict) {
            if (conflict.empty()) {
                close_node(m_root.get());
                m_root->set_status(status::closed);
                
                // store empty core at root to signal global unsat if you like
                m_root->set_core(vector<literal>()); // optional
                
                return;
            }           
            SASSERT(n != m_root.get());
            // all literals in conflict are on the path from root to n
            // remove assumptions from conflict to ensure this.
            DEBUG_CODE(
                auto on_path = [&](literal const& a) {
                    node<Config>* p = n;
                    while (p) {
                        if (p->get_literal() == a)
                            return true;
                        p = p->parent();
                    }
                    return false;
                };
                SASSERT(all_of(conflict, [&](auto const& a) { return on_path(a); }));
            );
            
            // find the node on the path whose literal is in conflict
            node<Config>* target = n;
            while (target) {
                if (any_of(conflict, [&](auto const& a) { return a == target->get_literal(); })) {
                    // store the conflict on the node that closes
                    target->set_core(conflict);
                    // close the subtree under target (preserves core on target)
                    close_node(target);
                    // now attempt to resolve upwards (recursive collapse)
                    try_resolve_upwards(target->parent());
                    return;
                }
                target = target->parent();
            }
            UNREACHABLE();
        }

        // return an active node in the tree, or nullptr if there is none
        // first check if there is a node to activate under n, 
        // if not, go up the tree and try to activate a sibling subtree
        node<Config>* activate_node(node<Config>* n) {
            if (!n) {
                if (m_root->get_status() == status::active)
                    return m_root.get();
                n = m_root.get();
            }
            auto res = activate_from_root(n);
            if (res)
                return res;

            auto p = n->parent();
            while (p) {
                if (p->left() && p->left()->get_status() == status::closed &&
                    p->right() && p->right()->get_status() == status::closed) {
                    p->set_status(status::closed);
                    n = p;                    
                    p = n->parent();
                    continue;
                }
                if (n == p->left()) {
                    res = activate_from_root(p->right());
                    if (res)
                        return res;
                }
                else {
                    VERIFY(n == p->right());
                    res = activate_from_root(p->left());
                    if (res)
                        return res;
                }                   
                n = p;
                p = n->parent();
            }
            return nullptr;
        }

        node<Config>* find_active_node() {
            return m_root->find_active_node();
        }

        bool is_closed() const {
            return m_root->get_status() == status::closed;
        }

        std::ostream& display(std::ostream& out) const {
            m_root->display(out, 0);
            return out;
        }

    };
}