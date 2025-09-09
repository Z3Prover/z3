#include "ast/ast_translation.h"
#include "ast/ast_ll_pp.h"

#include <vector>
#include <cstdlib>   // rand()
#include <ctime>

// forward declare
struct CubeNode;

typedef expr_ref_vector Cube;  // shorthand

enum state {
    open,
    closed,
    active
};

inline const char* to_string(state s) {
    switch (s) {
        case open:   return "open";
        case closed: return "closed";
        case active: return "active";
        default:     return "unknown";
    }
}

struct CubeNode {
    Cube cube;
    CubeNode* parent;
    std::vector<CubeNode*> children;
    
    state cube_state;

    CubeNode(const Cube& c, CubeNode* p = 0) 
        : cube(c), parent(p), cube_state(open) {}

    bool is_leaf() const { return children.empty(); }
};

class CubeTree {
public:
    CubeTree(ast_manager& m) {
        Cube root_cube(m);             // empty cube
        root = nullptr;
        std::srand((unsigned)std::time(0)); // is seeding the pseudo-random number generator used by std::rand()
    }

    ~CubeTree() {
        clear();
    }

    void clear() {
        delete_subtree(root); // actually delete all nodes
        root = nullptr;
    }

    bool empty() const {
        return root == nullptr;
    }

    CubeNode* get_root() { return root; } // if root is nullptr, tree is empty

    std::pair<CubeNode*, CubeNode*> add_children(CubeNode* parent,
                      const Cube& left_cube,
                      const Cube& right_cube) {
        IF_VERBOSE(1, verbose_stream() << "CubeTree: adding children of sizes " << left_cube.size() << " and " << right_cube.size() << " under parent of size " << (parent ? parent->cube.size() : 0) << "\n");
        CubeNode* left  = new CubeNode(left_cube, parent);
        CubeNode* right = new CubeNode(right_cube, parent);
        parent->children.push_back(left);
        parent->children.push_back(right);

        return {left, right}; // return the newly created children
    }

    // Add a new node under an existing parent
    void add_node(CubeNode* node, CubeNode* parent) {
        IF_VERBOSE(1, verbose_stream() << "CubeTree: adding node of size " << (node ? node->cube.size() : 0) << " under parent of size " << (parent ? parent->cube.size() : 0) << "\n");
        if (!node) return;

        // If no parent is specified, assume it's the root
        if (!parent) {
            root = node;
            node->parent = nullptr;
        } else {
            parent->children.push_back(node);
            node->parent = parent;
        }
    }

    // mark node as closed and propagate upward if its polarity pair is also closed (so we have a tautology, so its parent is closed, and thus all its siblings are closed)
    // return pointer to last affected ancestor (or nullptr if none) so we can select one of its siblings as the next cube
    CubeNode* remove_node_and_propagate(CubeNode* node, ast_manager& m) {
        if (!node || node == root || !node->is_leaf()) return nullptr; // error, root, or not a leaf

        CubeNode* parent = node->parent;
        CubeNode* last_closed = node;

        // helper: recursively mark a subtree inactive
        std::function<void(CubeNode*)> close_subtree = [&](CubeNode* n) {
            if (!n)
                return;
            n->cube_state = closed;
            for (CubeNode* child : n->children)
                close_subtree(child);
        };

        // mark this node as closed
        close_subtree(node);

        // propagate upward if parent became a "leaf" (all children closed)
        while (parent) {
            bool polarity_pair_closed = false;

            // get the index of the node in its parent's children
            auto it = std::find(parent->children.begin(), parent->children.end(), last_closed);
            SASSERT(it != parent->children.end());
            unsigned idx = std::distance(parent->children.begin(), it);

            CubeNode* polarity_pair = nullptr;
            if (idx % 2 == 0 && idx + 1 < parent->children.size()) {
                polarity_pair = parent->children[idx + 1]; // even index -> polarity pair is right sibling
            } else if (idx % 2 == 1) {
                polarity_pair = parent->children[idx - 1]; // odd index -> polarity pair is left sibling
            }

            // print the cube and its polarity pair CONTENTS, we have to loop thru each cube
            IF_VERBOSE(1, {
                verbose_stream() << "CubeTree: checking if parent node can be closed. Current node cube size: " << last_closed->cube.size() << " State: " << to_string(last_closed->cube_state) << " Cube: ";
                for (auto* e : last_closed->cube) {
                    verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                }
                verbose_stream() << "\n";
                if (polarity_pair) {
                    verbose_stream() << "CubeTree: polarity pair cube size: " << polarity_pair->cube.size() << " State: " << to_string(polarity_pair->cube_state) << " Cube: ";
                    for (auto* e : polarity_pair->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n";
                } else {
                    verbose_stream() << "CubeTree: no polarity pair found for current node\n";
                }
            });

            if (polarity_pair && polarity_pair->cube_state == closed) {
                polarity_pair_closed = true;
            } else {
                return last_closed;
            }

            if (!polarity_pair_closed) break;  // stop propagating

            SASSERT(parent->cube_state != active); // parent must not be currently worked on
            close_subtree(parent);   // mark parent and its subtree as closed
            last_closed = parent;    // track the last ancestor we mark
            parent = parent->parent;
        }

        return last_closed;
    }

    // get closest cube to current by getting a random sibling of current (if current was UNSAT and we removed it from the tree)
    // or by descending randomly to a leaf (if we split the current node) to get the newest cube split from the current
    // we descend randomly to a leaf instead of just taking a random child because it's possible another thread made more descendants
    CubeNode* get_next_cube(CubeNode* current, std::vector<CubeNode*>& frontier_roots, ast_manager& m, unsigned worker_id) {
        print_tree(m);
        
        IF_VERBOSE(1, verbose_stream() << "CubeTree: current cube is null: " << (current == nullptr) << "\n");
        if (!current) return nullptr;

        IF_VERBOSE(1, verbose_stream() << "CubeTree: getting next cube from current of size " << current->cube.size() << "\n");

        // lambda to find any open leaf in the subtree (explore all branches)
        std::function<CubeNode*(CubeNode*)> find_open_leaf = [&](CubeNode* node) -> CubeNode* {
            if (!node) return nullptr;
            if (node->is_leaf() && node->cube_state == open) return node;
            for (CubeNode* child : node->children) {
                CubeNode* open_leaf = find_open_leaf(child);
                if (open_leaf) return open_leaf;
            }
            return nullptr;
        };

        CubeNode* node = current;
        std::vector<CubeNode*> remaining_frontier_roots = frontier_roots;
        bool is_unexplored_frontier = frontier_roots.size() > 0 && current->cube.size() < frontier_roots[0]->cube.size(); // i.e. current is above the frontier (which always happens when we start with the empty cube!!)
        IF_VERBOSE(1, verbose_stream() << "CubeTree: current cube is " << (is_unexplored_frontier ? "above" : "within") << " the frontier. Current cube has the following children: \n");
        for (auto* child : current->children) {
            IF_VERBOSE(1, verbose_stream() << "  Child cube size: " << child->cube.size() << " State: " << to_string(child->cube_state) << " Cube: ");
            for (auto* e : child->cube) {
                IF_VERBOSE(1, verbose_stream() << mk_bounded_pp(e, m, 3) << " ");
            }
            IF_VERBOSE(1, verbose_stream() << "\n");
        }

        // if current is above the frontier, start searching from the first frontier root
        if (is_unexplored_frontier && !frontier_roots.empty()) {
            IF_VERBOSE(1, verbose_stream() << "CubeTree: Worker " << worker_id << " starting search from first frontier root. Frontier roots are:\n");
            for (auto* x : frontier_roots) {
                IF_VERBOSE(1, verbose_stream() << "  Cube size: " << x->cube.size() << " State: " << to_string(x->cube_state) << " Cube: ");
                for (auto* e : x->cube) {
                    IF_VERBOSE(1, verbose_stream() << mk_bounded_pp(e, m, 3) << " ");
                }
                IF_VERBOSE(1, verbose_stream() << "\n");
            }

            // begin code
            node = frontier_roots[0];
            // end code
            
            IF_VERBOSE(1, verbose_stream() << "CubeTree: Worker " << worker_id << " selected frontier root: ");
            for (auto* e : node->cube) {
                IF_VERBOSE(1, verbose_stream() << mk_bounded_pp(e, m, 3) << " ");
            }
            IF_VERBOSE(1, verbose_stream() << "\n");
            IF_VERBOSE(1, verbose_stream() << "This frontier root has children:\n");
            for (auto* child : node->children) {
                IF_VERBOSE(1, verbose_stream() << "  Child cube size: " << child->cube.size() << " State: " << to_string(child->cube_state) << " Cube: ");
                for (auto* e : child->cube) {
                    IF_VERBOSE(1, verbose_stream() << mk_bounded_pp(e, m, 3) << " ");
                }
                IF_VERBOSE(1, verbose_stream() << "\n");
            }
        }


        while (node) {
            // check open leaf descendants
            CubeNode* open_leaf_descendant = nullptr;
            open_leaf_descendant = find_open_leaf(node);
            
            if (open_leaf_descendant) {
                IF_VERBOSE(1, {verbose_stream() << "CubeTree: Worker " << worker_id << " found open leaf descendant under node (which could be the node itself): ";
                    for (auto* e : node->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n  Open leaf descendant is: ";
                    for (auto* e : open_leaf_descendant->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n";
                });
                return open_leaf_descendant;
            }

            IF_VERBOSE(1, {verbose_stream() << "CubeTree: Worker " << worker_id << " found no open leaf descendants found under node: "; 
                for (auto* e : node->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n";
            });

            // DO NOT NEED to check siblings and their active leaf descendants
            // since this is handled by the recusion up the tree!! 
            // and checking siblings here is unsafe if we adhere to thread frontier optimizations

            // see if we're at a boundary of the frontier (i.e. we hit one of the frontier roots)
            auto it = std::find(remaining_frontier_roots.begin(), remaining_frontier_roots.end(), node);
            // get the index of the node in remaining_frontier_roots
            unsigned curr_root_idx = std::distance(remaining_frontier_roots.begin(), it);
            if (it != remaining_frontier_roots.end()) { // i.e. the node is in the list of remaining_frontier_roots
                IF_VERBOSE(1, verbose_stream() << "CubeTree: hit frontier root " << node << "\n");

                if (!remaining_frontier_roots.empty()) {
                    IF_VERBOSE(1, verbose_stream() << "CubeTree: picking next frontier root to search from.\n");
                    // pick the next frontier root (wrap around if at end)
                    // we do this so we either move onto the next split atom in the frontier (if we just processed neg(atom))
                    // or we get the negation of the atom we just processed (if we just processed pos(atom))
                    // since the other the splits are added is [pos, neg, ...] for each split atom
                    node = remaining_frontier_roots[curr_root_idx + 1 < remaining_frontier_roots.size() ? curr_root_idx + 1 : 0];
                    
                    // Remove exhausted frontier root
                    remaining_frontier_roots.erase(it);
                } else {
                    IF_VERBOSE(1, verbose_stream() << "CubeTree: resetting frontier after exhausting\n");
                    // Frontier exhausted: reset frontier_roots for next iteration
                    frontier_roots.clear();

                    // Start "global" search from current node
                    node = node->parent;
                }

                continue;
            }

            // Move up in the current frontier
            node = node->parent;
        }

        IF_VERBOSE(1, verbose_stream() << "CubeTree: no active cube found\n");
        return nullptr;
    }

    // Pretty-print the entire cube tree
    void print_tree(ast_manager& m) const {
        IF_VERBOSE(1, verbose_stream() << "=== CubeTree Dump ===\n");
        print_subtree(m, root, 0);
        IF_VERBOSE(1, verbose_stream() << "=== End Dump ===\n");
    }

private:
    CubeNode* root;

    // mark leaf as closed instead of deleting it
    void mark_leaf_closed(CubeNode* node) {
        if (!node) return;
        SASSERT(node->children.empty());
        node->cube_state = closed;
    }

    void delete_subtree(CubeNode* node) {
        if (!node) return;
        for (CubeNode* child : node->children) {
            delete_subtree(child);
        }
        delete node;
    }

    void print_subtree(ast_manager& m, CubeNode* node, int indent) const {
        if (!node) return;

        // indent according to depth
        for (int i = 0; i < indent; i++) IF_VERBOSE(1, verbose_stream() << "  ");

        IF_VERBOSE(1, verbose_stream() << "Node@" << node
                         << " size=" << node->cube.size()
                         << " state=" << to_string(node->cube_state)
                         << " cube={ ");

        for (expr* e : node->cube) {
            IF_VERBOSE(1, verbose_stream() << mk_bounded_pp(e, m, 3) << " ");
        }
        IF_VERBOSE(1, verbose_stream() << "}\n");

        for (CubeNode* child : node->children) {
            print_subtree(m, child, indent + 1);
        }
    }
};
