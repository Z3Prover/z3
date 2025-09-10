#include "ast/ast_translation.h"
#include "ast/ast_ll_pp.h"

#include <vector>
#include <cstdlib>   // rand()
#include <ctime>

// forward declare
struct CubeNode;

typedef expr_ref_vector Cube;  // shorthand

enum State {
    open,
    closed,
    active
};

inline const char* to_string(State s) {
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
    
    State state;

    CubeNode(const Cube& c, CubeNode* p = 0) 
        : cube(c), parent(p), state(open) {}

    bool is_leaf() const { return children.empty(); }
};

class CubeTree {
public:
    CubeTree(ast_manager& m) {
        Cube empty_cube(m);
        root = new CubeNode(empty_cube);  // root is allocated properly
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
        if (!node) return nullptr; 

        CubeNode* parent = node->parent;
        CubeNode* last_closed = node;

        // helper: recursively mark a subtree inactive
        std::function<void(CubeNode*)> close_subtree = [&](CubeNode* n) {
            if (!n)
                return;
            n->state = closed;
            for (CubeNode* child : n->children)
                close_subtree(child);
        };

        // mark this node as closed
        close_subtree(node);

        // propagate upward if parent becomes UNSAT because one of its child polarity pairs (i.e. tautology) is closed
        while (parent) {
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
                verbose_stream() << "CubeTree: checking if parent node can be closed. Current node cube size: " << last_closed->cube.size() << " State: " << to_string(last_closed->state) << " Cube: ";
                for (auto* e : last_closed->cube) {
                    verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                }
                verbose_stream() << "\n";
                if (polarity_pair) {
                    verbose_stream() << "CubeTree: polarity pair cube size: " << polarity_pair->cube.size() << " State: " << to_string(polarity_pair->state) << " Cube: ";
                    for (auto* e : polarity_pair->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n";
                } else {
                    verbose_stream() << "CubeTree: no polarity pair found for current node\n";
                }
            });

            // node and its polarity pair are closed, this is a tautology, so the parent is closed, so the parent's entire subtree is closed
            if (polarity_pair && polarity_pair->state == closed) { 
                SASSERT(parent->state != active); // parent must not be currently worked on
                close_subtree(parent);   // mark parent and its subtree as closed
                last_closed = parent;    // track the last ancestor we mark
                parent = parent->parent;
            } else {
                break; // stop propagation
            }
        }

        return last_closed;
    }

    // get closest cube to current by getting a random sibling of current (if current was UNSAT and we removed it from the tree)
    // or by descending randomly to a leaf (if we split the current node) to get the newest cube split from the current
    // we descend randomly to a leaf instead of just taking a random child because it's possible another thread made more descendants
    CubeNode* get_next_cube(CubeNode* current, ast_manager& m, unsigned worker_id) {
        print_tree(m);
        
        IF_VERBOSE(1, verbose_stream() << "CubeTree: current cube is null: " << (current == nullptr) << "\n");
        if (!current) return nullptr;

        IF_VERBOSE(1, verbose_stream() << "CubeTree: getting next cube from current of size " << current->cube.size() << "\n");

        // lambda to find any open leaf in the subtree (explore all branches)
        std::function<CubeNode*(CubeNode*)> find_open_leaf = [&](CubeNode* node) -> CubeNode* {
            if (!node) return nullptr;
            if (node->is_leaf() && node->state == open) return node;
            for (CubeNode* child : node->children) {
                CubeNode* open_leaf = find_open_leaf(child);
                if (open_leaf) return open_leaf;
            }
            return nullptr;
        };

        CubeNode* node = current;
        
        IF_VERBOSE(1, verbose_stream() << "CubeTree: Current cube has the following children: \n");
        for (auto* child : current->children) {
            IF_VERBOSE(1, verbose_stream() << "  Child cube size: " << child->cube.size() << " State: " << to_string(child->state) << " Cube: ");
            for (auto* e : child->cube) {
                IF_VERBOSE(1, verbose_stream() << mk_bounded_pp(e, m, 3) << " ");
            }
            IF_VERBOSE(1, verbose_stream() << "\n");
        }

        while (node) {
            // check open leaf descendants
            CubeNode* nearest_open_leaf = nullptr;
            nearest_open_leaf = find_open_leaf(node); // find an open leaf descendant
            
            if (nearest_open_leaf) {
                IF_VERBOSE(1, {verbose_stream() << "CubeTree: Worker " << worker_id << " found open leaf descendant under node (which could be the node itself): ";
                    for (auto* e : node->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n  Open leaf descendant is: ";
                    for (auto* e : nearest_open_leaf->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n";
                });
                return nearest_open_leaf;
            }

            IF_VERBOSE(1, {verbose_stream() << "CubeTree: Worker " << worker_id << " found no open leaf descendants found under node: "; 
                for (auto* e : node->cube) {
                        verbose_stream() << mk_bounded_pp(e, m, 3) << " ";
                    }
                    verbose_stream() << "\n";
            });

            // DO NOT NEED TO CHECK FOR ACTIVE LEAVES bc this would only happen if we're in another thread's subtree and another thread
            // is working on some leaf. but this will NEVER HAPPEN because once we exhaust our own subtree, the problem must be UNSAT
            // bc of polarity pair tautologies!! so ONLY NEED TO CHECK FOR OPEN LEAVES

            // DO NOT NEED to check siblings and their active leaf descendants
            // since this is handled by the recusion up the tree!! 

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
                         << " state=" << to_string(node->state)
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
