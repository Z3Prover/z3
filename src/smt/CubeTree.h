#include "ast/ast_translation.h"

#include <vector>
#include <cstdlib>   // rand()
#include <ctime>

// forward declare
struct CubeNode;

typedef expr_ref_vector Cube;  // shorthand

struct CubeNode {
    Cube cube;
    CubeNode* parent;
    std::vector<CubeNode*> children;
    bool active = true;

    CubeNode(const Cube& c, CubeNode* p = 0) 
        : cube(c), parent(p) {}

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

    void add_children(CubeNode* parent,
                      const Cube& left_cube,
                      const Cube& right_cube) {
        IF_VERBOSE(1, verbose_stream() << "CubeTree: adding children of sizes " << left_cube.size() << " and " << right_cube.size() << " under parent of size " << (parent ? parent->cube.size() : 0) << "\n");
        CubeNode* left  = new CubeNode(left_cube, parent);
        CubeNode* right = new CubeNode(right_cube, parent);
        parent->children.push_back(left);
        parent->children.push_back(right);
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

    // mark node as inactive and propagate upward if parent becomes a leaf (all children inactive)
    // return pointer to last affected ancestor (or nullptr if none) so we can select one of its siblings as the next cube
    CubeNode* remove_node_and_propagate(CubeNode* node) {
        if (!node || node == root || !node->is_leaf()) return nullptr; // error, root, or not a leaf

        CubeNode* parent = node->parent;
        CubeNode* last_marked = node;

        // mark this node as inactive
        node->active = false;

        // propagate upward if parent became a "leaf" (all children inactive)
        while (parent && parent != root) {
            bool all_inactive = true;
            for (CubeNode* child : parent->children) {
                if (child->active) {
                    all_inactive = false;
                    break;
                }
            }

            if (!all_inactive) break;  // stop propagating

            SASSERT(parent->active); // parent must not be currently worked on
            last_marked = parent;     // track the last ancestor we mark
            parent->active = false;   // mark parent inactive
            parent = parent->parent;
        }

        return last_marked;
    }



    // get closest cube to current by getting a random sibling of current (if current was UNSAT and we removed it from the tree)
    // or by descending randomly to a leaf (if we split the current node) to get the newest cube split fromthe current
    // we descend randomly to a leaf instead of just taking a random child because it's possible another thread made more descendants
    CubeNode* get_next_cube(CubeNode* current) {

        IF_VERBOSE(1, verbose_stream() << "CubeTree: current cube is null: " << (current == nullptr) << "\n");
        if (!current) return nullptr;

        IF_VERBOSE(1, verbose_stream() << "CubeTree: getting next cube from current of size " << current->cube.size() << "\n");

        // lambda to find any active leaf in the subtree (explore all branches)
        std::function<CubeNode*(CubeNode*)> find_active_leaf = [&](CubeNode* node) -> CubeNode* {
            if (!node || !node->active) return nullptr;
            if (node->is_leaf()) return node;
            for (CubeNode* child : node->children) {
                CubeNode* leaf = find_active_leaf(child);
                if (leaf) return leaf;
            }
            return nullptr;
        };

        CubeNode* node = current;

        while (node) {
            // 1. check if current node itself is active leaf
            if (node->active && node->is_leaf()) return node;

            // 2. check active leaf descendants
            CubeNode* leaf_descendant = nullptr;
            for (CubeNode* child : node->children) {
                leaf_descendant = find_active_leaf(child);
                if (leaf_descendant) return leaf_descendant;
            }

            // 3 & 4. check siblings and their active leaf descendants
            if (node->parent) {
                CubeNode* parent = node->parent;
                for (CubeNode* sibling : parent->children) {
                    if (sibling == node) continue;

                    // check if sibling itself is an active leaf
                    if (sibling->active && sibling->is_leaf()) return sibling;

                    // check for active leaf descendants of sibling
                    CubeNode* leaf_in_sibling = find_active_leaf(sibling);
                    if (leaf_in_sibling) return leaf_in_sibling;
                }
            }

            // 5. climb up to parent
            node = node->parent;
        }

        IF_VERBOSE(1, verbose_stream() << "CubeTree: no active cube found\n");
        return nullptr;
    }

private:
    CubeNode* root;

    // mark leaf as inactive instead of deleting it
    void mark_leaf_inactive(CubeNode* node) {
        if (!node || !node->active) return;

        // must be a leaf
        SASSERT(node->children.empty());

        // just mark inactive
        node->active = false;
    }

    void delete_subtree(CubeNode* node) {
        if (!node) return;
        for (CubeNode* child : node->children) {
            delete_subtree(child);
        }
        delete node;
    }
};
