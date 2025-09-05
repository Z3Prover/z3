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
        delete_leaf(root);
        root = nullptr;
    }

    bool empty() const {
        return root == nullptr;
    }

    CubeNode* get_root() { return root; } // if root is nullptr, tree is empty

    void add_children(CubeNode* parent,
                      const Cube& left_cube,
                      const Cube& right_cube) {
        CubeNode* left  = new CubeNode(left_cube, parent);
        CubeNode* right = new CubeNode(right_cube, parent);
        parent->children.push_back(left);
        parent->children.push_back(right);
    }

    // Add a new node under an existing parent
    void add_node(CubeNode* node, CubeNode* parent) {
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

    // remove node and propagate upward if parent becomes leaf
    // return pointer to last removed ancestor (or nullptr if none) so we can select one of its siblings as the next cube
    CubeNode* remove_node_and_propagate(CubeNode* node) {
        if (!node || node == root || node->children.empty()) return nullptr; // error or root or not a leaf

        CubeNode* parent = node->parent;
        CubeNode* last_removed = node;

        // erase node from parent's children
        for (size_t i = 0; i < parent->children.size(); ++i) {
            if (parent->children[i] == node) {
                delete_leaf(node);
                parent->children.erase(parent->children.begin() + i);
                break;
            }
        }

        // propagate upward if parent became leaf
        while (parent && parent != root && parent->is_leaf()) {
            SASSERT(parent->active); // parent only just became a leaf node -- no thread should be working on it! i.e. must NOT be inactive!
            CubeNode* gp = parent->parent;
            for (size_t i = 0; i < gp->children.size(); ++i) {
                if (gp->children[i] == parent) {
                    last_removed = parent;   // track the last ancestor we delete
                    delete parent;
                    gp->children.erase(gp->children.begin() + i);
                    break;
                }
            }
            parent = gp;
        }

        return last_removed;
    }

    // get closest cube to current by getting a random sibling of current (if current was UNSAT and we removed it from the tree)
    // or by descending randomly to a leaf (if we split the current node) to get the newest cube split fromthe current
    // we descend randomly to a leaf instead of just taking a random child because it's possible another thread made more descendants
    CubeNode* get_next_cube(CubeNode* current) {
        if (!current) return nullptr;

        // must be a leaf
        SASSERT(current->is_leaf());

        // lambda to find any active leaf in the subtree (explore all branches)
        std::function<CubeNode*(CubeNode*)> find_active_leaf;
        find_active_leaf = [&](CubeNode* node) -> CubeNode* {
            if (!node || !node->active) return nullptr;
            if (node->is_leaf()) return node;

            for (CubeNode* child : node->children) {
                CubeNode* leaf = find_active_leaf(child);
                if (leaf) return leaf; // return first found active leaf
            }
            return nullptr;
        };

        CubeNode* node = current;

        while (node->parent) {
            CubeNode* parent = node->parent;

            // gather active siblings
            std::vector<CubeNode*> siblings;
            for (CubeNode* s : parent->children) {
                if (s != node && s->active)
                    siblings.push_back(s);
            }

            if (!siblings.empty()) {
                // try each sibling until we find an active leaf
                for (CubeNode* sibling : siblings) {
                    CubeNode* leaf = find_active_leaf(sibling);
                    if (leaf) return leaf;
                }
            }

            // no active leaf among siblings → climb up
            node = parent;
        }

        // nothing found
        return nullptr;
    }

private:
    CubeNode* root;

    void delete_leaf(CubeNode* node) {
        if (!node || !node->active) return;

        // must be a leaf
        SASSERT(node->children.empty());

        // detach from parent
        if (node->parent) {
            auto& siblings = node->parent->children;
            for (auto it = siblings.begin(); it != siblings.end(); ++it) {
                if (*it == node) {
                    siblings.erase(it);
                    break;
                }
            }
        }

        delete node;
    }
};
