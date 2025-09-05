
#include <vector>
#include <thread>
#include <mutex>
#include <cmath>
#include <cassert>
#include <iostream>

using unsigned_vector = std::vector<unsigned>;

std::mutex cout_mutex;
// Initially there are no cubes.
// workers that enter at this stage will receive an empty cube to work on.
// If they succeeed, they return the empty conflict.
// If they fail, they generate two cubes, one with +id and one with -id
// and add them to the cube manager.

#define LOG_OUT(_out_) { \
    std::lock_guard<std::mutex> lock(cout_mutex); \
    _out_   \
}

inline std::ostream& operator<<(std::ostream& out, std::vector<int> const& v) {
    out << "[";
    for (unsigned i = 0; i < v.size(); ++i) {
        if (i > 0)
            out << " ";
        out << v[i];
    }
    out << "]";
    return out;
}

enum status {
    open,
    closed,
    active
};

struct node {
    node* left = nullptr;
    node* right = nullptr;
    node* parent = nullptr;
    unsigned atom = UINT_MAX;
    status status = status::open;

    node() {}
    node(node* parent) : parent(parent) {
    }
    node(node* parent, int lit) : parent(parent) {
        parent->atom = std::abs(lit);        
        if (lit < 0)
            parent->left = this;
        else
            parent->right = this;
    }

    std::vector<int> get_cube() {
        std::vector<int> path;
        auto t = this;
        while (t->parent) {
            int lit = t->parent->atom;
            if (t == t->parent->left)
                lit = -lit;
            path.push_back(lit);
            t = t->parent;
        }
        std::reverse(path.begin(), path.end());
        return path;
    }
};

class search_tree {
    node* root;
    void close_rec(node* t) {
        t->status = status::closed;
        if (t->left)
            close_rec(t->left);
        if (t->right)
            close_rec(t->right);
    }

    bool contains(std::vector<int> const& core, int lit) const {
        for (auto c : core)
            if (lit == c)
                return true;
        return false;
    }

    void display_rec(std::ostream& out, node* t, unsigned indent) const {
        for (unsigned i = 0; i < indent; ++i)
            out << " ";
        if (t->atom != UINT_MAX)
            out << t->atom;
        else
            out << "leaf";
        out << (t->status == status::open ? " (o)" : t->status == status::closed ? " (c)" : " (a)");
        out << "\n";
        if (t->left)
            display_rec(out, t->left, indent + 2);
        if (t->right)
            display_rec(out, t->right, indent + 2);
    }

    node* get_open_rec(node* t) const {
        if (!t->left && !t->right && t->status == status::open) 
            return t;
        
        if (t->left) {
            auto r = get_open_rec(t->left);
            if (r)
                return r;
        }
        if (t->right) {
            auto r = get_open_rec(t->right);
            if (r)
                return r;
        }
        return nullptr;
    }

    node* get_active_rec(node* t) const {
        if (t->status == status::active) 
            return t;
        
        if (t->left) {
            auto r = get_active_rec(t->left);
            if (r)
                return r;
        }
        if (t->right) {
            auto r = get_active_rec(t->right);
            if (r)
                return r;
        }
        return nullptr;
    }

public:

    search_tree() {
        root = new node;
    }

    node* add_path(std::vector<int> const& path) {
        auto t = root;
        unsigned i = 0;
        while (i < path.size()) {
            int lit = path[i];
            unsigned atom = std::abs(lit);
            bool sign = lit < 0;
            if (t->atom == UINT_MAX) {
                t->atom = atom;
                t->status = status::open;
            }
            assert(t->atom == atom);
            if (sign) {
                if (!t->left) 
                    t = new node(t, lit);                
                else 
                    t = t->left;
            }
            else {
                if (!t->right) 
                    t = new node(t, lit);
                else 
                    t = t->right;
            }
            i++;
        }
        t->status = status::open;
        return t;
    }

    node* get_open() const {
        return get_open_rec(root);
    }

    node* get_active() const {
        return get_active_rec(root);
    }

    bool is_closed() const {
        return root->status == status::closed;
    }

    // close a branch that contains a core
    void close(std::vector<int> const& path, std::vector<int> const& core) {
        unsigned num_hit = 0;
        unsigned i = 0;
        auto t = root;
        while (num_hit < core.size()) {
            LOG_OUT(std::cout << "close " << path << " " << core << " at " << i << " " << t->atom << "\n";);
            int lit = path[i];
            unsigned atom = std::abs(lit);
            bool sign = lit < 0;
            auto next_t = sign ? t->left : t->right;
            if (!next_t)
                break; 
            assert(t->atom == atom);
            t = next_t;
            if (contains(core, lit))
                num_hit++;
            ++i;
        }        
        close_rec(t);
    }

    std::ostream& display(std::ostream& out) const {
        display_rec(out, root, 0);
        return out;
    }

};

class cube_manager {
    std::mutex mutex;
    std::condition_variable cv;
    search_tree tree;
    std::atomic<bool> at_start = true;
    unsigned num_workers = 0;
    std::atomic<unsigned> num_waiting = 0;
public:
    cube_manager(unsigned num_workers) : num_workers(num_workers) {}
    ~cube_manager() {}

    void add_atom(int atom) {
        std::lock_guard<std::mutex> lock(mutex);
        if (!at_start)
            return;
        LOG_OUT(std::cout << "adding atom " << atom << "\n";);
        at_start = false;        
        tree.add_path({atom});
        tree.add_path({ -atom });        
        LOG_OUT(tree.display(std::cout););
        cv.notify_all();
    }

    void add_cube(std::vector<int>& cube, int atom) {
        std::lock_guard<std::mutex> lock(mutex);
        std::vector<int> cube1(cube);
        cube1.push_back(atom);
        tree.add_path(cube1);
        cube.push_back(-atom);
        auto t = tree.add_path(cube);
        t->status = status::active;
        at_start = false;
        cv.notify_one();
        LOG_OUT(std::cout << "adding cube " << cube1 << " and " << cube << "\n";);
    }

    bool get_cube(std::vector<int>& cube) {
        std::unique_lock<std::mutex> lock(mutex);
        if (at_start) {
            cube.clear();
            return true;
        }
        node* t = nullptr;
        while ((t = tree.get_open()) == nullptr) {
            // if all threads have reported they are done, then return false
            // otherwise wait for condition variable.
            LOG_OUT(std::cout << "waiting... " << tree.get_active() << "\n";);
            if (!tree.get_active()) {
                LOG_OUT(std::cout << "all done\n";);
                cv.notify_all();
                return false;
            }
            cv.wait(lock);            
        }        
        cube = t->get_cube();
        LOG_OUT(std::cout << "got cube " << cube << " from " << t << " " << t->status << "\n";);
        t->status = status::active;
        return true;
    }

    void close(std::vector<int> const& path, std::vector<int> const& core) {
        std::lock_guard<std::mutex> lock(mutex);
        tree.close(path, core);
        LOG_OUT(std::cout << "closing "; tree.display(std::cout););
        if (tree.is_closed()) {
            LOG_OUT(std::cout << "all done\n";);
            cv.notify_all();
        }
    }

};

struct random_gen {
    unsigned idx = 0;
    random_gen(unsigned seed) : idx(seed) {}

    unsigned operator()(unsigned k) {
        idx += (idx + 1) * (idx << 3 + 2);
        return idx % k;
    }
};

class worker {
    unsigned id;
    cube_manager& cm;
    random_gen m_rand;

    bool solve_cube(const std::vector<int>& cube) {
        // dummy implementation
        LOG_OUT(std::cout << id << " solving " << cube << "\n";);
        std::this_thread::sleep_for(std::chrono::milliseconds(100 + m_rand(1000)));
        // the deeper the cube, the more likely we are to succeed.
        // 1 - (9/10)^(|cube|) success probability
        if (cube.empty())
            return false;
        double prob = m_rand(100);
        double threshold = 100.0 * (1.0 - std::pow(9.0 / 10.0, cube.size()));
        bool solved = prob < threshold;
        LOG_OUT(std::cout << id << (solved ? " solved " : " failed ") << cube << " " << prob << " " << threshold << "\n";);
        return solved;
    }

public:
    worker(unsigned id, cube_manager& cm) : id(id), cm(cm), m_rand(id) {}
    ~worker() {}
    void run() {
        std::vector<int> cube;
        while (cm.get_cube(cube)) {
            while (true) {
                if (solve_cube(cube)) {
                    std::vector<int> core;
                    for (auto l : cube)
                        if (m_rand(2) == 0)
                            core.push_back(l);
                    cm.close(cube, core);
                    break;
                }
                int atom = 1 + cube.size() + 1000 * id;
                if (cube.empty()) {
                    cm.add_atom(atom);
                    break;
                }
                if (m_rand(2) == 0)
                    atom = -atom;
                cm.add_cube(cube, atom);
            }
            LOG_OUT(std::cout << id << " getting new cube\n";);
        }
    }
};



class parallel_cuber {
    unsigned num_workers;
    std::vector<worker*> workers;
    cube_manager cm;
public:
    parallel_cuber(unsigned num_workers) : 
        num_workers(num_workers),
        cm(num_workers) {
    }
    ~parallel_cuber() {}

    void start() {
        for (unsigned i = 0; i < num_workers; ++i) 
            workers.push_back(new worker(i, cm));        
        std::vector<std::thread> threads;
        for (auto w : workers)
            threads.push_back(std::thread([w]() { w->run(); }));
        for (auto& t : threads)
            t.join();
        for (auto w : workers)
            delete w;
    }
};

int main() {
    parallel_cuber sp(3);
    sp.start();
    return 0;
}
