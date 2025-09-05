
#include <vector>
#include <thread>
#include <mutex>
#include <cmath>
#include <cassert>
#include <iostream>
#include <random>

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

struct atom {
    unsigned id = UINT_MAX;
    atom() {}
    atom(unsigned id) : id(id) {}
    bool operator<(atom const& other) const { return id < other.id; }
    bool operator==(atom const& other) const { return id == other.id; }    
    bool is_null() const { return id == UINT_MAX; }
};

struct literal {
    atom a;
    bool sign;
    literal(atom a, bool s = false) : a(a), sign(s) {}
    literal operator~() const { return literal(a, !sign); }
    bool operator==(literal const& other) const { return a == other.a && sign == other.sign; }
};

inline std::ostream& operator<<(std::ostream& out, literal const& l) {
    if (!l.sign)
        out << "-";
    out << l.a.id;
    return out;
}

using literal_vector = std::vector<literal>;

inline std::ostream& operator<<(std::ostream& out, literal_vector const& v) {
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
    atom atom = UINT_MAX;
    status status = status::open;

    node() {}
    node(node* parent) : parent(parent) {
    }
    node(node* parent, literal lit) : parent(parent) {
        parent->atom = lit.a;
        if (lit.sign)
            parent->left = this;
        else
            parent->right = this;
    }

    literal_vector get_cube() {
        literal_vector path;
        auto t = this;
        while (t->parent) {
            literal lit = t->parent->atom;
            if (t == t->parent->left)
                lit = ~lit;
            path.push_back(lit);
            t = t->parent;
        }
        std::reverse(path.begin(), path.end());
        return path;
    }

    void display(std::ostream& out, unsigned indent) const {
        auto t = this;
        for (unsigned i = 0; i < indent; ++i)
            out << " ";
        if (!t->atom.is_null())
            out << t->atom;
        else
            out << "leaf";
        out << (t->status == status::open ? " (o)" : t->status == status::closed ? " (c)" : " (a)");
        out << "\n";
        if (t->left)
            t->left->display(out, indent + 2);
        if (t->right)
            t->right->display(out, indent + 2);
    }

    std::ostream& display(std::ostream& out) const {
        display(out, 0);
        return out;
    }

    node* get_open() {
        if (!left && !right && status == status::open)
            return this;
        if (left) {
            auto r = left->get_open();
            if (r)
                return r;
        }
        if (right) {
            auto r = right->get_open();
            if (r)
                return r;
        }
        return nullptr;
    }


    node* get_active() {

        if (status == status::active)
            return this;

        if (left) {
            auto r = left->get_active();
            if (r)
                return r;
        }
        if (right) {
            auto r = right->get_active();
            if (r)
                return r;
        }
        return nullptr;
    }

};

class search_tree {
    node* root;
    void close_rec(node* t) {
        // if t->status == status::active, you can possibly pre-empt a worker.
        t->status = status::closed;
        if (t->left)
            close_rec(t->left);
        if (t->right)
            close_rec(t->right);
    }

    bool contains(literal_vector const& core, literal lit) const {
        for (auto c : core)
            if (lit == c)
                return true;
        return false;
    }

public:

    search_tree() {
        root = new node;
    }

    node* add_path(literal_vector const& path) {
        auto t = root;
        for (auto lit : path) {
            atom atom = lit.a;
            if (t->atom.is_null()) {
                t->atom = atom;                
            }
            assert(t->atom == atom);
            t->status = status::open;
            if (lit.sign) {
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
        }
        return t;
    }

    node* get_open() const {
        return root->get_open();
    }

    node* get_active() const {
        return root->get_active();
    }

    bool is_closed() const {
        return root->status == status::closed;
    }

    // close a branch that contains a core
    void close(literal_vector const& path, literal_vector const& core) {
        unsigned num_hit = 0;
        auto t = root;
        for (unsigned i = 0; num_hit < core.size(); ++i) {
            assert(i < path.size());
            LOG_OUT(std::cout << "close " << path << " " << core << " at " << i << " " << t->atom << "\n";);
            literal lit = path[i];
            atom atom = lit.a;
            assert(t->atom == atom);
            t = lit.sign ? t->left : t->right;            
            if (contains(core, lit))
                num_hit++;
        }
        close_rec(t);
    }

    std::ostream& display(std::ostream& out) const {
        return root->display(out);
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

    void add_atom(atom atom) {
        std::lock_guard<std::mutex> lock(mutex);
        if (!at_start)
            return;
        LOG_OUT(std::cout << "adding atom " << atom << "\n";);
        at_start = false;
        tree.add_path({ literal(atom) });
        tree.add_path({ ~literal(atom) });
        LOG_OUT(tree.display(std::cout););
        cv.notify_all();
    }

    void add_cube(literal_vector& cube, literal lit) {
        std::lock_guard<std::mutex> lock(mutex);
        literal_vector cube1(cube);
        cube1.push_back(lit);
        tree.add_path(cube1);
        cube.push_back(~lit);
        auto t = tree.add_path(cube);
        t->status = status::active;
        at_start = false;
        cv.notify_one();
        LOG_OUT(std::cout << "adding cube " << cube1 << " and " << cube << "\n";);
    }

    bool get_cube(literal_vector& cube) {
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

    void close(literal_vector const& path, literal_vector const& core) {
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
    unsigned idx = std::rand();
    random_gen(unsigned seed) : idx(seed) {}

    unsigned operator()(unsigned k) {
        return std::rand() % k;
    }
};

class worker {
    unsigned id;
    cube_manager& cm;
    random_gen m_rand;

    bool solve_cube(const literal_vector& cube) {
        // dummy implementation
        LOG_OUT(std::cout << id << " solving " << cube << "\n";);
        std::this_thread::sleep_for(std::chrono::milliseconds(50 + m_rand(100)));
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
        literal_vector cube;
        while (cm.get_cube(cube)) {
            while (true) {
                if (solve_cube(cube)) {
                    literal_vector core;
                    for (auto l : cube)
                        if (m_rand(2) == 0)
                            core.push_back(l);
                    cm.close(cube, core);
                    break;
                }
                atom atom = 1 + cube.size() + 1000 * id;
                if (cube.empty()) {
                    cm.add_atom(atom);
                    break;
                }
                literal lit(atom);
                if (m_rand(2) == 0)
                    lit = ~lit;

                cm.add_cube(cube, lit);

                LOG_OUT(std::cout << id << " getting new cube\n";);
            }
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
    parallel_cuber sp(8);
    sp.start();
    return 0;
}
