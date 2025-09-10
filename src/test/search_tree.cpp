#include "util/search_tree.h"
#include "util/trace.h"
#include <thread>
#include <mutex>
#include <cmath>
#include <iostream>
#include <condition_variable>


// Initially there are no cubes.
// workers that enter at this stage will receive an empty cube to work on.
// If they succeeed, they return the empty conflict.
// If they fail, they generate two cubes, one with +id and one with -id
// and add them to the cube manager.

struct literal {
    using atom = unsigned;
    atom a;
    bool sign;
    literal(atom a, bool s = false) : a(a), sign(s) {}
    literal operator~() const { return literal(a, !sign); }
    bool operator==(literal const& other) const { return a == other.a && sign == other.sign; }
};

inline std::ostream& operator<<(std::ostream& out, literal lit) {
    if (lit.a == UINT_MAX) {
        out << "null";
        return out;
    }
    if (!lit.sign)
        out << "-";
    out << lit.a;
    return out;
}

struct literal_config {
    using literal = literal;
    static bool literal_is_null(literal const& l) { return l.a == UINT_MAX; }
    static literal null_literal() { return literal(UINT_MAX); }
    static std::ostream& display_literal(std::ostream& out, literal l) { return out << l; }
};


using literal_vector = vector<literal>;

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


class cube_manager {
    using node = search_tree::node<literal_config>;
    using status = search_tree::status;
    using literal = typename literal_config::literal;
    std::mutex mutex;
    std::condition_variable cv;
    search_tree::tree<literal_config> tree;
    unsigned num_workers = 0;
    std::atomic<unsigned> num_waiting = 0;
public:
    cube_manager(unsigned num_workers) : num_workers(num_workers), tree(literal_config::null_literal()) {}
    ~cube_manager() {}

    void split(node* n, literal a, literal b) {
        std::lock_guard<std::mutex> lock(mutex);
        IF_VERBOSE(1, verbose_stream() << "adding literal " << a << " and " << b << "\n";);
        tree.split(n, a, b);
        IF_VERBOSE(1, tree.display(verbose_stream()););
        cv.notify_all();
    }

    bool get_cube(node*& n, literal_vector& cube) {
        cube.reset();
        std::unique_lock<std::mutex> lock(mutex);
        node* t = nullptr;
        while ((t = tree.activate_node(n)) == nullptr) {
            // if all threads have reported they are done, then return false
            // otherwise wait for condition variable
            IF_VERBOSE(1, verbose_stream() << "waiting... " << "\n";);
            if (tree.is_closed()) {
                IF_VERBOSE(1, verbose_stream() << "all done\n";);
                cv.notify_all();
                return false;
            }
            cv.wait(lock);
        }
        n = t;
        while (t) {
            if (literal_config::literal_is_null(t->get_literal()))
                break;
            cube.push_back(t->get_literal());
            t = t->parent();
        }
//        IF_VERBOSE(1, verbose_stream() << "got cube " << cube << " from " << " " << t->get_status() << "\n";);
        return true;
    }

    void backtrack(node* n, literal_vector const& core) {
        std::lock_guard<std::mutex> lock(mutex);
        IF_VERBOSE(1, verbose_stream() << "backtrack " << core << "\n"; tree.display(verbose_stream()););
        tree.backtrack(n, core);
        if (tree.is_closed()) {
            IF_VERBOSE(1, verbose_stream() << "all done\n";);
            cv.notify_all();
        }
    }

};
class worker {
    unsigned id;
    cube_manager& cm;
    random_gen m_rand;

    bool solve_cube(const literal_vector& cube) {
        // dummy implementation
        IF_VERBOSE(0, verbose_stream() << id << " solving " << cube << "\n";);
        std::this_thread::sleep_for(std::chrono::milliseconds(50 + m_rand(100)));
        // the deeper the cube, the more likely we are to succeed.
        // 1 - (9/10)^(|cube|) success probability
        if (cube.empty())
            return false;
        double prob = m_rand(100);
        double threshold = 100.0 * (1.0 - std::pow(9.0 / 10.0, cube.size()));
        bool solved = prob < threshold;
        IF_VERBOSE(0, verbose_stream() << id << (solved ? " solved " : " failed ") << cube << " " << prob << " " << threshold << "\n";);
        return solved;
    }

public:
    worker(unsigned id, cube_manager& cm) : id(id), cm(cm), m_rand(id) {
        m_rand.set_seed(rand()); // make it random across runs
    }
    ~worker() {}
    void run() {
        literal_vector cube;
        search_tree::node<literal_config>* n = nullptr;
        while (cm.get_cube(n, cube)) {
            if (solve_cube(cube)) {
                literal_vector core;
                for (auto l : cube)
                    if (m_rand(2) == 0)
                        core.push_back(l);
                cm.backtrack(n, core);
            }
            else {
                unsigned atom = 1 + cube.size() + 1000 * id;
                literal lit(atom);
                cm.split(n, lit, ~lit);
                IF_VERBOSE(1, verbose_stream() << id << " getting new cube\n";);
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


void tst_search_tree() {
    parallel_cuber sp(8);
    sp.start();
}