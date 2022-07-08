// test driver for scoped timer.
// fixes are required to be fuzzed
// with single and multi-threaded mode and short timeouts.
// run it with app-verifier (becuzz yes ...)

#include "util/scoped_timer.h"
#include "util/util.h"
#include "util/vector.h"
#include "util/trace.h"
#include <thread>
#include <atomic>
#include <iostream>

class test_scoped_eh : public event_handler {
    std::atomic<bool> m_called = false;
public:
    void operator()(event_handler_caller_t id) override {
        m_caller_id = id;
        m_called = true;
    }
    bool called() const { return m_called; }
};

static void worker_thread(unsigned tid) {
    for (unsigned i = 0; i < 100; ++i) {
        test_scoped_eh eh;
        scoped_timer sc(1, &eh);
        unsigned_vector v;
        for (unsigned j = 0; j < (2 << 25); ++j) {
            v.push_back(j);
            if (eh.called()) {
                // IF_VERBOSE(0, verbose_stream() << tid << " " << i << " " << j << "\n");
                break;
            }
        }
    }
}

void tst_scoped_timer() {

    std::cout << "sequential test\n";
    worker_thread(0);

    std::cout << "thread test\n";
    unsigned num_threads = 3;
    vector<std::thread> threads(num_threads);
    for (unsigned i = 0; i < num_threads; ++i) 
        threads[i] = std::thread([&, i]() { worker_thread(i); });
    
    for (auto& th : threads) 
        th.join();
    
}
