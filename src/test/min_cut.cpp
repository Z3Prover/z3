#include "util/min_cut.h"
#include "util/debug.h"

static void tst_bottleneck() {
    min_cut graph;
    unsigned a = graph.new_node();
    graph.add_edge(0, a, 2);
    graph.add_edge(a, 1);

    unsigned_vector cut;
    graph.compute_min_cut(cut);
    ENSURE(cut.size() == 1);
    ENSURE(cut[0] == 1);
}

static void tst_reverse_path() {
    min_cut graph;
    unsigned a = graph.new_node();
    unsigned b = graph.new_node();
    unsigned c = graph.new_node();
    unsigned d = graph.new_node();
    graph.add_edge(0, a);
    graph.add_edge(0, b);
    graph.add_edge(a, c);
    graph.add_edge(a, d);
    graph.add_edge(b, c);
    graph.add_edge(c, 1);
    graph.add_edge(d, 1);

    // After augmenting 0 -> a -> c -> 1, reroute through c -> a.
    unsigned_vector cut;
    graph.compute_min_cut(cut);
    ENSURE(cut.size() == 2);
    ENSURE(cut.contains(a));
    ENSURE(cut.contains(b));
}

void tst_min_cut() {
    tst_bottleneck();
    tst_reverse_path();
}
