/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    min_cut.cpp

Abstract:

    Test min_cut (used by Spacer's min-cut interpolating unsat cores, spacer.iuc=2).

--*/
#include "util/min_cut.h"
#include "util/debug.h"

static void tst_min_cut_reverse_arc() {
    // 0 = source, 1 = sink. The first augmenting path 0 -> 3 -> 1 needs the reverse
    // arcs 1 -> 3 and 3 -> 0; with arcs to the sink instead, the search did not terminate.
    min_cut mc;
    for (unsigned i = 0; i < 4; ++i)
        mc.new_node();
    mc.add_edge(0, 2);
    mc.add_edge(0, 3);
    mc.add_edge(2, 3);
    mc.add_edge(3, 1);
    unsigned_vector cut;
    mc.compute_min_cut(cut);
    ENSURE(cut.size() == 1 && cut[0] == 1);
}

static void tst_min_cut_two_paths() {
    // 0 -> 2 -> 1 and 0 -> 3 -> 4 -> 1 plus 2 -> 3: max flow 2.
    min_cut mc;
    for (unsigned i = 0; i < 5; ++i)
        mc.new_node();
    mc.add_edge(0, 2);
    mc.add_edge(0, 3);
    mc.add_edge(2, 1);
    mc.add_edge(2, 3);
    mc.add_edge(3, 4);
    mc.add_edge(4, 1);
    unsigned_vector cut;
    mc.compute_min_cut(cut);
    ENSURE(cut.size() == 2);
}

void tst_min_cut() {
    tst_min_cut_reverse_arc();
    tst_min_cut_two_paths();
}
