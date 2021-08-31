
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "sat/sat_solver.h"
#include "util/util.h"

typedef sat::literal_vector clause_t;
typedef vector<clause_t> clauses_t;
typedef vector<clauses_t> trail_t;

// [ [c1, c2, ..], [ ...] ]

static unsigned s_num_vars = 6;
static unsigned s_num_clauses_per_frame = 8;
static unsigned s_num_frames = 7;

static void add_literal(random_gen& r, clause_t& c) {
    c.push_back(sat::literal(r(s_num_vars) + 1, r(2) == 0));
}

static clause_t& last_clause(trail_t& t) {
    return t.back().back();
}

static void add_clause(sat::solver& s, random_gen& r, trail_t& t) {
    t.back().push_back(sat::literal_vector());
    clause_t& cls = last_clause(t);
    for (unsigned i = 0; i < 3; ++i) {
        add_literal(r, cls);
    }
    s.mk_clause(cls.size(), cls.data());
}

static void pop_user_scope(sat::solver& s, trail_t& t) {
    std::cout << "pop\n";
    s.user_pop(1);
    t.pop_back();
}

static void push_user_scope(sat::solver& s, trail_t& t) {
    std::cout << "push\n";
    s.user_push();
    t.push_back(clauses_t());
}

static void init_vars(sat::solver& s) {
    for (unsigned i = 0; i <= s_num_vars; ++i) {
        s.mk_var();
    }
}

static void check_coherence(sat::solver& s1, trail_t& t) {
    params_ref p;
    reslimit rlim;
    sat::solver s2(p, rlim);
    init_vars(s2);
    sat::literal_vector cls;
    for (unsigned i = 0; i < t.size(); ++i) {
        clauses_t& clss = t[i];
        for (unsigned j = 0; j < clss.size(); ++j) {
            cls.reset();
            cls.append(clss[j]);
            s2.mk_clause(cls.size(), cls.data());
        }
    }
    lbool is_sat1 = s1.check();
    lbool is_sat2 = s2.check();
    if (is_sat1 != is_sat2) {
        s1.display(std::cout);
        s2.display(std::cout);
    }
    std::cout << is_sat1 << "\n";
    ENSURE(is_sat1 == is_sat2);
}

void tst_sat_user_scope() {
    random_gen r(0);
    trail_t trail;
    params_ref p;
    reslimit rlim;
    sat::solver s(p, rlim);  // incremental solver
    init_vars(s);
    while (true) {
        for (unsigned i = 0; i < s_num_frames; ++i) {
            // push 3 frames, pop 2
            for (unsigned k = 0; k < 3; ++k) {
                push_user_scope(s, trail);
                for (unsigned j = 0; j < s_num_clauses_per_frame; ++j) {
                    add_clause(s, r, trail);
                }
                check_coherence(s, trail);
            }
            for (unsigned k = 0; k < 2; ++k) {
                pop_user_scope(s, trail);
                check_coherence(s, trail);
            }
        }
        for (unsigned i = 0; i < s_num_frames; ++i) {
            pop_user_scope(s, trail);
            check_coherence(s, trail);
        }
    }
}
