#include <z3++.h>
#include <cstring>
#include <iostream>

int main() {
    z3::context context;
    bool found = false;
    for (unsigned i = 0; i < Z3_get_num_tactics(context); ++i)
        found |= std::strcmp(Z3_get_tactic_name(context, i), "split-clause") == 0;
    if (!found) {
        std::cerr << "split-clause is not registered\n";
        return 1;
    }

    z3::expr p = context.bool_const("p");
    z3::expr q = context.bool_const("q");
    z3::goal goal(context);
    goal.add(p || q);
    z3::tactic split(context, "split-clause");
    z3::apply_result result = split(goal);
    if (result.size() != 2 ||
        result[0].size() != 1 || !z3::eq(result[0][0], p) ||
        result[1].size() != 1 || !z3::eq(result[1][0], q)) {
        std::cerr << "split-clause did not produce the expected subgoals\n";
        return 1;
    }

    z3::solver solver(context);
    z3::expr value = context.bool_const("value");
    solver.add(value);
    return solver.check() == z3::sat ? 0 : 1;
}
