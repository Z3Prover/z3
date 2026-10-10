#include "z3++.h"
#include <cassert>
int main() {
    z3::context c;
    auto f = c.finite_field_sort("21888242871839275222246405745257275088548364400416034343698204186575808495617");
    auto x = c.constant("x", f), y = c.constant("y", f);
    z3::solver s(c, "QF_FF");
    s.add(7 * x == 3);
    s.add(y == x * x);
    s.add(x - x == 0);
    assert(s.check() == z3::sat);
    assert(s.get_model().eval(7 * x == 3).is_true());
    s.push();
    s.add(x == 0);
    assert(s.check() == z3::unsat);
    s.pop();
    assert(s.check() == z3::sat);
}
