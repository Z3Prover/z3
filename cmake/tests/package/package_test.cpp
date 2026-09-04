#include <z3++.h>

int main() {
    z3::context context;
    z3::solver solver(context);
    z3::expr value = context.bool_const("value");
    solver.add(value);
    return solver.check() == z3::sat ? 0 : 1;
}
