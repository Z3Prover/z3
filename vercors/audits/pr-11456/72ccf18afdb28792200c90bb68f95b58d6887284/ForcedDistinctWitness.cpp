// Non-vacuity: concrete state satisfying preconditions; a={x1:true}, b={x1:false}, expected forced-distinct.
//@ requires true;
int main() {
    int ak[1] = {7}; int av[1] = {1}; int bk[1] = {7}; int bv[1] = {0};
    // assert ak[0] == bk[0] && av[0] != bv[0];
    return 0;
}
