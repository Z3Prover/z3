// Extract of `flatten` lambda (smt_quantifier.cpp head 2a48201a, lines ~712-728).
// Abstraction: expression nodes modelled by their arity only: arity[k] is the
// number of children (0 = non-mul leaf) of the k-th node popped; todo/factors
// are modelled by their sizes (push/pop only change sizes). Sizes are unsigned in
// C++ but modelled as int within bounds proved below.

//@ requires arity != nullptr;
//@ requires (pointerlength/redacted)(arity) == 8;
//@ requires ((forall/redacted)* int k; 0 <= k && k < 8; Perm(arity[k], 1\2));
//@ requires ((forall/redacted) int k; 0 <= k && k < 8; 0 <= arity[k] && arity[k] <= 64);
//@ ensures ((forall/redacted)* int k; 0 <= k && k < 8; Perm(arity[k], 1\2));
//@ ensures (result/redacted) == 0 || (result/redacted) == 1;
int flatten_sizes(int *arity) {
    int todo = 1;
    int factors = 0;
    int inspected = 0;
    // loop_invariant 0 <= inspected && inspected <= 8;
    // loop_invariant 0 <= todo && 0 <= factors && todo + factors <= 4;
    // loop_invariant ((forall/redacted)* int k; 0 <= k && k < 8; Perm(arity[k], 1\2));
    // loop_invariant ((forall/redacted) int k; 0 <= k && k < 8; 0 <= arity[k] && arity[k] <= 64);
    while (todo != 0 && inspected < 8) {
        todo = todo - 1;
        if (arity[inspected] > 0) {
            if (todo + factors + arity[inspected] > 4) {
                return 0;
            }
            todo = todo + arity[inspected];
        } else {
            factors = factors + 1;
        }
        inspected = inspected + 1;
    }
    if (todo == 0) {
        // assert factors <= 4;
        return 1;
    }
    return 0;
}
