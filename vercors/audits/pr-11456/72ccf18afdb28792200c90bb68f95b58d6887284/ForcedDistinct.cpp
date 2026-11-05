// Extract of theory_finite_set::are_forced_distinct (PR head 72ccf18a, src/smt/theory_finite_set.cpp lines 301-338).
// Abstraction: relevant `in` parents of a / b with arg1 root == a / b are arrays of
// (element-root id, value: 0=false, 1=true, 2=undef). obj_map lookup is modeled by scanning a's list.
/*@
requires na >= 0 && nb >= 0;
requires (pointer/redacted)(ak, na, read) ** (pointer/redacted)(av, na, read) ** (pointer/redacted)(bk, nb, read) ** (pointer/redacted)(bv, nb, read);
ensures (pointer/redacted)(ak, na, read) ** (pointer/redacted)(av, na, read) ** (pointer/redacted)(bk, nb, read) ** (pointer/redacted)(bv, nb, read);
ensures (result/redacted) ==> ((bEmpty && ((exists/redacted) int i; 0 <= i && i < na; av[i] == 1))
  || (aEmpty && ((exists/redacted) int j; 0 <= j && j < nb; bv[j] == 1))
  || ((exists/redacted) int i; 0 <= i && i < na; ((exists/redacted) int j; 0 <= j && j < nb; ak[i] == bk[j] && av[i] != 2 && bv[j] != 2 && av[i] != bv[j])));
@*/
bool forced_distinct(bool aEmpty, bool bEmpty, int* ak, int* av, int na, int* bk, int* bv, int nb) {
    /*@
    loop_invariant 0 <= i && i <= na;
    loop_invariant (pointer/redacted)(ak, na, read) ** (pointer/redacted)(av, na, read);
    loop_invariant ((forall/redacted) int q; 0 <= q && q < i; !(bEmpty && av[q] == 1));
    @*/
    for (int i = 0; i < na; i++) {
        if (av[i] == 2) continue;
        if (bEmpty && av[i] == 1) return true;
    }
    /*@
    loop_invariant 0 <= j && j <= nb;
    loop_invariant (pointer/redacted)(ak, na, read) ** (pointer/redacted)(av, na, read) ** (pointer/redacted)(bk, nb, read) ** (pointer/redacted)(bv, nb, read);
    loop_invariant ((forall/redacted) int q; 0 <= q && q < j; !(aEmpty && bv[q] == 1));
    loop_invariant ((forall/redacted) int q; 0 <= q && q < j; ((forall/redacted) int i; 0 <= i && i < na; !(ak[i] == bk[q] && av[i] != 2 && bv[q] != 2 && av[i] != bv[q])));
    @*/
    for (int j = 0; j < nb; j++) {
        if (bv[j] == 2) continue;
        if (aEmpty && bv[j] == 1) return true;
        /*@
        loop_invariant 0 <= i && i <= na;
        loop_invariant (pointer/redacted)(ak, na, read) ** (pointer/redacted)(av, na, read) ** (pointer/redacted)(bk, nb, read) ** (pointer/redacted)(bv, nb, read);
        loop_invariant 0 <= j && j < nb && bv[j] != 2;
        loop_invariant ((forall/redacted) int q; 0 <= q && q < i; !(ak[q] == bk[j] && av[q] != 2 && av[q] != bv[j]));
        @*/
        for (int i = 0; i < na; i++) {
            if (ak[i] == bk[j] && av[i] != 2 && av[i] != bv[j]) return true;
        }
    }
    return false;
}
