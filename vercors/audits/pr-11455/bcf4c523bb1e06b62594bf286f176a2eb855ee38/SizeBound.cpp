// Abstraction: sort_size{kind,size} passed by value; emitted flag and bound
// returned as two pure functions mirroring `if (domain_size.is_finite()) add bound size()`.
// kind 0 = SS_FINITE, 1 = VERY_BIG, 2 = INFINITE. size is int (not uint64).
/*@
  ensures (result/redacted) == (kind == 0);
@*/
bool emitted(int kind) {
    bool r = false;
    if (kind == 0) {
        r = true;
    }
    return r;
}

/*@
  requires kind == 0 ==> size >= 0;
  ensures kind == 0 ==> (result/redacted) == size;
@*/
int bound_value(int kind, int size) {
    int b = -1;
    if (kind == 0) {
        b = size;
    }
    return b;
}
