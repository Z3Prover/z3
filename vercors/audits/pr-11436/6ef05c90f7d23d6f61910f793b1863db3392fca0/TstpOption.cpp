// Abstract extract of the "--tstp-out" branch of run() (main.cpp L591-595) and the
// post-loop guard (L620-621). argv[i][0] is modelled by first[i] (the first character,
// 0 = empty string); NativeError throw is modelled by returning -1 (error) with no mutation.
// Result encoding: *tstp_set = 1 iff options.tstp_out is non-empty.

/*@
  requires argc > 0 && 0 <= i && i < argc;
  context (pointer/redacted)(first, argc, 1\2);
  context (pointer/redacted)(tstp_set, 1, write);
  // result is the new index, or -1 for the thrown error
  ensures (result/redacted) == -1 || (result/redacted) == i + 1;
  ensures ((result/redacted) == i + 1) == (i + 1 < argc && first[i + 1] != 0);
  ensures (result/redacted) == i + 1 ==> *tstp_set == 1;
  ensures (result/redacted) == -1 ==> *tstp_set == (old/redacted)(*tstp_set);
@*/
int parse_tstp(int argc, int *first, int *tstp_set, int i) {
    int j = i + 1;
    if (j == argc)
        return -1;
    if (first[j] == 0)
        return -1;
    *tstp_set = 1;
    return j;
}

/*@
  requires interactive == 0 || interactive == 1;
  requires clause_proofs == 0 || clause_proofs == 1;
  ensures (result/redacted) == -1 || (result/redacted) == 0;
  ensures (result/redacted) == 0 ==> (tstp_set == 0 || (interactive == 0 && clause_proofs == 0));
  ensures (result/redacted) == -1 ==> (tstp_set != 0 && (interactive != 0 || clause_proofs != 0));
@*/
int post_check(int tstp_set, int interactive, int clause_proofs) {
    if (tstp_set != 0 && (interactive != 0 || clause_proofs != 0))
        return -1;
    return 0;
}

/*@
  context (pointer/redacted)(first, 2, write) ** (pointer/redacted)(flag, 1, write);
  requires *flag == 0;
  ensures (result/redacted) == 0;
@*/
int witness_ok(int *first, int *flag) {
    first[0] = 1; first[1] = 7;       // argv = {"--tstp-out", "x"}; i = 0, argc = 2
    int r = parse_tstp(2, first, flag, 0);
    // assert r == 1 && *flag == 1;
    int c = post_check(*flag, 0, 0);
    // assert c == 0;
    int e = post_check(*flag, 1, 0);
    // assert e == -1;
    return 0;
}

/*@
  context (pointer/redacted)(first, 2, write) ** (pointer/redacted)(flag, 1, write);
  requires *flag == 0;
  ensures (result/redacted) == 0;
@*/
int witness_missing(int *first, int *flag) {
    first[0] = 1; first[1] = 0;       // empty path
    int r = parse_tstp(2, first, flag, 0);
    // assert r == -1 && *flag == 0;
    return 0;
}
