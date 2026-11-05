// Extract of prove_unbounded backward-difference loop (opt_curve_certificate.cpp, head 23c9024, lines ~139-151).
// Abstractions: rational -> int; vector(vector<rational)> values -> flat array v[i*k+c];
// binomial update (exact in rational source) is abstracted to a bounded int step: binomial in [0,3].
// Rational arithmetic is arbitrary precision in the source; int overflow is excluded by explicit bounds.

/*@
requires 1 <= k && k <= 8 && 1 <= m && m <= 4;
requires 0 <= j && j < m;
requires (pointer/redacted)(v, m*k, read) ** (pointer/redacted)(row, k, write);
requires ((forall/redacted) int q; 0 <= q && q < m*k ==> -100 <= v[q] && v[q] <= 100);
ensures (pointer/redacted)(v, m*k, read) ** (pointer/redacted)(row, k, write);
ensures ((forall/redacted) int c; 0 <= c && c < k ==> -300*(j+1) <= row[c] && row[c] <= 300*(j+1));
@*/
void diff_row(int* v, int* row, int k, int m, int j, int b0, int b1, int b2, int b3) {
    /*@
    loop_invariant 0 <= c0 && c0 <= k; loop_invariant (pointer/redacted)(row, k, write);
    loop_invariant ((forall/redacted) int q; 0 <= q && q < c0 ==> row[q] == 0);
    @*/
    for (int c0 = 0; c0 < k; ++c0) row[c0] = 0;
    int binomial = 1;
    /*@
    loop_invariant 0 <= i && i <= j + 1;
    loop_invariant (pointer/redacted)(v, m*k, read) ** (pointer/redacted)(row, k, write);
    loop_invariant ((forall/redacted) int q; 0 <= q && q < m*k ==> -100 <= v[q] && v[q] <= 100);
    loop_invariant 0 <= binomial && binomial <= 3;
    loop_invariant ((forall/redacted) int c; 0 <= c && c < k ==> -300*i <= row[c] && row[c] <= 300*i);
    @*/
    for (int i = 0; i <= j; ++i) {
        int sign = (i % 2 == 0) ? 1 : -1;
        /*@
        loop_invariant 0 <= c && c <= k;
        loop_invariant (pointer/redacted)(v, m*k, read) ** (pointer/redacted)(row, k, write);
        loop_invariant ((forall/redacted) int q; 0 <= q && q < m*k ==> -100 <= v[q] && v[q] <= 100);
        loop_invariant ((forall/redacted) int d; 0 <= d && d < k ==> -300*i - (d < c ? 300 : 0) <= row[d] && row[d] <= 300*i + (d < c ? 300 : 0));
        @*/
        for (int c = 0; c < k; ++c)
            row[c] += sign * binomial * v[i * k + c];
        // abstracted exact rational update binomial*(j-i)/(i+1), bounded 0..3
        binomial = (i == 0) ? 1 : (b0 >= 0 && b0 <= 3 ? b0 : 0);
    }
}

int main() {
    int v[4]; int row[2];
    v[0]=1; v[1]=2; v[2]=3; v[3]=4;
    diff_row(v, row, 2, 2, 1, 0,0,0,0);
    return 0;
}
