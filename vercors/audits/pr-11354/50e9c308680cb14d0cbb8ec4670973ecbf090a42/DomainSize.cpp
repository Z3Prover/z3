// Extract of the domain-size loop of check_array_map_coherence
// (src/ast/rewriter/array_map_coherence.h, head 50e9c308).
// sz[i], finite[i], uninterp[i] abstract domain sort i of the array sort:
//   sz[i] = size.size(), finite[i] = size.is_finite(), uninterp[i] = m.is_uninterp(domain).
// WIDTH-REDUCED: source uses uint64_t for domain_size/size.size(); VerCors cpp lacks 64-bit types, so 32-bit unsigned int is used. n = indices.size() (32-bit in source).
// Source evaluates `size` only after the uninterp check, as here.

//@ context (pointer/redacted)(sz, arity, read) ** (pointer/redacted)(finite, arity, read) ** (pointer/redacted)(uninterp, arity, read);
//@ context (pointer/redacted)(out, 1, write);
//@ requires 0 <= arity && arity <= 1000;
//@ requires 0 <= n && n < 4294967296;
//@ requires ((forall/redacted) int i; 0 <= i && i < arity; sz[i] >= 1 && sz[i] <= 4294967295);
//@ ensures (result/redacted) == 0 || (result/redacted) == 1;
//@ ensures *out >= 1;
//@ ensures *out <= n || *out == 1;
int domain_fits(unsigned int* sz, int* finite, int* uninterp, int arity, unsigned int n, unsigned int* out) {
    unsigned int domain_size = 1;
    int exceeds = 0;
    // loop_invariant (pointer/redacted)(sz, arity, read) ** (pointer/redacted)(finite, arity, read) ** (pointer/redacted)(uninterp, arity, read);
    // loop_invariant 0 <= i && i <= arity;
    // loop_invariant ((forall/redacted) int j; 0 <= j && j < arity; sz[j] >= 1);
    // loop_invariant exceeds == 0 || exceeds == 1;
    // loop_invariant domain_size >= 1;
    // loop_invariant domain_size <= n || domain_size == 1;
    // loop_invariant ((forall/redacted) int j; 0 <= j && j < i; uninterp[j] != 0 || (finite[j] != 0 && sz[j] <= n));
    for (int i = 0; i < arity; ++i) {
        if (uninterp[i] != 0) {
            continue;
        }
        unsigned int size = sz[i];
        if (finite[i] == 0 || size > n || domain_size > n / size) {
            exceeds = 1;
            break;
        }
        // assert domain_size * size <= n;
        // assert domain_size * size >= 1;
        domain_size *= size;
    }
    *out = domain_size;
    return exceeds;
}

