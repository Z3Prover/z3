## F* audit PR #11702 (head 63737fe7, base 1a1d88dd)
File: src/opt/opt_context.cpp. Fetched at those SHAs via contents API; sha256 head 3d777ad0c313bea3f034ac932ce994e7da1e6425ab59df8ea4824920f27f835c, base 77bbfc703846afb915aa0b9c9c71308ff98bba50b6d8534514cb2d9a1a65bbf9 (decoded contents). Head lines ~1746-1769 (is_cardinality/is_lower_bound/is_upper_bound), 2322-2330, 2342-2350.
Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend), z3rlimit 10.

### Obligations
1. (proved) Old lower-bound predicate == new is_le && x==term && is_cardinality(y): same boolean result and same (max,min) cardinality update, for all inputs (lemma equiv).
2. (proved) Same for upper bound (identical guard structure with is_ge; the model is parametric in the shape flag).
3. (proved) Accepted cases only widen max/min cardinality (lemma monotone).

### Correspondence
Booleans model: shape match, x==term, mark.is_marked(y), is_zero_one(y), a.is_add(y), all_of(args,is_zero_one); n=num_args. The C++ short-circuit order is preserved; the old code also tested guards in the same order. Side-effects of is_zero_one on captured n/cnd/th/el are not modelled (is_zero_one is called once per predicate in both versions, same order).

### Not mechanized / manually reviewed
- get_lower_value / get_upper_value (O_MAXSMT): the m_maxsmts.find(obj.m_id) lookup is hoisted into a const reference `ms`, calling the same getters with the same negate selection. Lookup is a pure map find and getters are const; equivalent by inspection. Not formalized (excluded). Assumes the key exists, as before (deref of find result unchanged).
- C++ execution, memory safety, AST plumbing, rest of is_min_max_of_sums.

### Assumptions
F* standard library only; no admit/assume; no base modules imported.

### Reproduce
bash run.sh (see verification log). Semantic model proof, not verification of C++.