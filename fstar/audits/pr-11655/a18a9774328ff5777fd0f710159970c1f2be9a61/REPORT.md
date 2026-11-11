# F* audit of PR #11655 @ a18a9774328ff5777fd0f710159970c1f2be9a61 (base 145c0c51570a357cc558ce898ce77573ba9d4fbf)

Source: src/util/id_var_list.h at head (sha256 f64196ed33e474431493ae4bfdd53bdb3403efa23c654e0a9d2d9495e21bb76a), fields lines 28-30, set_var/get_var 49-51/162-164, replace 107-118.

## Obligations (3 of max 3)
1. O1 (base behaviour, witness): with the old `int m_var:24`, storing 2^23 reads back -2^23 and INT_MAX reads back -1 (two's-complement wrap, the behaviour of gcc/clang/MSVC; implementation-defined in C++). PROVED in F* as a model of the *pre-PR* code, confirming the bug the PR fixes. Not a defect of the PR head.
2. O2 (head): storing any int32 in a full-width `int` field round-trips, including 2^23-1, 2^23, 2^23+1, INT_MAX. PROVED.
3. O3 (head): replace(v,id) over a cell list sets find(id)=v and leaves other ids unchanged (value-level model of the list with full-width fields). PROVED.

## Correspondence and assumptions
F* `wrap24` models bit-field truncation; `store_new` models an `int` field; `find`/`replace` model the list as an immutable list of (id,var) pairs. Assumes int is 32-bit two's complement, ids unique per list (as SASSERT'd in add_var), and the replaced id exists. Only base F* library/standard library assumed; no admits.

## Not covered
Pointer-linked mutation/aliasing in add_var/del_var, region allocation, memory safety, sizeof static_asserts (16 bytes on 64-bit: 4+4+8, trivially holds; 32-bit: 2*4+4=12 matches), the test file src/test/list.cpp (not executed, PR code not run), and all callers of id_var_list (e.g. users that may rely on an 8-bit id range or on null_var sentinels colliding with large vars: with full int, var == null_var (-1) remains the only sentinel). Semantic proof only; not mechanized verification of C++.

## Reproduce
See verification log. F* 2026.09.27, Z3 4.13.3.
