module Z3SeqRewriterExtract

(*
   Length-only audit of the nested-extract flattening rules in
   src/ast/rewriter/seq_rewriter.cpp::mk_seq_extract (lines 1017-1085).

   We model only the exact SMT-LIB extract/substring length semantics:

     extract_result_len(|s|, offset, req) =
       0                           if offset >= |s|
       min(req, |s| - offset)      otherwise

   All offsets/length requests below are naturals, which is enough for the
   branches audited here: every flattening rule in question is guarded by
   non-negative numerals or by syntactic `is_prefix` / `is_suffix` shapes
   whose arithmetic parameters are themselves natural "trim counts".
*)

let min_nat (x y:nat) : nat =
  if x < y then x else y

let remaining_len (base_len offset:nat) : nat =
  if offset < base_len then base_len - offset else 0

let extract_result_len (base_len offset req_len:nat) : nat =
  min_nat req_len (remaining_len base_len offset)

/// extract(s, p, |s|-p) is exactly the suffix of length |s|-p.
let suffix_exact_len (base_len offset:nat) : Lemma
  (extract_result_len base_len offset (remaining_len base_len offset) == remaining_len base_len offset) =
  ()

/// seq_rewriter.cpp:1017-1024
///   extract(extract(x, p1, |x|-p1), p2, |extract(...)|-p2)
///   -> extract(x, p1+p2, (|x|-p1)-p2)
let suffix_suffix_flatten_len (base_len p1 p2:nat) : Lemma
  (extract_result_len
      (extract_result_len base_len p1 (remaining_len base_len p1))
      p2
      (remaining_len (extract_result_len base_len p1 (remaining_len base_len p1)) p2)
   ==
   extract_result_len base_len (p1 + p2) (remaining_len (remaining_len base_len p1) p2)) =
  suffix_exact_len base_len p1

/// seq_rewriter.cpp:1038-1050
///   extract(extract(x, p1, l1), p2, l2)
///   -> extract(x, p1+p2, min(l1-p2, l2))
/// under the branch guard p2 <= l1.
let nested_numeric_flatten_len (base_len p1 l1 p2 l2:nat) : Lemma
  (requires p2 <= l1)
  (ensures
    extract_result_len
      (extract_result_len base_len p1 l1)
      p2
      l2
    ==
    extract_result_len
      base_len
      (p1 + p2)
      (if remaining_len l1 p2 < l2 then remaining_len l1 p2 else l2)) =
  ()

/// seq_rewriter.cpp:1028-1031
///   if p1 = 0 and l1 >= p2 + l2 then
///   extract(extract(x, 0, l1), p2, l2) -> extract(x, p2, l2)
let zero_offset_covering_shortcut_len (base_len l1 p2 l2:nat) : Lemma
  (requires l1 >= p2 + l2)
  (ensures
    extract_result_len
      (extract_result_len base_len 0 l1)
      p2
      l2
    ==
    extract_result_len base_len p2 l2) =
  ()

/// seq_rewriter.cpp:1053-1056
///   extract(extract(x, 0, |x|-d1), 0, |extract(...)|-d2)
///   -> extract(x, 0, (|x|-d1)-d2)
let prefix_prefix_flatten_len (base_len d1 d2:nat{d1 > 0 /\ d2 > 0}) : Lemma
  (extract_result_len
      (extract_result_len base_len 0 (remaining_len base_len d1))
      0
      (remaining_len (extract_result_len base_len 0 (remaining_len base_len d1)) d2)
   ==
   extract_result_len base_len 0 (remaining_len (remaining_len base_len d1) d2)) =
  ()

/// seq_rewriter.cpp:1059-1064
///   extract(extract(x, p, |x|-p), 0, |extract(...)|-d)
///   -> extract(x, p, (|x|-p)-d)
let prefix_of_suffix_flatten_len (base_len p d:nat{d > 0}) : Lemma
  (extract_result_len
      (extract_result_len base_len p (remaining_len base_len p))
      0
      (remaining_len (extract_result_len base_len p (remaining_len base_len p)) d)
   ==
   extract_result_len base_len p (remaining_len (remaining_len base_len p) d)) =
  suffix_exact_len base_len p

/// seq_rewriter.cpp:1067-1070
///   extract(extract(x, p, l), 0, |x|)
///   -> extract(x, p, l)
let nested_extract_identity_len_of_base (base_len p l:nat) : Lemma
  (extract_result_len
      (extract_result_len base_len p l)
      0
      base_len
   ==
   extract_result_len base_len p l) =
  ()

/// seq_rewriter.cpp:1073-1076
///   extract(extract(x, p, l), 0, l)
///   -> extract(x, p, l)
let nested_extract_identity_len_of_same_request (base_len p l:nat) : Lemma
  (extract_result_len
      (extract_result_len base_len p l)
      0
      l
   ==
   extract_result_len base_len p l) =
  ()

/// seq_rewriter.cpp:1079-1085
///   extract(extract(x, p1, l1), p2, |extract(...)|-p2)
///   -> extract(x, p1+p2, l1-p2)
///
/// This is the branch the external report suspected, but the clamping on the
/// *outer* flattened extract is enough to recover the correct final length even
/// when l1 is overlong relative to x.
let suffix_of_numeric_flatten_len (base_len p1 l1 p2:nat{p2 > 0}) : Lemma
  (extract_result_len
      (extract_result_len base_len p1 l1)
      p2
      (remaining_len (extract_result_len base_len p1 l1) p2)
   ==
   extract_result_len base_len (p1 + p2) (remaining_len l1 p2)) =
  ()

/// The NFV witness itself computes the right length semantically:
/// |X| = 1, inner = extract(X,0,2), outer = extract(inner,0,|inner|-1).
let nfv_witness_semantics () : Lemma
  (extract_result_len
      (extract_result_len 1 0 2)
      0
      (remaining_len (extract_result_len 1 0 2) 1)
   == 0) =
  ()
