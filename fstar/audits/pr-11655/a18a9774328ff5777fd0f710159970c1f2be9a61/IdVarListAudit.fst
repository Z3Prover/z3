module IdVarListAudit
(* Models a C++ int field storing an int32 value, before (24-bit signed bit-field,
   two's complement wrap, the implementation-defined behaviour on gcc/clang/MSVC) and after the PR (full int). *)
let int32_min = -2147483648
let int32_max = 2147483647
type i32 = v:int{v >= int32_min /\ v <= int32_max}

let wrap24 (v:int) : int =
  let m = v % 16777216 in
  if m >= 8388608 then m - 16777216 else m

let store_old (v:i32) : int = wrap24 v
let store_new (v:i32) : i32 = v

(* O1: counterexample on base: v = 2^23 is read back as -2^23 (negative index). *)
let o1_witness () : Lemma (store_old 8388608 <> 8388608 /\ store_old 8388608 = -8388608 /\ store_old 2147483647 = -1) = ()

(* O2: after PR, set_var/get_var round-trips every int32, including 2^23-1, 2^23, 2^23+1, INT_MAX. *)
let o2_roundtrip (v:i32) : Lemma (store_new v = v) = ()

(* O3: replace on a list of cells: cell content after replace(v,id) at matching id returns v for
   find(id); other ids unchanged. Cells are (id,var) pairs with full-width fields. *)
type cell = tuple2 i32 i32
let rec find (l:list cell) (id:i32) (null_var:i32) : i32 =
  match l with
  | [] -> null_var
  | (i,v)::t -> if i = id then v else find t id null_var
let rec replace (l:list cell) (v:i32) (id:i32) : list cell =
  match l with
  | [] -> []
  | (i,w)::t -> if i = id then (i,v)::t else (i,w)::replace t v id
let rec o3_replace (l:list cell) (v:i32) (id id2:i32) : Lemma
  (requires Cons? l /\ (exists (c:cell). List.Tot.memP c l /\ fst c = id))
  (ensures find (replace l v id) id (-1) = v /\ (id2 <> id ==> find (replace l v id) id2 (-1) = find l id2 (-1)))
  (decreases l) =
  match l with
  | [(i,w)] -> ()
  | (i,w)::t -> if i = id then () else (
      match t with
      | [] -> ()
      | _ -> o3_replace t v id id2)
