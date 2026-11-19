module Z3BvFamilyId
(* Model of family_manager::mk_family_id (src/ast/ast.cpp:127-137):
   a table of names; existing name -> its index, otherwise append, id = old size. *)
open FStar.List.Tot

type fm = list string

let rec idx (s:string) (m:fm) : option nat =
  match m with
  | [] -> None
  | x::xs -> if x = s then Some 0 else (match idx s xs with Some i -> Some (i+1) | None -> None)

let mk (m:fm) (s:string) : (nat & fm) =
  match idx s m with
  | Some i -> (i, m)
  | None -> (length m, m @ [s])

(* ast_manager::init order, with the PR's added ENSURE for "bv" *)
let init_names = ["basic";"label";"pattern";"model-value";"user-sort";"arith";"polymorphic";"bv"]

let rec run (m:fm) (l:list string) : Tot fm (decreases l) =
  match l with [] -> m | s::r -> run (snd (mk m s)) r

let bv_family_id : nat = 7

(* O1: the PR's ENSURE holds on an empty manager: the 8th mk_family_id call returns 7 *)
let o1 () : Lemma (mk (run [] ["basic";"label";"pattern";"model-value";"user-sort";"arith";"polymorphic"]) "bv"
                   == (bv_family_id, init_names)) = assert_norm (mk (run [] ["basic";"label";"pattern";"model-value";"user-sort";"arith";"polymorphic"]) "bv" == (bv_family_id, init_names))

(* O2: after init, later lookups of "bv" (bv_util ctor, plugin registration, API) return 7 *)
let o2 () : Lemma (idx "bv" (run [] init_names) == Some bv_family_id) = assert_norm (idx "bv" (run [] init_names) == Some bv_family_id)

(* O3: mk_family_id is idempotent and never renumbers existing families *)
let rec idx_append (s:string) (m:fm) (t:string) : Lemma
  (requires Some? (idx s m)) (ensures idx s (m @ [t]) == idx s m) =
  match m with [] -> () | x::xs -> if x = s then () else idx_append s xs t

let o3 (m:fm) (s:string) (t:string) : Lemma
  (requires Some? (idx s m))
  (ensures fst (mk m t) >= 0 /\ idx s (snd (mk m t)) == idx s m) =
  match idx t m with Some _ -> () | None -> idx_append s m t

(* O4: the preassigned names occupy distinct ids 0..7, so bv's id cannot collide with a builtin/arith/poly id *)
let o4 () : Lemma (idx "arith" (run [] init_names) == Some 5 /\ idx "polymorphic" (run [] init_names) == Some 6
                   /\ idx "user-sort" (run [] init_names) == Some 4) = assert_norm (idx "arith" (run [] init_names) == Some 5 /\ idx "polymorphic" (run [] init_names) == Some 6 /\ idx "user-sort" (run [] init_names) == Some 4)
