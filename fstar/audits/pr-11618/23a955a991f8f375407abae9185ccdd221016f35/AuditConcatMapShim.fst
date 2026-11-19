module AuditConcatMapShim
open FStar.List.Tot

(* Model of OCaml Stdlib.List.concat_map: accumulate with rev_append, reverse at the end. *)
let rec rev_app (#a:Type) (l acc: list a) : Tot (list a) (decreases l) =
  match l with [] -> acc | x :: t -> rev_app t (x :: acc)

let rec rev_app_spec (#a:Type) (l acc: list a)
  : Lemma (ensures rev_app l acc == rev l @ acc) (decreases l) =
  match l with
  | [] -> ()
  | x :: t ->
    rev_app_spec t (x :: acc);
    rev_append [x] t;
    append_assoc (rev t) [x] acc

let rec aux (#a #b:Type) (f: a -> Tot (list b)) (acc: list b) (l: list a) : Tot (list b) (decreases l) =
  match l with
  | [] -> rev_app acc []
  | x :: tl -> aux f (rev_app (f x) acc) tl

let ocaml_concat_map (#a #b:Type) (f: a -> Tot (list b)) (l: list a) : list b = aux f [] l

(* O1: invariant of the accumulator loop *)
let rec aux_correct (#a #b:Type) (f: a -> Tot (list b)) (acc: list b) (l: list a)
  : Lemma (ensures aux f acc l == rev acc @ concatMap f l) (decreases l) =
  match l with
  | [] -> rev_app_spec acc []; append_l_nil (rev acc)
  | x :: tl ->
    rev_app_spec (f x) acc;
    aux_correct f (rev_app (f x) acc) tl;
    rev_append (rev (f x)) acc;
    rev_involutive (f x);
    append_assoc (rev acc) (f x) (concatMap f tl)

(* O2: shim equals the F* spec concatMap *)
let concat_map_shim_correct (#a #b:Type) (f: a -> Tot (list b)) (l: list a)
  : Lemma (ocaml_concat_map f l == concatMap f l) =
  aux_correct f [] l
