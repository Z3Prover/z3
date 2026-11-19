module Z3PR11533Audit
open FStar.List.Tot

(* then_simplifier::supports_proofs = all_of(m_simplifiers, supports_proofs) *)
let rec supports_all (l: list bool) : bool =
  match l with | [] -> true | s :: t -> s && supports_all t

let rec o1 (l: list bool) : Lemma (supports_all l = true <==> (forall x. memP x l ==> x = true)) =
  match l with | [] -> () | _ :: t -> o1 t

let rec o2 (a b: list bool) : Lemma (supports_all (a @ b) = (supports_all a && supports_all b)) =
  match a with | [] -> () | _ :: t -> o2 t b

(* nested then(then(a,b),c): a child's flag is its own supports_all *)
let o3 (a b c: list bool) : Lemma
  (supports_all [supports_all (a @ b); supports_all c] = supports_all (a @ b @ c)) =
  o2 a b; o2 a (b @ c); o2 b c

(* one unsupported leaf at any nesting depth makes the pipeline false *)
let o3b (a b: list bool) : Lemma (requires memP false a \/ memP false b)
  (ensures supports_all (a @ b) = false) = o1 (a @ b); append_memP a b false

(* Flush check: for i in [qhead,size): !pr || fact(pr) != fml => throw.
   Formulas are (fml, pr option) with fact abstracted as a function on proof ids. *)
type dep = { fml: int; pr: option int }
let ok (fact: int -> int) (d: dep) : bool =
  match d.pr with | None -> false | Some p -> fact p = d.fml

let rec all_ok (fact: int -> int) (l: list dep) : bool =
  match l with | [] -> true | d :: t -> ok fact d && all_ok fact t

(* O4: no exception iff every flushed formula has a proof whose fact is exactly it *)
let rec o4 (fact: int -> int) (l: list dep) : Lemma
  (all_ok fact l = true <==> (forall d. memP d l ==> (Some? d.pr /\ fact (Some?.v d.pr) = d.fml))) =
  match l with | [] -> () | _ :: t -> o4 fact t

(* O5: the PR's test witness: not(a) carrying a's proof (fact = identity) is rejected,
   and so is a dropped proof; both are reachable from malformed_proof_simplifier. *)
let neg (x:int) = -x - 1
let o5 : unit =
  assert (not (ok (fun p -> p) {fml = neg 5; pr = Some 5}));
  assert (not (ok (fun p -> p) {fml = neg 5; pr = None}))

(* O6: an unsupporting simplifier with proofs enabled and a factory is rejected at
   construction; with proofs disabled nothing is checked. *)
let guard (proofs factory supports: bool) : bool = factory && proofs && not supports
let o6 : unit =
  assert (guard true true false = true);
  assert (guard false true false = false);
  assert (guard true true true = false)
