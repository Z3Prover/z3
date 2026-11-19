module Z3PR11533ProofContract
open FStar.List.Tot

(* then_simplifier::supports_proofs: conjunction over children *)
let rec supports_all (l: list bool) : bool =
  match l with | [] -> true | s :: t -> if not s then false else supports_all t

(* O1: result is true iff every child supports proofs *)
let rec o1 (l: list bool) : Lemma (supports_all l = true <==> (forall x. memP x l ==> x = true)) =
  match l with | [] -> () | _ :: t -> o1 t

(* O2: nested composition is flat conjunction (then(then(a,b),c)) *)
let rec o2 (a b: list bool) : Lemma (supports_all (a @ b) = (supports_all a && supports_all b)) =
  match a with | [] -> () | _ :: t -> o2 t b

(* O3: one unsupported leaf at any depth makes the pipeline report false *)
let o3 (a b: list bool) : Lemma (requires memP false a \/ memP false b)
  (ensures supports_all (a @ b) = false) =
  o1 (a @ b); append_memP a b false

(* Flush-time contract: an assertion is accepted iff it has a proof whose fact equals it.
   Fact is abstracted as an integer expression id; pr = None models nullptr. *)
let accept (fml: int) (pr: option int) (fact: int -> int) : bool =
  match pr with | None -> false | Some p -> fact p = fml

(* O4: accepted implies a proof exists with fact exactly the asserted formula;
   rejected for missing proofs and for any mismatched fact *)
let o4 (fml: int) (pr: option int) (fact: int -> int) : Lemma
  (ensures (accept fml pr fact = true <==> (Some? pr /\ fact (Some?.v pr) = fml))) = ()

(* Concrete witness check for the test's malformed simplifier: not(a) with old proof of a *)
let neg (x:int) = -x - 1
let o5 : unit = assert (accept (neg 5) (Some 5) (fun p -> p) = false); assert (accept (neg 5) None (fun p -> p) = false)
