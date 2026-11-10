module PRClauseEqualityAudit
module L = FStar.List.Tot

(* Abstract propositional model of integer_product_clause_equality:
   a clause is a list of literals evaluated under valuation v; the rule
   picks e in lits, assumes facts and the negation of every literal <> e,
   and requires that these entail e. *)
type lit = int
let holds_clause (v:lit -> bool) (lits:list lit) : bool = L.existsb v lits
let others_false (v:lit -> bool) (lits:list lit) (e:lit) : prop =
  forall (t:lit). L.mem t lits /\ t <> e ==> not (v t)

(* O1: soundness of the guarded step, including duplicate occurrences of e *)
let rec step_sound (v:lit -> bool) (lits:list lit) (e:lit)
  : Lemma (requires L.mem e lits /\ others_false v lits e /\ v e)
          (ensures holds_clause v lits) (decreases lits) =
  match lits with
  | [] -> ()
  | h :: t -> if h = e then () else step_sound v t e

(* O2: if the clause is false, every literal is false, hence complements of
   all non-e literals hold (what lemma_clause_complements_except provides) *)
let rec clause_false_all (v:lit -> bool) (lits:list lit)
  : Lemma (requires not (holds_clause v lits))
          (ensures forall (t:lit). L.mem t lits ==> not (v t)) (decreases lits) =
  match lits with
  | [] -> ()
  | _ :: t -> clause_false_all v t

(* O3: arithmetic of the example: x<=2 /\ x>=2 ==> x*y = 2*y over Int *)
let example_arith (x y:int)
  : Lemma (requires x <= 2 /\ x >= 2) (ensures x * y = 2 * y) = ()

(* Refutation attempt: no witness, since O1 holds universally. Control:
   dropping the others-false premise is unsound (clause can be false). *)
let control_needs_guard : unit =
  let v : lit -> bool = fun _ -> false in
  assert (not (holds_clause v [1;2]))
