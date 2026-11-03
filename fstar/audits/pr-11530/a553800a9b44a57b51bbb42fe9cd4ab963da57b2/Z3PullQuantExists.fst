module Z3PullQuantExists
(* Audit of PR 11530: pull_quant.cpp reduce_quantifier, is_exists branch.
   Source: result = mk_not(new_body); result = not(forall(result)); result_pr = mk_rewrite(old_q,result). *)
open FStar.Classical

type fm =
  | FTrue | FFalse | FAtom : nat -> fm | FNot : fm -> fm

(* ast_util.cpp mk_not(m, arg) *)
let mk_not (a:fm) : fm =
  match a with
  | FNot x -> x
  | FTrue -> FFalse
  | FFalse -> FTrue
  | _ -> FNot a

(* semantics under a valuation of atoms, per bound-variable value *)
let rec ev (v:nat -> prop) (f:fm) : Tot prop (decreases f) =
  match f with
  | FTrue -> True | FFalse -> False | FAtom n -> v n
  | FNot g -> ~(ev v g)

(* Obligation 1: mk_not is semantically negation *)
let ob1 (v:nat -> prop) (a:fm) : Lemma (ev v (mk_not a) <==> ~(ev v a)) = ()

(* Obligation 2: exists x. B(x)  <==>  not (forall x. not-sem(mk_not B(x)))
   Body family b : x -> fm, evaluated per value of the bound variable. *)
let ob2 (#d:Type) (v:d -> nat -> prop) (b:fm)
  : Lemma ((exists (x:d). ev (v x) b) <==> ~(forall (x:d). ev (v x) (mk_not b)))
  = FStar.Classical.forall_intro (fun (x:d) -> ob1 (v x) b)

(* Obligation 3: proof-chain endpoints. Proof terms as (lhs,rhs) facts. *)
type fact = { l:fm; r:fm }
type pf = option fact   (* None = null proof *)
(* ast_manager::mk_transitivity: null on either side returns the other *)
let trans (p1 p2:pf) : pf =
  match p1, p2 with
  | None, _ -> p2 | _, None -> p1
  | Some a, Some b -> if a.r = b.l then Some ({l=a.l; r=b.r}) else None

(* caller (rewriter_def.h): m_pr: q = new_q (or null if q==new_q), then pr2 = rewrite(new_q,result) *)
let ob3 (q new_q result:fm) (m_pr_prev:pf)
  : Lemma (requires (match m_pr_prev with None -> q == new_q | Some f -> f.l == q /\ f.r == new_q))
          (ensures (match trans m_pr_prev (Some {l=new_q; r=result}) with
                    | Some f -> f.l == q /\ f.r == result | None -> False))
  = ()

(* Base behaviour (pre-PR): pr2 discarded (null) => endpoint stays new_q, not result. *)
let ob3_old (q new_q result:fm) (hp:squash (new_q <> result))
  : Lemma (match trans (Some {l=q; r=new_q}) None with
           | Some f -> f.r <> result | None -> False)
  = ()
