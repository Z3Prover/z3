module FlattenClausesPR11334Head
open FStar.List.Tot

type form = | V : nat -> form | Not : form -> form | Or : list form -> form

let rec ev (rho:nat -> bool) (f:form) : Tot bool (decreases f) =
  match f with
  | V i -> rho i
  | Not g -> not (ev rho g)
  | Or gs -> ev_or rho gs
and ev_or (rho:nat -> bool) (gs:list form) : Tot bool (decreases gs) =
  match gs with
  | [] -> false
  | g::r -> ev rho g || ev_or rho r

(* mk_not in C++: strip a negation if present, else wrap *)
let mk_not (e:form) : form = match e with Not x -> x | _ -> Not e

let mk_not_sem (rho:nat -> bool) (e:form) : Lemma (ev rho (mk_not e) == not (ev rho e)) = ()

(* clause (or a (not (or bs))) vs the clauses (or a (mk_not b)) for b in bs *)
let rec all_clauses (rho:nat -> bool) (a:form) (bs:list form) : bool =
  match bs with
  | [] -> true
  | b::r -> ev rho (Or [a; mk_not b]) && all_clauses rho a r

let rec ev_or_exists (rho:nat -> bool) (bs:list form)
  : Lemma (ev_or rho bs == existsb (fun b -> ev rho b) bs)
  = match bs with [] -> () | _::r -> ev_or_exists rho r

(* Obligation 1: distribution preserves equivalence (both disjunct orders are symmetric via commutativity of ||) *)
let rec distribute_sound (rho:nat -> bool) (a:form) (bs:list form)
  : Lemma (ev rho (Or [a; Not (Or bs)]) == all_clauses rho a bs)
  = match bs with
    | [] -> ()
    | _::r -> distribute_sound rho a r

(* Obligation 2: the new guard strengthens the old one, so every rewrite the patch still performs
   was already performed by the base; the set of rewrites is a subset. *)
let old_guard (n:nat) = (n = 1)
let new_guard (n:nat) (is_not_e:bool) (rc_d:nat) = (n = 1) && is_not_e && (rc_d = 1)
let guard_refines (n:nat) (b:bool) (rc:nat) : Lemma (new_guard n b rc ==> old_guard n) = ()

(* Obligation 3: guard is not vacuous (reachable): unshared negated disjunction with rc 1 passes;
   a shared one (rc 2, e.g. also in (or d x)) is rejected. *)
let guard_pass : squash (new_guard 1 true 1) = ()
let guard_reject_shared : squash (~(new_guard 1 true 2)) = ()
let guard_reject_non_not : squash (~(new_guard 1 false 1)) = ()

(* Whole-formula: any sequence of such rewrites preserves the conjunction of the clause set *)
let rec conj (rho:nat -> bool) (cs:list form) : bool =
  match cs with [] -> true | c::r -> ev rho c && conj rho r

let rec conj_append (rho:nat -> bool) (x y:list form)
  : Lemma (conj rho (x @ y) == (conj rho x && conj rho y))
  = match x with [] -> () | _::r -> conj_append rho r y

let rec clauses_of (a:form) (bs:list form) : list form =
  match bs with [] -> [] | b::r -> Or [a; mk_not b] :: clauses_of a r

let rec clauses_conj (rho:nat -> bool) (a:form) (bs:list form)
  : Lemma (conj rho (clauses_of a bs) == all_clauses rho a bs)
  = match bs with [] -> () | _::r -> clauses_conj rho a r

let rewrite_sound (rho:nat -> bool) (pre post:list form) (a:form) (bs:list form)
  : Lemma (conj rho (pre @ [Or [a; Not (Or bs)]] @ post)
        == conj rho (pre @ clauses_of a bs @ post))
  = conj_append rho pre ([Or [a; Not (Or bs)]] @ post);
    conj_append rho [Or [a; Not (Or bs)]] post;
    conj_append rho pre (clauses_of a bs @ post);
    conj_append rho (clauses_of a bs) post;
    distribute_sound rho a bs; clauses_conj rho a bs
