module OptLabelsAudit

(* Abstract model of optsmt best-model/label pairing (PR #11372).
   labels_of is a universally quantified function: the labels the solver
   reports for a model id. No axioms, no assume. *)

type st = { best: int; labels: list int }      (* m_best_model, optsmt::m_labels *)
type ctx = { m_model: int; m_labels: list int } (* context state after initial check *)

let paired (lf:int -> list int) (s:st) : prop = s.labels == lf s.best
let ctx_ok (lf:int -> list int) (c:ctx) : prop = c.m_labels == lf c.m_model

(* old: m_context.get_base_model(m_best_model) only *)
let base_old (c:ctx) (s:st) : st = { s with best = c.m_model }
(* new: also m_labels.reset(); m_context.get_labels(m_labels) *)
let base_new (c:ctx) (s:st) : st = { best = c.m_model; labels = c.m_labels }
(* improvement: m_best_model = m_model; m_s->get_labels(m_labels) *)
let improve (lf:int -> list int) (m:int) (_:st) : st = { best = m; labels = lf m }

let rec run (lf:int -> list int) (ms:list int) (s:st) : Tot st (decreases ms) =
  match ms with [] -> s | m::t -> run lf t (improve lf m s)

(* O1: new seeding establishes the pairing invariant (no improvement => get_model paired) *)
let o1 (lf:int -> list int) (c:ctx) (s:st)
  : Lemma (requires ctx_ok lf c) (ensures paired lf (base_new c s)) = ()

(* O2: improvement preserves it *)
let o2 (lf:int -> list int) (m:int) (s:st) : Lemma (ensures paired lf (improve lf m s)) = ()

(* O3: after seeding and any sequence of improvements, result is paired *)
let rec o3 (lf:int -> list int) (ms:list int) (s:st)
  : Lemma (requires paired lf s) (ensures paired lf (run lf ms s)) (decreases ms) =
  match ms with
  | [] -> ()
  | m::t -> o3 lf t (improve lf m s)

let o3' (lf:int -> list int) (ms:list int) (c:ctx) (s:st)
  : Lemma (requires ctx_ok lf c) (ensures paired lf (run lf ms (base_new c s))) =
  o3 lf ms (base_new c s)

(* Refutation of the OLD behaviour: concrete witness. Base model 1 has labels [7];
   optsmt labels start empty; no improvement. Old seeding is unpaired, new is paired. *)
let lf0 (m:int) : list int = if m = 1 then [7] else []

let witness_old () : Lemma (
    let c = { m_model = 1; m_labels = [7] } in
    let s0 = { best = 0; labels = [] } in
    ctx_ok lf0 c /\ s0.labels == [] /\ (run lf0 [] (base_old c s0)).labels == [] /\ lf0 1 == [7]
    /\ ~(paired lf0 (run lf0 [] (base_old c s0)))) =
  assert_norm (lf0 1 == [7]);
  assert_norm ([] <> [7])

let witness_new () : Lemma (
    let c = { m_model = 1; m_labels = [7] } in
    let s0 = { best = 0; labels = [] } in
    paired lf0 (run lf0 [] (base_new c s0))) = assert_norm (lf0 1 == [7])
