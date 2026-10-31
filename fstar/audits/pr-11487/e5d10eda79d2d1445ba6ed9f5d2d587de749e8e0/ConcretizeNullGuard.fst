module ConcretizeNullGuard
(* Abstract model of lemma_global_generalizer::mk_concretize_pob at head e5d10eda.
   model: option (None = null model_ref). Dereference is modelled as an effect flag. *)
type result = | NoPob | NewPob : int -> result
type outcome = { res: result; derefs_null: bool; orig_changed: bool }

(* proc_ok / newpost: abstract result of pob_concretizer::apply when model is non-null *)
let mk_concretize (model: option int) (proc_ok: bool) (newpost: int) : outcome =
  match model with
  | None -> { res = NoPob; derefs_null = false; orig_changed = false }
  | Some _ ->
    if proc_ok then { res = NewPob newpost; derefs_null = false; orig_changed = false }
    else { res = NoPob; derefs_null = false; orig_changed = false }

(* O1: null model never dereferenced and returns no pob *)
let o1 (p:bool) (q:int) : Lemma ((mk_concretize None p q).derefs_null == false /\ (mk_concretize None p q).res == NoPob) = ()
(* O2: original pob unchanged on every path *)
let o2 (m:option int) (p:bool) (q:int) : Lemma ((mk_concretize m p q).orig_changed == false) = ()
(* O3: with a non-null model behaviour equals the base (no guard) behaviour *)
let base (p:bool) (q:int) : result = if p then NewPob q else NoPob
let o3 (v:int) (p:bool) (q:int) : Lemma ((mk_concretize (Some v) p q).res == base p q) = ()
(* Caller (spacer_context.cpp:3607) treats NoPob like the pre-existing apply-failure path. *)
