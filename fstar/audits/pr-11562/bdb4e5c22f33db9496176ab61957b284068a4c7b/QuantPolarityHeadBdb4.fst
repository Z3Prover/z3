module QuantPolarityHeadBdb4
(* Boolean abstraction of context::internalize_quantifier at head bdb4e5c2. *)
type lb = | LTrue | LFalse | LUndef
type kind = | Forall | Exists

let flip (p:lb) : lb = match p with LTrue -> LFalse | LFalse -> LTrue | LUndef -> LUndef
(* an occurrence polarity (true = positive) is permitted by the lbool argument *)
let permits (p:lb) (pos:bool) : bool =
  match p with LUndef -> true | LTrue -> pos | LFalse -> not pos

(* guards of internalize_quantifier: (positive skolem/NNF clause, negative clause) *)
let pos_clause (k:kind) (p:lb) : bool = (k = Exists) && (p <> LFalse)
let neg_clause (p:lb) : bool = (p <> LTrue)
(* forall positive is handled by the quantifier manager (registered on first internalization) *)
let covered (k:kind) (p:lb) (pos:bool) : bool =
  if pos then (k = Forall) || pos_clause k p else neg_clause p

(* O1: every permitted occurrence polarity is covered by a registration or clause *)
let o1 (k:kind) (p:lb) (pos:bool) : Lemma (requires permits p pos) (ensures covered k p pos) = ()

(* O2: the NOT-gate shortcut (~polarity) maps permitted polarities exactly *)
let o2 (p:lb) (pos:bool) : Lemma (ensures permits (flip p) (not pos) == permits p pos) = ()

(* O3: premise literal literal(var(q), !positive) is true exactly when the NNF source
   (q if positive, not q if negative) holds, so the clause (~premise \/ result) is source ==> result. *)
let lit_true (b:bool) (sign:bool) : bool = if sign then not b else b
let source (b:bool) (positive:bool) : bool = if positive then b else not b
let o3 (b:bool) (positive:bool) (result:bool)
  : Lemma (ensures (not (lit_true b (not positive)) || result) == (not (source b positive) || result)) = ()
