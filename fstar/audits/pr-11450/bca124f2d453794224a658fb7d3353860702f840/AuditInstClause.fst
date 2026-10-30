module AuditInstClause
(* Abstract many-sorted model of the QuantifierInstantiation clause
   (or (not (forall x:s. body)) body[t/x]) used by Z3QuantifierKernel.
   Independent re-derivation; does not import PR proof modules. *)
type sort = | SInt | SBool
type value = | VInt : int -> value | VBool : bool -> value
let sort_of (v:value) : sort = match v with VInt _ -> SInt | VBool _ -> SBool
type ty (s:sort) = v:value{sort_of v == s}

(* O1: for a well-sorted argument, the clause holds for every body. *)
let inst_clause (s:sort) (body: value -> bool) (t: ty s) : Lemma
  (ensures (~(forall (x:ty s). body x) \/ body t)) = ()

(* O2: the clause is a disjunction, so an equality-shaped conclusion
   can never be the clause (canonical Or vs Eq disjointness). *)
type prop_shape = | POr : prop_shape -> prop_shape -> prop_shape | PNot : prop_shape -> prop_shape | PEq : prop_shape
let is_clause (p:prop_shape) = POr? p
let eq_never_clause () : Lemma (~(is_clause PEq)) = ()

