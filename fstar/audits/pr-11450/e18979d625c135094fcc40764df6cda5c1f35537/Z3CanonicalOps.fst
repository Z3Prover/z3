(*
   Z3CanonicalOps.fst

   One typed policy for the interpreted Boolean connectives, shared by the
   model contracts that give them their meaning and by the checkers that
   dispatch on them.

   A declaration is the canonical `not`, `and`, `or`, `=>`, `=`, `true` or
   `false` only when its name, its kind tag (`Z3ValueTheory.op_*`), its
   domain, its range and its parameters all have the shape Z3's
   `basic_decl_plugin` gives that connective. The native bridge
   (`Z3NativeProof.marshal_declaration`) produces exactly these shapes:
   the name is Z3's, the tag comes from `operator_tag`, the domain is the
   list of argument sorts, and the connectives carry no parameters.

   Keying a contract by the name alone is not enough. A user datatype may
   have an accessor named `and` (tag `Z3DatatypeLemma.op_accessor`), and
   nothing in the term language stops a declaration named `=` from carrying
   a bit-vector tag. A contract keyed by name would then constrain the same
   application twice, once as a Boolean connective and once by the
   datatype or bit-vector contract that its tag selects, and the two can
   contradict each other. The canonical predicates below accept only the
   Boolean tags, which are all below 100, while the bit-vector (100-120),
   datatype (200-202) and finite-field tags are not, so no declaration is
   both a canonical connective and a declaration of another theory
   (`lemma_canonical_tag`).
*)
module Z3CanonicalOps

open Z3AstTheory
open Z3ValueTheory

let rec boolean_sorts (dom:list sort) : Tot bool (decreases dom) =
  match dom with
  | [] -> true
  | s :: rest -> s = bool_sort && boolean_sorts rest

let canonical_true (f:func_decl) : bool =
  f.decl_name = "true" && f.interp = Some op_true && f.domain = [] &&
  f.range = bool_sort && f.int_params = []

let canonical_false (f:func_decl) : bool =
  f.decl_name = "false" && f.interp = Some op_false && f.domain = [] &&
  f.range = bool_sort && f.int_params = []

let canonical_not (f:func_decl) : bool =
  f.decl_name = "not" && f.interp = Some op_not && f.domain = [bool_sort] &&
  f.range = bool_sort && f.int_params = []

let canonical_and (f:func_decl) : bool =
  f.decl_name = "and" && f.interp = Some op_and && boolean_sorts f.domain &&
  f.range = bool_sort && f.int_params = []

let canonical_or (f:func_decl) : bool =
  f.decl_name = "or" && f.interp = Some op_or && boolean_sorts f.domain &&
  f.range = bool_sort && f.int_params = []

let canonical_implies (f:func_decl) : bool =
  (f.decl_name = "=>" || f.decl_name = "implies") && f.interp = Some op_implies &&
  f.domain = [bool_sort; bool_sort] && f.range = bool_sort && f.int_params = []

let canonical_eq (f:func_decl) : bool =
  f.decl_name = "=" && f.interp = Some op_eq && f.range = bool_sort && f.int_params = [] &&
  (match f.domain with
   | [s; t] -> s = t
   | _ -> false)

let canonical_connective (f:func_decl) : bool =
  canonical_true f || canonical_false f || canonical_not f || canonical_and f ||
  canonical_or f || canonical_implies f || canonical_eq f

(* Every canonical connective carries one of the Boolean kind tags; the
   kind tags of the other theories are at least 100. *)
let lemma_canonical_tag (f:func_decl)
  : Lemma (requires canonical_connective f)
          (ensures Some? f.interp /\ Some?.v f.interp < 100 /\
                   (f.interp = Some op_true \/ f.interp = Some op_false \/ f.interp = Some op_not \/
                    f.interp = Some op_and \/ f.interp = Some op_or \/ f.interp = Some op_implies \/
                    f.interp = Some op_eq))
  = ()

(* The canonical connectives are pairwise distinct: a declaration is at
   most one of them. *)
let lemma_canonical_exclusive (f:func_decl)
  : Lemma ((canonical_true f ==> ~(canonical_false f \/ canonical_not f \/ canonical_and f \/
                                   canonical_or f \/ canonical_implies f \/ canonical_eq f)) /\
           (canonical_false f ==> ~(canonical_not f \/ canonical_and f \/ canonical_or f \/
                                    canonical_implies f \/ canonical_eq f)) /\
           (canonical_not f ==> ~(canonical_and f \/ canonical_or f \/ canonical_implies f \/
                                  canonical_eq f)) /\
           (canonical_and f ==> ~(canonical_or f \/ canonical_implies f \/ canonical_eq f)) /\
           (canonical_or f ==> ~(canonical_implies f \/ canonical_eq f)) /\
           (canonical_implies f ==> ~(canonical_eq f)))
  = ()

(* The canonical declarations themselves, as the checkers build them. *)
let true_decl : func_decl =
  { decl_name = "true"; domain = []; range = bool_sort; interp = Some op_true; int_params = [] }

let false_decl : func_decl =
  { decl_name = "false"; domain = []; range = bool_sort; interp = Some op_false; int_params = [] }

let not_decl : func_decl =
  { decl_name = "not"; domain = [bool_sort]; range = bool_sort; interp = Some op_not; int_params = [] }

let eq_decl (s:sort) : func_decl =
  { decl_name = "="; domain = [s; s]; range = bool_sort; interp = Some op_eq; int_params = [] }

let rec boolean_domain (n:nat) : Tot (list sort) (decreases n) =
  if n = 0 then [] else bool_sort :: boolean_domain (n - 1)

let rec lemma_boolean_domain (n:nat)
  : Lemma (ensures boolean_sorts (boolean_domain n)) (decreases n)
  = if n = 0 then () else lemma_boolean_domain (n - 1)

let and_decl (n:nat) : func_decl =
  { decl_name = "and"; domain = boolean_domain n; range = bool_sort; interp = Some op_and; int_params = [] }

let or_decl (n:nat) : func_decl =
  { decl_name = "or"; domain = boolean_domain n; range = bool_sort; interp = Some op_or; int_params = [] }

let lemma_canonical_decls (s:sort) (n:nat)
  : Lemma (canonical_true true_decl /\ canonical_false false_decl /\ canonical_not not_decl /\
           canonical_eq (eq_decl s) /\ canonical_and (and_decl n) /\ canonical_or (or_decl n))
  = lemma_boolean_domain n
