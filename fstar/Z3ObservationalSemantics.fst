module Z3ObservationalSemantics

open Z3AstTheory

(* A denotation is only required on the caller's scoped expression domain.
   The carrier may contain ghost functions; no executable equality is used. *)
type denotation (value:Type) (domain:expr -> bool) =
  e:expr{domain e} -> GTot value

let observations_agree (#value:Type) (#domain:expr -> bool)
                       (vtrue:value) (denote:denotation value domain)
                       (a:expr{domain a}) (b:expr{domain b}) : prop =
  get_sort a == get_sort b /\
  (if get_sort a = bool_sort then (denote a == vtrue <==> denote b == vtrue)
   else denote a == denote b)

let boolean_value (#value:Type) (vtrue vfalse v:value) : prop =
  v == vtrue \/ v == vfalse

let boolean_model (#value:Type) (#domain:expr -> bool)
                  (vtrue vfalse:value) (denote:denotation value domain) : prop =
  forall (e:expr{domain e}).
    get_sort e == bool_sort ==> boolean_value vtrue vfalse (denote e)

let lemma_values (#value:Type) (#domain:expr -> bool)
                 (vtrue vfalse:value) (denote:denotation value domain)
                 (a:expr{domain a}) (b:expr{domain b})
  : Lemma (requires observations_agree vtrue denote a b /\
                    (get_sort a == bool_sort ==>
                     boolean_value vtrue vfalse (denote a) /\
                     boolean_value vtrue vfalse (denote b)))
          (ensures denote a == denote b)
  = ()

let lemma_from_values (#value:Type) (#domain:expr -> bool)
                      (vtrue:value) (denote:denotation value domain)
                      (a:expr{domain a}) (b:expr{domain b})
  : Lemma (requires get_sort a == get_sort b /\ denote a == denote b)
          (ensures observations_agree vtrue denote a b)
  = ()

let lemma_symmetry (#value:Type) (#domain:expr -> bool)
                   (vtrue:value) (denote:denotation value domain)
                   (a:expr{domain a}) (b:expr{domain b})
  : Lemma (requires observations_agree vtrue denote a b)
          (ensures observations_agree vtrue denote b a)
  = ()

let lemma_transitivity (#value:Type) (#domain:expr -> bool)
                       (vtrue:value) (denote:denotation value domain)
                       (a:expr{domain a}) (b:expr{domain b}) (c:expr{domain c})
  : Lemma (requires observations_agree vtrue denote a b /\ observations_agree vtrue denote b c)
          (ensures observations_agree vtrue denote a c)
  = ()

let lemma_mp (#value:Type) (#domain:expr -> bool)
             (vtrue:value) (denote:denotation value domain)
             (a:expr{domain a}) (b:expr{domain b})
  : Lemma (requires observations_agree vtrue denote a b /\ denote a == vtrue)
          (ensures denote b == vtrue)
  = ()

let lemma_equisatisfiable (#value #state:Type) (#domain:expr -> bool)
                         (vtrue:value) (denote:state -> denotation value domain)
                         (a:expr{domain a}) (b:expr{domain b})
  : Lemma (requires forall (rho:state). observations_agree vtrue (denote rho) a b)
          (ensures (exists (rho:state). denote rho a == vtrue) <==>
                   (exists (rho:state). denote rho b == vtrue))
  = ()
