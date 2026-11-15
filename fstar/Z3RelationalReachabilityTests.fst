module Z3RelationalReachabilityTests

open Z3AstTheory
open Z3UnifiedProofSyntax
module Reach = Z3RelationalReachability
module L = FStar.List.Tot

let atom (name:string) : expr =
  App { decl_name = name; domain = []; range = bool_sort; interp = None; int_params = [] } []

let a = atom "a"
let b = atom "b"
let c = atom "c"
let d = atom "d"
let edges = [Equal c d; Observational b c; Equal b a]

let relation (denote:expr -> GTot int) (x y:expr) : prop =
  denote x == denote y

let observation_path (denote:expr -> GTot int)
  : Lemma (requires denote a == denote b /\ denote b == denote c /\ denote c == denote d)
          (ensures L.mem d (reachable 3 Observation edges [a]) /\ denote a == denote d) =
  assert_norm (L.mem d (reachable 3 Observation edges [a]));
  Reach.lemma_reachable (relation denote) Observation a edges [a] 3;
  FStar.List.Tot.Properties.mem_memP d (reachable 3 Observation edges [a])

let missing_and_wrong_relation_edges ()
  : Lemma (not (L.mem d (reachable 2 Observation edges [a])) /\
           not (L.mem d (reachable 3 Equality edges [a]))) =
  assert_norm (not (L.mem d (reachable 2 Observation edges [a])) /\
               not (L.mem d (reachable 3 Equality edges [a])))

let matching_observation_edge (denote:expr -> GTot int)
  : Lemma (requires denote a == denote b /\ denote b == denote c /\ denote c == denote d)
          (ensures matching Observation b c edges /\ denote b == denote c /\
                   not (matching Equality b c edges) /\ not (matching Observation c b edges)) =
  assert_norm (matching Observation b c edges /\ not (matching Equality b c edges) /\
               not (matching Observation c b edges));
  Reach.lemma_matching (relation denote) Observation b c edges

let matching_arguments (denote:expr -> GTot int)
  : Lemma (requires denote a == denote b /\ denote b == denote c /\ denote c == denote d)
          (ensures Reach.arguments_related (relation denote) [a; b; c] [a; c; d] /\
                   not (arguments_match Observation [a; b] [a] edges) /\
                   not (arguments_match Equality [b] [c] edges)) =
  assert_norm (arguments_match Observation [a; b; c] [a; c; d] edges /\
               not (arguments_match Observation [a; b] [a] edges) /\
               not (arguments_match Equality [b] [c] edges));
  Reach.lemma_arguments (relation denote) Observation [a; b; c] [a; c; d] edges
