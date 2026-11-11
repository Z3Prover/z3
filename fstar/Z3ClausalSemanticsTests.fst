module Z3ClausalSemanticsTests

open Z3AstTheory
open Z3OperatorTags
module C = Z3CanonicalOps
module CS = Z3ClausalSemantics
module P = Z3ProofTheory

let rec truth (atoms:CS.valuation) (e:expr) : GTot bool (decreases e) =
  match e with
  | App f [] ->
    if C.canonical_true f then true
    else if C.canonical_false f then false
    else atoms e
  | App f [a] -> if C.canonical_not f then not (truth atoms a) else atoms e
  | _ -> atoms e

let lemma_negation (atoms:CS.valuation) (e a:expr)
  : Lemma (requires P.is_not e == Some a)
          (ensures truth atoms e == not (truth atoms a))
  = match e with App _ [_] -> () | _ -> ()

let lemma_complement_model (atoms:CS.valuation)
  : Lemma (CS.complement_model (truth atoms))
  = let pair (a b:expr)
      : Lemma (CS.complementary a b /\ truth atoms a ==> not (truth atoms b))
      = if P.is_not a = Some b then lemma_negation atoms a b
        else if P.is_not b = Some a then lemma_negation atoms b a
        else match a, b with App _ [], App _ [] -> () | _, _ -> () in
    FStar.Classical.forall_intro_2 pair

let atom (name:string) : expr =
  App { decl_name = name; domain = []; range = bool_sort;
        interp = None; int_params = [] } []

let p = atom "p"
let q = atom "q"
let np = App C.not_decl [p]
let true_e = App { decl_name = "true"; domain = []; range = bool_sort;
                  interp = Some op_true; int_params = [] } []
let false_e = App { decl_name = "false"; domain = []; range = bool_sort;
                   interp = Some op_false; int_params = [] } []

let repeated_resolution (atoms:CS.valuation)
  : Lemma (requires CS.clause_holds (truth atoms) [p; p; q] /\ truth atoms np)
          (ensures truth atoms q)
  = lemma_complement_model atoms;
    CS.lemma_unit_resolution (truth atoms) [p; p; q] [np];
    assert_norm (CS.unit_resolve [p; p; q] [np] == [q])

let function_atoms (a b:int -> GTot int) (e:expr) : GTot bool =
  if e = p then
    FStar.IndefiniteDescription.strong_excluded_middle (forall (x:int). a x == b x)
  else true

let ghost_function_resolution (a b:int -> GTot int)
  : Lemma (requires a 0 <> b 0) (ensures truth (function_atoms a b) q)
  = repeated_resolution (function_atoms a b)

let distinct_function_witness ()
  : Lemma (truth (function_atoms (fun _ -> 0) (fun _ -> 1)) q)
  = ghost_function_resolution (fun _ -> 0) (fun _ -> 1)

let rejects_inconsistent_valuation ()
  : Lemma (not (CS.complement_model (fun _ -> true)))
  = assert_norm (CS.complementary true_e false_e)

let complementary_controls ()
  : Lemma (CS.unit_resolve [false_e; p; false_e] [true_e] == [p] /\
           not (CS.complementary
             (App { C.not_decl with interp = None } [p]) p))
  = assert_norm (CS.unit_resolve [false_e; p; false_e] [true_e] == [p] /\
                not (CS.complementary
                  (App { C.not_decl with interp = None } [p]) p))
