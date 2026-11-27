module Z3BooleanRewrite

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module B = Z3BoundedBoolEquiv
module N = Z3BooleanNormalForm
module C = Z3CanonicalOps
module Syntax = Z3ClauseSyntax

include Z3BooleanRewriteSyntax

let connective_holds (op:connective) (i:interpretation value) (rho:env value)
                     (args:list expr) : prop =
  match op with
  | Conjunction -> conj_holds i rho args
  | Disjunction -> clause_holds i rho args

(* The canonical connective built here holds exactly when its arguments do. *)
let lemma_connective_holds (op:connective) (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (requires and_sound i /\ or_sound i)
          (ensures lit_true i rho (App (connective_decl op args) args) <==> connective_holds op i rho args)
  = lemma_connective_decl op args

let rec lemma_connective_append (op:connective) (i:interpretation value)
                                 (rho:env value) (xs ys:list expr)
  : Lemma
      (connective_holds op i rho (xs @ ys) <==>
       (if op = Conjunction
        then connective_holds op i rho xs /\ connective_holds op i rho ys
        else connective_holds op i rho xs \/ connective_holds op i rho ys))
      (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: rest -> lemma_connective_append op i rho rest ys

let rec lemma_flatten_expr_sound (op:connective) (i:interpretation value)
                                 (rho:env value) (e:expr)
  : Lemma (requires and_sound i /\ or_sound i)
          (ensures connective_holds op i rho (flatten_expr op e) <==> lit_true i rho e)
          (decreases e)
  = match e with
    | App f args ->
      if connective_app op f args then (
        lemma_flatten_args_sound op i rho args;
        match op with Conjunction | Disjunction -> ())
    | _ -> ()

and lemma_flatten_args_sound (op:connective) (i:interpretation value)
                             (rho:env value) (args:list expr)
  : Lemma (requires and_sound i /\ or_sound i)
          (ensures connective_holds op i rho (flatten_args op args) <==>
                   connective_holds op i rho args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_flatten_expr_sound op i rho a;
      lemma_flatten_args_sound op i rho rest;
      lemma_connective_append op i rho (flatten_expr op a) (flatten_args op rest)

let lemma_flatten_rewrite_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires boolean_model i /\ and_sound i /\ or_sound i /\
                    flatten_rewrite s == Some t)
          (ensures eval i s rho == eval i t rho)
  = match s with
    | App f args ->
      let op = if f.decl_name = "and" then Conjunction else Disjunction in
      lemma_flatten_args_sound op i rho args;
      (match op with Conjunction | Disjunction -> ());
      (match eval i s rho, eval i t rho with
       | VBool _, VBool _ -> ()
       | _, _ -> ())
    | _ -> ()

let bool_value (v:value) : bool =
  match v with VBool b -> b | _ -> false

(* Ghost: the truth of an atom under the (ghost) interpretation. Lemmas
   about the executable normal-form and row checks are applied to it
   through `B.freeze`, an executable valuation agreeing on the atoms. *)
let valuation (i:interpretation value) (rho:env value) : expr -> GTot bool =
  fun e -> bool_value (eval i e rho)

let ite_sound (i:interpretation value) : prop =
  forall (c t e:expr) (rho:env value).
    {:pattern (eval i (App boolean_ite_decl [c; t; e]) rho)}
    boolean_args [c; t; e] ==>
    eval i (App boolean_ite_decl [c; t; e]) rho ==
      (if bool_value (eval i c rho) then eval i t rho else eval i e rho)

let xor_sound (i:interpretation value) : prop =
  forall (a b:expr) (rho:env value).
    {:pattern (eval i (App boolean_xor_decl [a; b]) rho)}
    boolean_args [a; b] ==>
    eval i (App boolean_xor_decl [a; b]) rho ==
      VBool (bool_value (eval i a rho) <> bool_value (eval i b rho))

let boolean_rewrite_model (i:interpretation value) : prop =
  boolean_model i /\ not_sound i /\ and_sound i /\ or_sound i /\
  implies_sound i /\ eq_sound i /\ true_sound i /\ false_sound i /\ ite_sound i /\ xor_sound i

let rec lemma_boolean_cut_sound (boundaries:list expr) (depth:nat)
                                (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires boolean_rewrite_model i /\ get_sort e == bool_sort)
          (ensures B.geval (valuation i rho) (boolean_cut boundaries depth e) ==
                   bool_value (eval i e rho))
          (decreases e) =
  if reflexive_equality e then (
    match e with App _ [_; _] -> () | _ -> ())
  else if mem e boundaries then ()
  else match e with
  | App f args ->
    lemma_native_bool_op f args;
    (match native_bool_op f args with
     | B.BTrue | B.BFalse -> ()
     | B.BNary B.Xor ->
       assert (f == boolean_xor_decl /\ boolean_args args);
       (match args with
        | [a; b] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho a;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho b)
        | _ -> ())
     | B.BNary op ->
       if depth > 0 then (
         lemma_boolean_cut_args_sound boundaries (depth - 1) i rho args;
         match op with B.And | B.Or | B.Xor -> ())
     | B.BNot ->
       (match args with
        | [a] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho a;
            match eval i a rho, eval i e rho with VBool _, VBool _ -> () | _, _ -> ())
        | _ -> ())
     | B.BImplies | B.BEq ->
       (match args with
        | [a; b] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho a;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho b;
            match eval i a rho, eval i b rho, eval i e rho with
            | VBool _, VBool _, VBool _ -> () | _, _, _ -> ())
        | _ -> ())
     | B.BIte ->
       assert (f == boolean_ite_decl /\ boolean_args args);
       (match args with
        | [c; t; f] ->
          if depth > 0 then (
            lemma_boolean_cut_sound boundaries (depth - 1) i rho c;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho t;
            lemma_boolean_cut_sound boundaries (depth - 1) i rho f;
            B.lemma_boolean_ite_geval (valuation i rho)
              (boolean_cut boundaries (depth - 1) c)
              (boolean_cut boundaries (depth - 1) t)
              (boolean_cut boundaries (depth - 1) f);
            match eval i c rho, eval i t rho, eval i f rho with
            | VBool _, VBool _, VBool _ -> () | _, _, _ -> ())
        | _ -> ())
     | _ -> ())
  | _ -> ()

and lemma_boolean_cut_args_sound (boundaries:list expr) (depth:nat)
                                 (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (requires boolean_rewrite_model i /\ boolean_args args)
          (ensures
            (B.geval_args (valuation i rho) B.And (boolean_cut_args boundaries depth args) == true
             <==> conj_holds i rho args) /\
            (B.geval_args (valuation i rho) B.Or (boolean_cut_args boundaries depth args) == true
             <==> clause_holds i rho args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_boolean_cut_sound boundaries depth i rho a;
    lemma_boolean_cut_args_sound boundaries depth i rho rest;
    match eval i a rho with VBool _ -> () | _ -> ()

let lemma_boolean_equiv_sound (depth width:nat) (i:interpretation value)
                              (rho:env value) (s t:expr)
  : Lemma (requires boolean_rewrite_model i /\ boolean_equiv depth width s t)
          (ensures eval i s rho == eval i t rho) =
  let boundaries = B.unique (B.intersect (boolean_nodes depth s) (boolean_nodes depth t)) in
  let cs = boolean_cut boundaries depth s in
  let ct = boolean_cut boundaries depth t in
  let atoms = B.unique (B.support cs @ B.support ct) in
  if structural_boolean_equiv s t then (
    let ss = boolean_cut [] (boolean_height s) s in
    let st = boolean_cut [] (boolean_height t) t in
    B.lemma_freeze_pair (valuation i rho) ss st;
    N.lemma_equivalent_sound (B.freeze (valuation i rho) (B.support ss @ B.support st)) ss st;
    lemma_boolean_cut_sound [] (boolean_height s) i rho s;
    lemma_boolean_cut_sound [] (boolean_height t) i rho t)
  else (
    if N.equivalent cs ct then (
      B.lemma_freeze_pair (valuation i rho) cs ct;
      N.lemma_equivalent_sound (B.freeze (valuation i rho) (B.support cs @ B.support ct)) cs ct)
    else (
      B.lemma_mem_append (B.support cs) (B.support ct);
      B.lemma_unique_mem (B.support cs @ B.support ct);
      assert (B.agree_outside atoms (fun _ -> false) (valuation i rho) cs ct);
      B.lemma_check_rows_sound_ghost atoms (fun _ -> false) (valuation i rho) cs ct);
    lemma_boolean_cut_sound boundaries depth i rho s;
    lemma_boolean_cut_sound boundaries depth i rho t);
  match eval i s rho, eval i t rho with VBool _, VBool _ -> () | _, _ -> ()

let lemma_boolean_search_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires boolean_rewrite_model i /\ boolean_search s t)
          (ensures eval i s rho == eval i t rho) =
  let cs = boolean_cut [] (boolean_height s) s in
  let ct = boolean_cut [] (boolean_height t) t in
  let v = B.freeze (valuation i rho) (B.support cs @ B.support ct) in
  B.lemma_freeze_pair (valuation i rho) cs ct;
  N.lemma_shannon_sound v 7 (N.normalize_context 2 cs) (N.normalize_context 2 ct);
  N.lemma_normalize_context_sound v 2 cs;
  N.lemma_normalize_context_sound v 2 ct;
  lemma_boolean_cut_sound [] (boolean_height s) i rho s;
  lemma_boolean_cut_sound [] (boolean_height t) i rho t;
  match eval i s rho, eval i t rho with VBool _, VBool _ -> () | _, _ -> ()
