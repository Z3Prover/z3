(* Concrete evaluation tests for the fresh-bit model extension
   (`Z3BvFresh.extend`, `extend_context`, `number`), the literal retraction
   (`Z3BvFreshModel.retract`) and the scoped witness (`Z3ScopedModel.witness`).

   The native test harness (`fstar/tools/test_native_bridge.ml`, tests
   `checked-fresh-bit-model-extension`, `checked-fresh-bit-context-extension`
   and `scoped-model-extension`) used to run these semantic definitions as
   extracted code. `Z3AstTheory.interpretation` and `eval` are ghost now and
   are erased by extraction, so the facts below, on the same fixtures, are
   checked here by evaluation in F*. The native tests keep their executable
   parts: context and freshness checks, retraction with the bit value
   computed here, the typing predicates and the step checks. *)
module Z3BvFreshTests

open Z3AstTheory
open Z3ValueTheory
module F = Z3BvFresh
module M = Z3BvFreshModel
module SM = Z3ScopedModel
module R = Z3ResolutionProofTheory
module BV = Z3BvLemma
module W = Z3BvWord
module L = FStar.List.Tot

let symbol (name:string) (range:sort) : func_decl =
  { decl_name = name; domain = []; range = range; interp = None; int_params = [] }

let rec number (vs:list value) : int =
  match vs with
  | [] -> 0
  | VBool b :: rest -> (if b then 1 else 0) + 2 * number rest
  | _ -> 0

let project (_:pos) (v:value) : int = match v with VInt n -> n | _ -> 0

let constructor_of (symbols:list func_decl) : func_decl =
  match W.word (F.atoms symbols) with App f _ -> f | _ -> symbol "unexpected" bool_sort

let booleans (names:list string) : list func_decl = L.map (fun n -> symbol n bool_sort) names

let reconstruction (width:pos) (name:string) (names:list string) : F.reconstruction =
  { F.width = width; F.original = symbol name (BV.bv_sort width);
    F.constructor = constructor_of (booleans names); F.symbols = booleans names }

let equation (r:F.reconstruction) : expr = R.mk_eq_expr (F.source r) (F.word r)

let zero_env : env value = fun _ -> VInt 0

(* --- checked-fresh-bit-model-extension -------------------------------------- *)

(* The native base model: `mkbv` is the number of its bits, `=` compares
   integers, the original constant has the value `n`, other constants are
   false and other applications 37. *)
let base_model (r:F.reconstruction) (n:int) : interpretation value = {
  interp_app = (fun f vs ->
    if f.interp = Some BV.op_mkbv then VInt (number vs)
    else if f.interp = Some op_eq then
      (match vs with [VInt a; VInt b] -> VBool (a = b) | _ -> VInt (-1))
    else VInt (-1));
  uninterp_app = (fun f vs ->
    if f = r.F.original then VInt n
    else match vs with [] -> VBool false | _ -> VInt 37);
  interp_quant = (fun _ _ _ -> VInt (-1)) }

let names1 : list string = ["ordinary-name-0"]
let names3 : list string = ["ordinary-name-0"; "ordinary-name-1"; "ordinary-name-2"]
let names8 : list string =
  ["ordinary-name-0"; "ordinary-name-1"; "ordinary-name-2"; "ordinary-name-3";
   "ordinary-name-4"; "ordinary-name-5"; "ordinary-name-6"; "ordinary-name-7"]

let first_symbol : f:func_decl{is_uninterp_decl f} = symbol "ordinary-name-0" bool_sort

(* The extension reconstructs the original value from its bits, satisfies
   the reconstruction equation, and leaves an unrelated constant and a
   non-nullary application of a bit symbol unchanged. *)
let extension_holds (w:pos) (names:list string) (n:int) : prop =
  let r = reconstruction w "v" names in
  let ext = F.extend r (base_model r n) project in
  eval ext (F.source r) zero_env == VInt n /\ eval ext (F.word r) zero_env == VInt n /\
  eval ext (equation r) zero_env == VBool true /\
  eval ext (App (symbol "unrelated" bool_sort) []) zero_env == VBool false /\
  ext.uninterp_app first_symbol [VBool true] == VInt 37

let model_extension_1 () : Lemma (extension_holds 1 names1 0 /\ extension_holds 1 names1 1)
  = assert_norm (extension_holds 1 names1 0 /\ extension_holds 1 names1 1)

let model_extension_3 ()
  : Lemma (extension_holds 3 names3 0 /\ extension_holds 3 names3 1 /\
           extension_holds 3 names3 5 /\ extension_holds 3 names3 7)
  = assert_norm (extension_holds 3 names3 0 /\ extension_holds 3 names3 1 /\
                 extension_holds 3 names3 5 /\ extension_holds 3 names3 7)

let model_extension_8 ()
  : Lemma (extension_holds 8 names8 0 /\ extension_holds 8 names8 128 /\
           extension_holds 8 names8 165 /\ extension_holds 8 names8 255)
  = assert_norm (extension_holds 8 names8 0 /\ extension_holds 8 names8 128 /\
                 extension_holds 8 names8 165 /\ extension_holds 8 names8 255)

(* --- checked-fresh-bit-context-extension ------------------------------------ *)

let rv : F.reconstruction = reconstruction 3 "v" ["p"; "q"; "r"]
let sw : F.reconstruction = reconstruction 3 "w" ["s"; "t"; "u"]
let context_inputs : list expr = [R.mk_eq_expr (F.source rv) (F.source rv)]
let context_formulas : list expr = [equation rv; R.mk_eq_expr (F.word sw) (F.source sw)]

(* Scalars only here, so identity is decidable. *)
let scalar_eq (a b:value) : bool =
  match a, b with
  | VInt x, VInt y -> x = y
  | VBool x, VBool y -> x = y
  | _, _ -> false

let context_base : interpretation value = {
  interp_app = (fun f vs ->
    if f.interp = Some op_true then VBool true
    else if f.interp = Some op_false then VBool false
    else if f.interp = Some op_eq then
      (match vs with [a; b] -> VBool (scalar_eq a b) | _ -> VInt (-1))
    else if f.interp = Some BV.op_mkbv then VInt (number vs)
    else VInt (-1));
  uninterp_app = (fun f vs ->
    if f = rv.F.original then VInt 5
    else if f = sw.F.original then VInt 2
    else match vs with [] -> VBool false | _ -> VInt 37);
  interp_quant = (fun _ bs body -> body (L.map (fun _ -> VBool true) bs)) }

let first : expr = App (L.hd rv.F.symbols) []
let applied : expr = App (L.hd rv.F.symbols) [Var 0 bool_sort]
let quantified : expr = Quantifier Forall_k [bool_sort] bool_sort (R.mk_eq_expr first (Var 0 bool_sort))

(* The native context check accepts these two reconstructions; the batch
   extension keeps the inputs and satisfies both orientations. *)
let context_extension ()
  : Lemma (Some? (M.check_context context_inputs context_formulas) /\
           (let rs = Some?.v (M.check_context context_inputs context_formulas) in
            let ext = F.extend_context rs context_base project in
            eval_args ext context_inputs zero_env == eval_args context_base context_inputs zero_env /\
            eval ext (equation rv) zero_env == VBool true /\
            eval ext (R.mk_eq_expr (F.word sw) (F.source sw)) zero_env == VBool true))
  = assert_norm (Some? (M.check_context context_inputs context_formulas) /\
                 (let rs = Some?.v (M.check_context context_inputs context_formulas) in
                  let ext = F.extend_context rs context_base project in
                  eval_args ext context_inputs zero_env == eval_args context_base context_inputs zero_env /\
                  eval ext (equation rv) zero_env == VBool true /\
                  eval ext (R.mk_eq_expr (F.word sw) (F.source sw)) zero_env == VBool true))

(* The bit value of the single extension is 5 (the native test retracts with
   this literal), and retraction preserves evaluation in the extension. *)
let retraction ()
  : Lemma (F.number rv context_base project == 5 /\
           M.retract rv.F.symbols 5 first == R.true_expr /\
           (let one = F.extend rv context_base project in
            eval one first zero_env == eval context_base (M.retract rv.F.symbols 5 first) zero_env /\
            eval one (F.word rv) zero_env == eval context_base (M.retract rv.F.symbols 5 (F.word rv)) zero_env /\
            eval one applied zero_env == eval context_base (M.retract rv.F.symbols 5 applied) zero_env /\
            eval one quantified zero_env == eval context_base (M.retract rv.F.symbols 5 quantified) zero_env))
  = assert_norm (F.number rv context_base project == 5 /\
                 M.retract rv.F.symbols 5 first == R.true_expr /\
                 (let one = F.extend rv context_base project in
                  eval one first zero_env == eval context_base (M.retract rv.F.symbols 5 first) zero_env /\
                  eval one (F.word rv) zero_env == eval context_base (M.retract rv.F.symbols 5 (F.word rv)) zero_env /\
                  eval one applied zero_env == eval context_base (M.retract rv.F.symbols 5 applied) zero_env /\
                  eval one quantified zero_env == eval context_base (M.retract rv.F.symbols 5 quantified) zero_env))

(* --- scoped-model-extension --------------------------------------------------- *)

let scope : list sort = [bool_sort; SM.int_sort]
let scoped_env : env value = SM.default_environment scope
let bvar : expr = Var 0 bool_sort
let ivar : expr = Var 1 SM.int_sort

let scoped_witness ()
  : Lemma (eval SM.witness bvar scoped_env == VBool false /\
           eval SM.witness ivar scoped_env == VInt 0 /\
           eval SM.witness bvar zero_env == VInt 0)
  = assert_norm (eval SM.witness bvar scoped_env == VBool false /\
                 eval SM.witness ivar scoped_env == VInt 0 /\
                 eval SM.witness bvar zero_env == VInt 0)

(* Reserved Boolean names as fresh bits: still ordinary uninterpreted atoms. *)
let rs4 : F.reconstruction = reconstruction 4 "v" ["true"; "false"; "and"; "or"]
let scoped_equations : list expr = [R.mk_eq_expr (F.word rs4) (F.source rs4)]

let scoped_base : interpretation value = {
  SM.witness with
  interp_app = (fun f vs ->
    if f.interp = Some BV.op_mkbv then VInt (number vs) else SM.witness.interp_app f vs);
  uninterp_app = (fun f vs ->
    if f = rs4.F.original then VInt 6 else SM.witness.uninterp_app f vs) }

let scoped_quantified : expr =
  Quantifier Forall_k scope bool_sort (R.mk_eq_expr (Var 0 SM.int_sort) (Var 0 SM.int_sort))

let scoped_extension ()
  : Lemma (Some? (F.check_context [] scoped_equations) /\
           (let ext = F.extend_context (Some?.v (F.check_context [] scoped_equations)) scoped_base project in
            eval ext (F.source rs4) scoped_env == VInt 6 /\ eval ext (F.word rs4) scoped_env == VInt 6 /\
            eval ext (L.hd scoped_equations) scoped_env == VBool true /\
            eval ext (App (L.index rs4.F.symbols 0) []) scoped_env == VBool false /\
            eval ext (App (L.index rs4.F.symbols 1) []) scoped_env == VBool true /\
            eval ext R.true_expr scoped_env == VBool true /\
            eval ext R.false_expr scoped_env == VBool false /\
            SM.scalar_typed (get_sort bvar) (eval ext bvar scoped_env) /\
            SM.scalar_typed (get_sort ivar) (eval ext ivar scoped_env) /\
            SM.scalar_typed (get_sort R.true_expr) (eval ext R.true_expr scoped_env) /\
            SM.scalar_typed (get_sort R.false_expr) (eval ext R.false_expr scoped_env) /\
            SM.scalar_typed (get_sort scoped_quantified) (eval ext scoped_quantified scoped_env) /\
            SM.scalar_typed (get_sort (F.word rs4)) (eval ext (F.word rs4) scoped_env)))
  = assert_norm (Some? (F.check_context [] scoped_equations) /\
           (let ext = F.extend_context (Some?.v (F.check_context [] scoped_equations)) scoped_base project in
            eval ext (F.source rs4) scoped_env == VInt 6 /\ eval ext (F.word rs4) scoped_env == VInt 6 /\
            eval ext (L.hd scoped_equations) scoped_env == VBool true /\
            eval ext (App (L.index rs4.F.symbols 0) []) scoped_env == VBool false /\
            eval ext (App (L.index rs4.F.symbols 1) []) scoped_env == VBool true /\
            eval ext R.true_expr scoped_env == VBool true /\
            eval ext R.false_expr scoped_env == VBool false /\
            SM.scalar_typed (get_sort bvar) (eval ext bvar scoped_env) /\
            SM.scalar_typed (get_sort ivar) (eval ext ivar scoped_env) /\
            SM.scalar_typed (get_sort R.true_expr) (eval ext R.true_expr scoped_env) /\
            SM.scalar_typed (get_sort R.false_expr) (eval ext R.false_expr scoped_env) /\
            SM.scalar_typed (get_sort scoped_quantified) (eval ext scoped_quantified scoped_env) /\
            SM.scalar_typed (get_sort (F.word rs4)) (eval ext (F.word rs4) scoped_env)))

(* --- Mutation controls: the evaluation is discriminating ----------------------- *)

[@@expect_failure [19]]
let wrong_reconstruction ()
  : Lemma (let r = reconstruction 3 "v" names3 in
           eval (F.extend r (base_model r 5) project) (F.word r) zero_env == VInt 4)
  = assert_norm (let r = reconstruction 3 "v" names3 in
                 eval (F.extend r (base_model r 5) project) (F.word r) zero_env == VInt 4)

[@@expect_failure [19]]
let wrong_bit_value () : Lemma (F.number rv context_base project == 4)
  = assert_norm (F.number rv context_base project == 4)

[@@expect_failure [19]]
let reserved_name_is_literal ()
  : Lemma (let ext = F.extend_context (Some?.v (F.check_context [] scoped_equations)) scoped_base project in
           eval ext (App (symbol "true" bool_sort) []) scoped_env == VBool true)
  = assert_norm (let ext = F.extend_context (Some?.v (F.check_context [] scoped_equations)) scoped_base project in
                 eval ext (App (symbol "true" bool_sort) []) scoped_env == VBool true)
