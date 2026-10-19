module Z3BvLemma

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
module D = Z3Definitions
module L = FStar.List.Tot
module U = FStar.UInt

let op_and : decl_kind = 100
let op_or : decl_kind = 101
let op_xor : decl_kind = 102
let op_not : decl_kind = 103
let op_add : decl_kind = 104
let op_mul : decl_kind = 105
let op_sub : decl_kind = 106
let op_neg : decl_kind = 107
let op_numeral : decl_kind = 108

let bv_sort (width:int) : sort = BaseSort ("BV" ^ Prims.string_of_int width)

let numeral (e:expr) : option (pos & int) =
  match e with
  | App f [] ->
    (match f.int_params with
     | [width; n] ->
       if width > 0 && width <= 4096 && f.range = bv_sort width &&
          f.domain = [] && f.interp = Some op_numeral && n >= 0 && n < pow2 width
       then Some (width, n) else None
     | _ -> None)
  | _ -> None

let operation (f:func_decl) (args:list expr) : option (pos & decl_kind) =
  match f.int_params, f.interp with
  | [width], Some op ->
    if width > 0 && width <= 4096 && f.range = bv_sort width &&
       sorts_match args f.domain && f.domain = L.map (fun _ -> bv_sort width) args &&
       (((op = op_not || op = op_neg) && L.length args = 1) ||
        ((op = op_and || op = op_or || op = op_xor || op = op_add ||
          op = op_mul || op = op_sub) && L.length args = 2))
    then Some (width, op) else None
  | _, _ -> None

let calculate (width:pos) (op:decl_kind) (xs:list (U.uint_t width)) : U.uint_t width =
  match xs with
  | [x] -> if op = op_not then U.lognot x else U.sub_mod 0 x
  | [x; y] ->
    if op = op_and then U.logand x y
    else if op = op_or then U.logor x y
    else if op = op_xor then U.logxor x y
    else if op = op_add then U.add_mod x y
    else if op = op_mul then U.mul_mod x y
    else U.sub_mod x y
  | _ -> 0

let words (width:pos) (project:pos -> value -> int) (vs:list value) : list (U.uint_t width) =
  L.map (fun v -> U.to_uint_t width (project width v)) vs

(* Closed terms avoid imposing bit-vector typing on arbitrary binder environments. *)
let bv_model (i:interpretation value) (project:pos -> value -> int) : prop =
  (forall (width:pos) (a b:expr) (rho:env value).
    D.scoped [] a /\ D.scoped [] b /\ get_sort a == bv_sort width /\ get_sort b == bv_sort width ==>
    ((eval i a rho == eval i b rho <==> project width (eval i a rho) == project width (eval i b rho)) /\
     0 <= project width (eval i a rho) /\ project width (eval i a rho) < pow2 width)) /\
  (forall (e:expr) (rho:env value) (width:pos) (n:int).
    numeral e == Some (width, n) ==> project width (eval i e rho) == n) /\
  (forall (f:func_decl) (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
    D.scoped [] (App f args) /\ operation f args == Some (width, op) ==>
    project width (eval i (App f args) rho) ==
    calculate width op (words width project (eval_args i args rho)))

let literal (width:pos) (n:int) : expr =
  App { decl_name = "bv"; domain = []; range = bv_sort width;
        interp = Some op_numeral; int_params = [width; n] } []

let lemma_literal (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                  (width:pos) (n:int)
  : Lemma (requires bv_model i project /\ width <= 4096 /\ 0 <= n /\ n < pow2 width)
          (ensures project width (eval i (literal width n) rho) == n)
  = assert (numeral (literal width n) == Some (width, n))

let lemma_word (i:interpretation value) (rho:env value) (project:pos -> value -> int)
               (width:pos) (e:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] e /\ get_sort e == bv_sort width)
          (ensures 0 <= project width (eval i e rho) /\
                   project width (eval i e rho) < pow2 width /\
                   U.to_uint_t width (project width (eval i e rho)) == project width (eval i e rho))
  = assert (0 <= project width (eval i e rho) /\ project width (eval i e rho) < pow2 width);
    FStar.Math.Lemmas.small_mod (project width (eval i e rho)) (pow2 width)

let lemma_operation (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                    (f:func_decl) (args:list expr) (width:pos) (op:decl_kind)
  : Lemma (requires bv_model i project /\ D.scoped [] (App f args) /\
                    operation f args == Some (width, op))
          (ensures project width (eval i (App f args) rho) ==
                   calculate width op (words width project (eval_args i args rho)))
  = ()

let lemma_reflect (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                  (width:pos) (a b:expr)
  : Lemma (requires bv_model i project /\ D.scoped [] a /\ D.scoped [] b /\
                    get_sort a == bv_sort width /\ get_sort b == bv_sort width /\
                    project width (eval i a rho) == project width (eval i b rho))
          (ensures eval i a rho == eval i b rho)
  = ()

let rec constants (width:pos) (args:list expr) : Tot (option (list (U.uint_t width))) (decreases args) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match numeral a, constants width rest with
     | Some (w, n), Some ns -> if w = width then Some (n :: ns) else None
     | _, _ -> None)

let simple (width:pos) (op:decl_kind) (args:list expr) : option expr =
  match args with
  | [App f [x]] ->
    if (op = op_not || op = op_neg) && operation f [x] = Some (width, op)
    then Some x else None
  | [x; y] ->
    if x = y && (op = op_and || op = op_or) then Some x
    else if x = y && (op = op_xor || op = op_sub) then Some (literal width 0)
    else (match numeral y with
          | Some (w, n) ->
            if w <> width then None
            else if n = 0 && (op = op_or || op = op_xor || op = op_add || op = op_sub) then Some x
            else if n = 0 && (op = op_and || op = op_mul) then Some y
            else if n = 1 && op = op_mul then Some x
            else None
          | None -> None)
  | _ -> None

let comparison (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else (match numeral a, numeral b with
          | Some (width, n), Some (width', m) ->
            if width = width' then Some (if n = m then true_expr else false_expr) else None
          | _, _ -> None)
  | _ -> None

let rewrite (e:expr) : option expr =
  if not (D.scoped [] e) then None
  else if Some? (comparison e) then comparison e
  else match e with
  | App f args ->
    (match operation f args with
     | Some (width, op) ->
       (match constants width args with
        | Some ns -> Some (literal width (calculate width op ns))
        | None -> simple width op args)
     | None -> None)
  | _ -> None

let rec lemma_constants (i:interpretation value) (rho:env value)
                        (project:pos -> value -> int) (width:pos) (args:list expr)
                        (ns:list (U.uint_t width))
  : Lemma (requires bv_model i project /\ constants width args == Some ns)
          (ensures words width project (eval_args i args rho) == ns)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      let w, n = Some?.v (numeral a) in
      lemma_constants i rho project width rest (Some?.v (constants width rest));
      assert (w == width);
      assert (project width (eval i a rho) == n);
      FStar.Math.Lemmas.small_mod n (pow2 width);
      assert (U.to_uint_t width (project width (eval i a rho)) == n)

let lemma_simple (i:interpretation value) (rho:env value) (project:pos -> value -> int)
                 (width:pos) (op:decl_kind) (args:list expr) (result:expr)
  : Lemma (requires bv_model i project /\ D.scoped_args [] args /\
                    L.for_all (fun a -> get_sort a = bv_sort width) args /\
                    width <= 4096 /\ simple width op args == Some result)
          (ensures get_sort result == bv_sort width /\ D.scoped [] result /\
                   calculate width op (words width project (eval_args i args rho)) ==
                   project width (eval i result rho))
  = match args with
    | [App f [x]] ->
      lemma_word i rho project width x;
      lemma_operation i rho project f [x] width op;
      lemma_word i rho project width (App f [x]);
      if op = op_not then U.lognot_self #width (project width (eval i x rho))
    | [x; y] ->
      lemma_word i rho project width x;
      lemma_word i rho project width y;
      lemma_literal i rho project width 0;
      let a = project width (eval i x rho) in
      assert (0 <= a /\ a < pow2 width);
      FStar.Math.Lemmas.small_mod a (pow2 width);
      if x = y && op = op_and then U.logand_self #width a
      else if x = y && op = op_or then U.logor_self #width a
      else if x = y && op = op_xor then U.logxor_self #width a
      else if x = y && op = op_sub then ()
      else (match numeral y with
            | Some (_, n) ->
              FStar.Math.Lemmas.small_mod n (pow2 width);
              if n = 0 && op = op_and then U.logand_lemma_1 #width a
              else if n = 0 && op = op_or then U.logor_lemma_1 #width a
              else if n = 0 && op = op_xor then U.logxor_lemma_1 #width a
              else ()
            | None -> ())
    | _ -> ()

let lemma_rewrite (i:interpretation value) (rho:env value)
                  (project:pos -> value -> int) (e result:expr)
  : Lemma (requires bv_model i project /\ Z3BooleanRewrite.boolean_rewrite_model i /\
                    rewrite e == Some result)
          (ensures eval i e rho == eval i result rho)
  = if Some? (comparison e) then
      (match e with
       | App f [a; b] ->
         let width, n = Some?.v (numeral a) in
         let _, m = Some?.v (numeral b) in
         assert (project width (eval i a rho) == n);
         assert (project width (eval i b rho) == m);
         if n = m then lemma_reflect i rho project width a b;
         (match eval i e rho, eval i result rho with
          | VBool _, VBool _ -> ()
          | _, _ -> ())
       | _ -> ())
    else match e with
    | App f args ->
      (match operation f args with
       | Some (width, op) ->
         (match constants width args with
          | Some ns ->
            lemma_constants i rho project width args ns;
            lemma_literal i rho project width (calculate width op ns)
          | None ->
            lemma_simple i rho project width op args result);
         assert (D.scoped [] result /\ get_sort result == bv_sort width);
         lemma_operation i rho project f args width op;
         lemma_reflect i rho project width e result
       | None -> ())
    | _ -> ()
