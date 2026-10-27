module Z3BvFreshModel

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open FStar.List.Tot
module F = Z3BvFresh
module BV = Z3BvLemma
module BO = Z3BvOrder
module B = Z3BooleanRewrite
module SM = Z3ScopedModel
module D = Z3Definitions
module SK = Z3Skolemization
module L = FStar.List.Tot

(* The legacy Boolean model constrains these nullary declarations by name. *)
let rec safe_symbols (symbols:list func_decl) : Tot bool (decreases symbols) =
  match symbols with
  | [] -> true
  | f :: rest ->
    f.decl_name <> "true" && f.decl_name <> "false" &&
    f.decl_name <> "and" && f.decl_name <> "or" && safe_symbols rest

let rec safe_context (rs:list F.reconstruction) : Tot bool (decreases rs) =
  match rs with [] -> true | r :: rest -> safe_symbols r.F.symbols && safe_context rest

let check_context (inputs es:list expr)
  : result:option (list F.reconstruction){
      forall rs. result == Some rs ==>
        F.valid_context rs /\ F.fresh_inputs rs inputs /\ F.matches rs es /\ safe_context rs} =
  match F.check_context inputs es with
  | Some rs -> if safe_context rs then Some rs else None
  | None -> None

let literal (b:bool) : expr = if b then true_expr else false_expr

let rec retract (symbols:list func_decl) (n:nat) (e:expr) : Tot expr (decreases e) =
  match e with
  | Var _ _ -> e
  | App f [] ->
    if Some? f.interp then e
    else (match F.lookup f symbols n with Some b -> literal b | None -> e)
  | App f args -> App f (retract_args symbols n args)
  | Quantifier k bs s body -> Quantifier k bs s (retract symbols n body)

and retract_args (symbols:list func_decl) (n:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> retract symbols n a :: retract_args symbols n rest

let rec lemma_symbol_member (symbols:list func_decl) (f:func_decl)
  : Lemma (requires F.valid_symbols symbols /\ L.mem f symbols)
          (ensures f.interp == None /\ f.domain == [] /\ f.range == bool_sort)
          (decreases symbols)
  = match symbols with
    | [] -> ()
    | g :: rest -> if f <> g then lemma_symbol_member rest f

let lemma_retract_sort (symbols:list func_decl) (n:nat) (e:expr)
  : Lemma (requires F.valid_symbols symbols)
          (ensures get_sort (retract symbols n e) == get_sort e)
  = match e with
    | App f [] ->
      if None? f.interp && Some? (F.lookup f symbols n) then (
        F.lemma_lookup_member f symbols n (Some?.v (F.lookup f symbols n));
        lemma_symbol_member symbols f)
    | _ -> ()

let rec lemma_retract_shape (symbols:list func_decl) (n:nat) (scope:list sort) (e:expr)
  : Lemma (requires F.valid_symbols symbols)
          (ensures get_sort (retract symbols n e) == get_sort e /\
                   (D.scoped scope e ==> D.scoped scope (retract symbols n e)))
          (decreases e)
  = lemma_retract_sort symbols n e;
    match e with
    | Var _ _ -> ()
    | App f args -> lemma_retract_args_shape symbols n scope args f.domain
    | Quantifier _ bs _ body -> lemma_retract_shape symbols n (L.rev bs @ scope) body

and lemma_retract_args_shape (symbols:list func_decl) (n:nat) (scope:list sort)
                             (args:list expr) (domain:list sort)
  : Lemma (requires F.valid_symbols symbols)
          (ensures L.length (retract_args symbols n args) == L.length args /\
                   (D.scoped_args scope args ==> D.scoped_args scope (retract_args symbols n args)) /\
                   sorts_match (retract_args symbols n args) domain == sorts_match args domain /\
                   L.for_all (fun a -> get_sort a = bool_sort) (retract_args symbols n args) ==
                     L.for_all (fun a -> get_sort a = bool_sort) args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_retract_shape symbols n scope a;
      lemma_retract_args_shape symbols n scope rest (match domain with [] -> [] | _ :: ds -> ds)

let rec lemma_eval_retract (r:F.reconstruction) (i:interpretation value)
                           (project:pos -> value -> int) (rho:env value) (e:expr)
  : Lemma (requires SM.literal_model i /\ quant_extensional i)
          (ensures eval (F.extend r i project) e rho ==
                     eval i (retract r.F.symbols (F.number r i project) e) rho)
          (decreases e)
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_eval_retract_args r i project rho args
    | Quantifier _ bs _ body ->
      let aux (vs:list value{L.length vs = L.length bs})
        : Lemma (eval (F.extend r i project) body (shift vs rho) ==
                   eval i (retract r.F.symbols (F.number r i project) body) (shift vs rho))
        = lemma_eval_retract r i project (shift vs rho) body in
      FStar.Classical.forall_intro aux

and lemma_eval_retract_args (r:F.reconstruction) (i:interpretation value)
                            (project:pos -> value -> int) (rho:env value) (args:list expr)
  : Lemma (requires SM.literal_model i /\ quant_extensional i)
          (ensures eval_args (F.extend r i project) args rho ==
                     eval_args i (retract_args r.F.symbols (F.number r i project) args) rho /\
                   BV.bit_values (F.extend r i project) rho args ==
                     BV.bit_values i rho (retract_args r.F.symbols (F.number r i project) args))
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_eval_retract r i project rho a;
      lemma_eval_retract_args r i project rho rest

let lemma_retract_app (symbols:list func_decl) (n:nat) (f:func_decl) (args:list expr)
  : Lemma (requires Some? f.interp)
          (ensures retract symbols n (App f args) == App f (retract_args symbols n args))
  = match args with [] -> () | _ :: _ -> ()

let rec lemma_constant_domains (s:sort) (xs ys:list expr)
  : Lemma (requires L.length xs == L.length ys)
          (ensures L.map (fun _ -> s) xs == L.map (fun _ -> s) ys)
          (decreases xs)
  = match xs, ys with
    | _ :: rest, _ :: tail -> lemma_constant_domains s rest tail
    | _, _ -> ()

let rec lemma_maps_extensional (args:list expr)
  : Lemma (forall (f g:expr -> Tot sort).
             (forall a. f a == g a) ==> L.map f args == L.map g args)
          (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest ->
      lemma_maps_extensional rest;
      let aux (f g:expr -> Tot sort)
        : Lemma ((forall a. f a == g a) ==> L.map f args == L.map g args) = () in
      FStar.Classical.forall_intro_2 aux

#push-options "--fuel 4 --ifuel 2"
let lemma_operations (r:F.reconstruction) (i:interpretation value)
                      (project:pos -> value -> int) (rho:env value)
                      (f:func_decl) (args:list expr) (width:pos) (op:decl_kind)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i /\
                    D.scoped [] (App f args) /\
                    (BV.operation f args == Some (width, op) \/
                     BV.nary_operation f args == Some (width, op)))
          (ensures (let j = F.extend r i project in
                    (BV.operation f args == Some (width, op) ==>
                     project width (eval j (App f args) rho) ==
                       BV.calculate width op (BV.words width project (eval_args j args rho))) /\
                    (BV.nary_operation f args == Some (width, op) ==>
                     project width (eval j (App f args) rho) ==
                       BV.calculate_nary width op (BV.words width project (eval_args j args rho)))))
  = let symbols = r.F.symbols in
    let n = F.number r i project in
    let ras = retract_args symbols n args in
    lemma_retract_args_shape symbols n [] args f.domain;
    lemma_constant_domains (BV.bv_sort width) args ras;
    lemma_maps_extensional args;
    lemma_maps_extensional ras;
    lemma_retract_app symbols n f args;
    lemma_eval_retract r i project rho (App f args);
    lemma_eval_retract_args r i project rho args;
    if BV.operation f args = Some (width, op) then (
      assert (BV.operation f ras == Some (width, op));
      BV.lemma_operation i rho project f ras width op);
    if BV.nary_operation f args = Some (width, op) then (
      assert (f.int_params == [width] /\ f.interp == Some op);
      assert (f.domain == L.map (fun _ -> BV.bv_sort width) args);
      assert (sorts_match ras f.domain /\ L.length ras >= 3);
      assert (BV.nary_operation f ras == Some (width, op)))
#pop-options

let lemma_extract (r:F.reconstruction) (i:interpretation value)
                   (project:pos -> value -> int) (rho:env value) (e:expr) (s:BV.extraction)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i /\
                    D.scoped [] e /\ BV.extract_parts e == Some s)
          (ensures (let j = F.extend r i project in
                    project (s.BV.high - s.BV.low + 1) (eval j e rho) ==
                      (project s.BV.source_width (eval j s.BV.operand rho) / pow2 s.BV.low) %
                      pow2 (s.BV.high - s.BV.low + 1)))
  = let symbols = r.F.symbols in
    let n = F.number r i project in
    lemma_retract_shape symbols n [] e;
    lemma_retract_shape symbols n [] s.BV.operand;
    lemma_eval_retract r i project rho e;
    lemma_eval_retract r i project rho s.BV.operand;
    let rs = { s with BV.operand = retract symbols n s.BV.operand } in
    (match e with App f args -> lemma_retract_app symbols n f args | _ -> ());
    assert (BV.extract_parts (retract symbols n e) == Some rs);
    BV.lemma_extract_parts i rho project (retract symbols n e) rs

let lemma_retract_concat_shape (symbols:list func_decl) (n:nat) (e:expr) (c:BV.concatenation)
  : Lemma (requires F.valid_symbols symbols /\ D.scoped [] e /\ BV.concat_parts e == Some c)
          (ensures D.scoped [] (retract symbols n e) /\
                   BV.concat_parts (retract symbols n e) ==
                     Some { c with BV.left = retract symbols n c.BV.left;
                                   BV.right = retract symbols n c.BV.right })
  = lemma_retract_shape symbols n [] e;
    lemma_retract_shape symbols n [] c.BV.left;
    lemma_retract_shape symbols n [] c.BV.right;
    match e with App f args -> lemma_retract_app symbols n f args | _ -> ()

let lemma_concat (r:F.reconstruction) (i:interpretation value)
                  (project:pos -> value -> int) (rho:env value) (e:expr) (c:BV.concatenation)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i /\
                    D.scoped [] e /\ BV.concat_parts e == Some c)
          (ensures (let j = F.extend r i project in
                    project (c.BV.left_width + c.BV.right_width) (eval j e rho) ==
                      project c.BV.left_width (eval j c.BV.left rho) * pow2 c.BV.right_width +
                      project c.BV.right_width (eval j c.BV.right rho)))
  = let symbols = r.F.symbols in
    let n = F.number r i project in
    lemma_retract_concat_shape symbols n e c;
    lemma_eval_retract r i project rho e;
    lemma_eval_retract r i project rho c.BV.left;
    lemma_eval_retract r i project rho c.BV.right;
    let rc = { c with BV.left = retract symbols n c.BV.left; BV.right = retract symbols n c.BV.right } in
    BV.lemma_concat_parts i rho project (retract symbols n e) rc

let lemma_unsigned (r:F.reconstruction) (i:interpretation value)
                    (project:pos -> value -> int) (rho:env value) (e:expr) (c:BV.unsigned_comparison)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i /\
                    D.scoped [] e /\ BV.unsigned_parts e == Some c)
          (ensures (let j = F.extend r i project in
                    eval j e rho == VBool (BV.unsigned_value c.BV.relation
                      (project c.BV.width (eval j c.BV.lhs rho)) (project c.BV.width (eval j c.BV.rhs rho)))))
  = let symbols = r.F.symbols in
    let n = F.number r i project in
    lemma_retract_shape symbols n [] e;
    lemma_retract_shape symbols n [] c.BV.lhs;
    lemma_retract_shape symbols n [] c.BV.rhs;
    lemma_eval_retract r i project rho e;
    lemma_eval_retract r i project rho c.BV.lhs;
    lemma_eval_retract r i project rho c.BV.rhs;
    let rc = { c with BV.lhs = retract symbols n c.BV.lhs; BV.rhs = retract symbols n c.BV.rhs } in
    (match e with App f args -> lemma_retract_app symbols n f args | _ -> ());
    assert (BV.unsigned_parts (retract symbols n e) == Some rc);
    BO.lemma_unsigned_parts i rho project (retract symbols n e) rc

let lemma_concat3_value (i:interpretation value) (project:pos -> value -> int)
                        (rho:env value) (e:expr) (c:BV.concatenation3)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\ BV.concat3_parts e == Some c)
          (ensures project (c.BV.width1 + c.BV.width2 + c.BV.width3) (eval i e rho) ==
                     project c.BV.width1 (eval i c.BV.first rho) * pow2 (c.BV.width2 + c.BV.width3) +
                     project c.BV.width2 (eval i c.BV.second rho) * pow2 c.BV.width3 +
                     project c.BV.width3 (eval i c.BV.third rho))
  = match e with App _ [_; _; _] -> () | _ -> ()

let lemma_retract_concat3_shape (symbols:list func_decl) (n:nat) (e:expr) (c:BV.concatenation3)
  : Lemma (requires F.valid_symbols symbols /\ D.scoped [] e /\ BV.concat3_parts e == Some c)
          (ensures D.scoped [] (retract symbols n e) /\
                   BV.concat3_parts (retract symbols n e) ==
                     Some { c with BV.first = retract symbols n c.BV.first;
                                   BV.second = retract symbols n c.BV.second;
                                   BV.third = retract symbols n c.BV.third })
  = lemma_retract_shape symbols n [] e;
    lemma_retract_shape symbols n [] c.BV.first;
    lemma_retract_shape symbols n [] c.BV.second;
    lemma_retract_shape symbols n [] c.BV.third;
    match e with App f args -> lemma_retract_app symbols n f args | _ -> ()

let lemma_concat3 (r:F.reconstruction) (i:interpretation value)
                   (project:pos -> value -> int) (rho:env value) (e:expr) (c:BV.concatenation3)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i /\
                    D.scoped [] e /\ BV.concat3_parts e == Some c)
          (ensures (let j = F.extend r i project in
                    project (c.BV.width1 + c.BV.width2 + c.BV.width3) (eval j e rho) ==
                      project c.BV.width1 (eval j c.BV.first rho) * pow2 (c.BV.width2 + c.BV.width3) +
                      project c.BV.width2 (eval j c.BV.second rho) * pow2 c.BV.width3 +
                      project c.BV.width3 (eval j c.BV.third rho)))
  = let symbols = r.F.symbols in
    let n = F.number r i project in
    lemma_retract_concat3_shape symbols n e c;
    lemma_eval_retract r i project rho e;
    lemma_eval_retract r i project rho c.BV.first;
    lemma_eval_retract r i project rho c.BV.second;
    lemma_eval_retract r i project rho c.BV.third;
    let rc = { c with BV.first = retract symbols n c.BV.first;
                     BV.second = retract symbols n c.BV.second; BV.third = retract symbols n c.BV.third } in
    lemma_concat3_value i project rho (retract symbols n e) rc;
    let j = F.extend r i project in
    assert (eval j c.BV.first rho == eval i rc.BV.first rho);
    assert (eval j c.BV.second rho == eval i rc.BV.second rho);
    assert (eval j c.BV.third rho == eval i rc.BV.third rho);
    assert (project c.BV.width1 (eval i rc.BV.first rho) ==
            project c.BV.width1 (eval j c.BV.first rho));
    assert (project c.BV.width2 (eval i rc.BV.second rho) ==
            project c.BV.width2 (eval j c.BV.second rho));
    assert (project c.BV.width3 (eval i rc.BV.third rho) ==
            project c.BV.width3 (eval j c.BV.third rho))

let lemma_word_value (i:interpretation value) (project:pos -> value -> int)
                     (rho:env value) (e:expr) (width:pos) (args:list expr)
  : Lemma (requires BV.bv_model i project /\ D.scoped [] e /\
                    BV.word_parts e == Some (width, args))
          (ensures project width (eval i e rho) == BV.bits_number (BV.bit_values i rho args))
  = match e with App _ _ -> () | _ -> ()

let lemma_word (r:F.reconstruction) (i:interpretation value)
                (project:pos -> value -> int) (rho:env value) (e:expr) (width:pos) (args:list expr)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i /\
                    D.scoped [] e /\ BV.word_parts e == Some (width, args))
          (ensures (let j = F.extend r i project in
                    project width (eval j e rho) == BV.bits_number (BV.bit_values j rho args)))
  = let symbols = r.F.symbols in
    let n = F.number r i project in
    let ras = retract_args symbols n args in
    lemma_retract_shape symbols n [] e;
    lemma_retract_args_shape symbols n [] args [];
    lemma_constant_domains bool_sort args ras;
    lemma_eval_retract r i project rho e;
    lemma_eval_retract_args r i project rho args;
    (match e with App f args -> lemma_retract_app symbols n f args | _ -> ());
    assert (BV.word_parts (retract symbols n e) == Some (width, ras));
    lemma_word_value i project rho (retract symbols n e) width ras

let lemma_bv_model (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ BV.bv_model i project /\
                    SM.literal_model i /\ quant_extensional i)
          (ensures BV.bv_model (F.extend r i project) project)
  = let j = F.extend r i project in
    let symbols = r.F.symbols in
    let n = F.number r i project in
    let bounds (width:pos) (a b:expr) (rho:env value)
      : Lemma (D.scoped [] a /\ D.scoped [] b /\
                 get_sort a == BV.bv_sort width /\ get_sort b == BV.bv_sort width ==>
                ((eval j a rho == eval j b rho <==>
                   project width (eval j a rho) == project width (eval j b rho)) /\
                 0 <= project width (eval j a rho) /\ project width (eval j a rho) < pow2 width))
      = lemma_retract_shape symbols n [] a;
        lemma_retract_shape symbols n [] b;
        lemma_eval_retract r i project rho a;
        lemma_eval_retract r i project rho b in
    FStar.Classical.forall_intro_4 bounds;
    let numeral (e:expr) (rho:env value) (width:pos) (v:int)
      : Lemma (BV.numeral e == Some (width, v) ==> project width (eval j e rho) == v)
      = if BV.numeral e = Some (width, v) then (
          (match e with App f args -> lemma_retract_app symbols n f args | _ -> ());
          lemma_eval_retract r i project rho e) in
    FStar.Classical.forall_intro_4 numeral;
    let operations (f:func_decl)
      : Lemma (forall (args:list expr) (rho:env value) (width:pos) (op:decl_kind).
          (D.scoped [] (App f args) /\ BV.operation f args == Some (width, op) ==>
             project width (eval j (App f args) rho) ==
               BV.calculate width op (BV.words width project (eval_args j args rho))) /\
          (D.scoped [] (App f args) /\ BV.nary_operation f args == Some (width, op) ==>
             project width (eval j (App f args) rho) ==
               BV.calculate_nary width op (BV.words width project (eval_args j args rho))))
      = let aux (args:list expr) (rho:env value) (width:pos) (op:decl_kind)
          : Lemma (
            (D.scoped [] (App f args) /\ BV.operation f args == Some (width, op) ==>
               project width (eval j (App f args) rho) ==
                 BV.calculate width op (BV.words width project (eval_args j args rho))) /\
            (D.scoped [] (App f args) /\ BV.nary_operation f args == Some (width, op) ==>
               project width (eval j (App f args) rho) ==
                 BV.calculate_nary width op (BV.words width project (eval_args j args rho))))
          = if D.scoped [] (App f args) &&
               (BV.operation f args = Some (width, op) || BV.nary_operation f args = Some (width, op))
            then lemma_operations r i project rho f args width op in
        FStar.Classical.forall_intro_4 aux in
    FStar.Classical.forall_intro operations;
    let extract (e:expr) (rho:env value) (s:BV.extraction)
      : Lemma (D.scoped [] e /\ BV.extract_parts e == Some s ==>
          project (s.BV.high - s.BV.low + 1) (eval j e rho) ==
            (project s.BV.source_width (eval j s.BV.operand rho) / pow2 s.BV.low) %
            pow2 (s.BV.high - s.BV.low + 1))
      = if D.scoped [] e && BV.extract_parts e = Some s then lemma_extract r i project rho e s in
    FStar.Classical.forall_intro_3 extract;
    let concat (e:expr) (rho:env value) (c:BV.concatenation)
      : Lemma (D.scoped [] e /\ BV.concat_parts e == Some c ==>
          project (c.BV.left_width + c.BV.right_width) (eval j e rho) ==
            project c.BV.left_width (eval j c.BV.left rho) * pow2 c.BV.right_width +
            project c.BV.right_width (eval j c.BV.right rho))
      = if D.scoped [] e && BV.concat_parts e = Some c then lemma_concat r i project rho e c in
    FStar.Classical.forall_intro_3 concat;
    let word (e:expr) (rho:env value) (width:pos) (args:list expr)
      : Lemma (D.scoped [] e /\ BV.word_parts e == Some (width, args) ==>
          project width (eval j e rho) == BV.bits_number (BV.bit_values j rho args))
      = if D.scoped [] e && BV.word_parts e = Some (width, args)
        then lemma_word r i project rho e width args in
    FStar.Classical.forall_intro_4 word;
    let unsigned (e:expr) (rho:env value) (c:BV.unsigned_comparison)
      : Lemma (D.scoped [] e /\ BV.unsigned_parts e == Some c ==>
          eval j e rho == VBool (BV.unsigned_value c.BV.relation
            (project c.BV.width (eval j c.BV.lhs rho)) (project c.BV.width (eval j c.BV.rhs rho))))
      = if D.scoped [] e && BV.unsigned_parts e = Some c then lemma_unsigned r i project rho e c in
    FStar.Classical.forall_intro_3 unsigned;
    let concat3 (e:expr) (rho:env value) (c:BV.concatenation3)
      : Lemma (D.scoped [] e /\ BV.concat3_parts e == Some c ==>
          project (c.BV.width1 + c.BV.width2 + c.BV.width3) (eval j e rho) ==
            project c.BV.width1 (eval j c.BV.first rho) * pow2 (c.BV.width2 + c.BV.width3) +
            project c.BV.width2 (eval j c.BV.second rho) * pow2 c.BV.width3 +
            project c.BV.width3 (eval j c.BV.third rho))
      = if D.scoped [] e && BV.concat3_parts e = Some c then lemma_concat3 r i project rho e c in
    FStar.Classical.forall_intro_3 concat3;
    assert (BV.bv_model j project)

let rec lemma_lookup_reserved (symbols:list func_decl) (n:nat) (f:func_decl)
  : Lemma (requires safe_symbols symbols /\
                    (f.decl_name == "true" \/ f.decl_name == "false" \/
                     f.decl_name == "and" \/ f.decl_name == "or"))
          (ensures F.lookup f symbols n == None)
          (decreases symbols)
  = match symbols with [] -> () | _ :: rest -> lemma_lookup_reserved rest (n / 2) f

let lemma_retract_named (symbols:list func_decl) (n:nat) (f:func_decl) (args:list expr)
  : Lemma (requires safe_symbols symbols /\
                    (f.decl_name == "true" \/ f.decl_name == "false" \/
                     f.decl_name == "and" \/ f.decl_name == "or"))
          (ensures retract symbols n (App f args) == App f (retract_args symbols n args))
  = lemma_lookup_reserved symbols n f;
    match args with [] -> () | _ :: _ -> ()

let lemma_literals (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires safe_symbols r.F.symbols /\ true_sound i /\ false_sound i /\ quant_extensional i)
          (ensures true_sound (F.extend r i project) /\ false_sound (F.extend r i project))
  = let j = F.extend r i project in
    let aux (f:func_decl) (rho:env value)
      : Lemma ((f.decl_name == "true" ==> eval j (App f []) rho == VBool true) /\
               (f.decl_name == "false" ==> eval j (App f []) rho == VBool false))
      = if f.decl_name = "true" || f.decl_name = "false" then (
          lemma_retract_named r.F.symbols (F.number r i project) f [];
          lemma_eval_retract r i project rho (App f [])) in
    FStar.Classical.forall_intro_2 aux

let rec lemma_connectives (r:F.reconstruction) (i:interpretation value)
                          (project:pos -> value -> int) (rho:env value) (args:list expr)
  : Lemma (requires SM.literal_model i /\ quant_extensional i)
          (ensures (conj_holds (F.extend r i project) rho args <==>
                      conj_holds i rho (retract_args r.F.symbols (F.number r i project) args)) /\
                   (clause_holds (F.extend r i project) rho args <==>
                      clause_holds i rho (retract_args r.F.symbols (F.number r i project) args)))
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_eval_retract r i project rho a;
      lemma_connectives r i project rho rest

let rec lemma_retract_boolean_args (symbols:list func_decl) (n:nat) (args:list expr)
  : Lemma (requires F.valid_symbols symbols)
          (ensures B.boolean_args (retract_args symbols n args) == B.boolean_args args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_retract_sort symbols n a;
      lemma_retract_boolean_args symbols n rest

let lemma_boolean_base (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ safe_symbols r.F.symbols /\
                    B.boolean_rewrite_model i /\ quant_extensional i)
          (ensures (let j = F.extend r i project in
                    Z3ObservationalEquality.boolean_model j /\ not_sound j /\ true_sound j /\ false_sound j))
  = let j = F.extend r i project in
    let symbols = r.F.symbols in
    let n = F.number r i project in
    lemma_literals r i project;
    let boolean (a:expr) (rho:env value)
      : Lemma (get_sort a == bool_sort ==> VBool? (eval j a rho))
      = lemma_retract_sort symbols n a;
        lemma_eval_retract r i project rho a in
    FStar.Classical.forall_intro_2 boolean;
    let negation (f:func_decl) (a:expr) (rho:env value)
      : Lemma (f.decl_name == "not" ==>
                ((eval j (App f [a]) rho == VBool true) == (eval j a rho == VBool false)))
      = lemma_eval_retract r i project rho (App f [a]);
        lemma_eval_retract r i project rho a in
    FStar.Classical.forall_intro_3 negation

let lemma_boolean_connectives (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ safe_symbols r.F.symbols /\
                    B.boolean_rewrite_model i /\ quant_extensional i)
          (ensures and_sound (F.extend r i project) /\ or_sound (F.extend r i project))
  = let j = F.extend r i project in
    let symbols = r.F.symbols in
    let n = F.number r i project in
    let connectives (f:func_decl) (args:list expr) (rho:env value)
      : Lemma ((f.decl_name == "and" ==>
                 (eval j (App f args) rho == VBool true <==> conj_holds j rho args)) /\
               (f.decl_name == "or" ==>
                 (eval j (App f args) rho == VBool true <==> clause_holds j rho args)))
      = if f.decl_name = "and" || f.decl_name = "or" then (
          lemma_retract_named symbols n f args;
          lemma_eval_retract r i project rho (App f args);
          lemma_connectives r i project rho args) in
    FStar.Classical.forall_intro_3 connectives

let lemma_boolean_binary (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ B.boolean_rewrite_model i /\ quant_extensional i)
          (ensures implies_sound (F.extend r i project) /\ eq_sound (F.extend r i project))
  = let j = F.extend r i project in
    let binary (f:func_decl) (a b:expr) (rho:env value)
      : Lemma (
          ((f.decl_name == "implies" \/ f.decl_name == "=>") ==>
            (eval j (App f [a; b]) rho == VBool true <==> (lit_true j rho a ==> lit_true j rho b))) /\
          (f.decl_name == "=" ==>
            (eval j (App f [a; b]) rho == VBool true <==> eval j a rho == eval j b rho)))
      = lemma_eval_retract r i project rho (App f [a; b]);
        lemma_eval_retract r i project rho a;
        lemma_eval_retract r i project rho b in
    FStar.Classical.forall_intro_4 binary

let lemma_boolean_ite (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ B.boolean_rewrite_model i /\ quant_extensional i)
          (ensures B.ite_sound (F.extend r i project))
  = let j = F.extend r i project in
    let symbols = r.F.symbols in
    let n = F.number r i project in
    let ite (c t e:expr) (rho:env value)
      : Lemma (B.boolean_args [c; t; e] ==>
          eval j (App B.boolean_ite_decl [c; t; e]) rho ==
            (if B.bool_value (eval j c rho) then eval j t rho else eval j e rho))
      = lemma_retract_boolean_args symbols n [c; t; e];
        lemma_eval_retract r i project rho (App B.boolean_ite_decl [c; t; e]);
        lemma_eval_retract r i project rho c;
        lemma_eval_retract r i project rho t;
        lemma_eval_retract r i project rho e in
    FStar.Classical.forall_intro_4 ite

let lemma_boolean_xor (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ B.boolean_rewrite_model i /\ quant_extensional i)
          (ensures B.xor_sound (F.extend r i project))
  = let j = F.extend r i project in
    let symbols = r.F.symbols in
    let n = F.number r i project in
    let xor (a b:expr) (rho:env value)
      : Lemma (B.boolean_args [a; b] ==>
          eval j (App B.boolean_xor_decl [a; b]) rho ==
            VBool (B.bool_value (eval j a rho) <> B.bool_value (eval j b rho)))
      = lemma_retract_boolean_args symbols n [a; b];
        lemma_eval_retract r i project rho (App B.boolean_xor_decl [a; b]);
        lemma_eval_retract r i project rho a;
        lemma_eval_retract r i project rho b in
    FStar.Classical.forall_intro_3 xor

let lemma_boolean_model (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ safe_symbols r.F.symbols /\
                    B.boolean_rewrite_model i /\ quant_extensional i)
          (ensures B.boolean_rewrite_model (F.extend r i project))
  = lemma_boolean_base r i project;
    lemma_boolean_connectives r i project;
    lemma_boolean_binary r i project;
    lemma_boolean_ite r i project;
    lemma_boolean_xor r i project

let lemma_official_literals (r:F.reconstruction) (i:interpretation value)
                            (project:pos -> value -> int)
  : Lemma (requires SM.literal_model i /\ quant_extensional i)
          (ensures SM.literal_model (F.extend r i project))
  = let aux (rho:env value)
      : Lemma (eval (F.extend r i project) true_expr rho == VBool true /\
               eval (F.extend r i project) false_expr rho == VBool false)
      = lemma_eval_retract r i project rho true_expr;
        lemma_eval_retract r i project rho false_expr in
    FStar.Classical.forall_intro aux

let lemma_scoped_model (r:F.reconstruction) (i:interpretation value) (project:pos -> value -> int)
  : Lemma (requires F.valid r /\ SM.model i /\ SM.literal_model i /\ quant_extensional i)
          (ensures SM.model (F.extend r i project))
  = let aux (scope:list sort) (e:expr) (rho:env value)
      : Lemma (D.scoped scope e /\ SM.environment_typed scope rho ==>
                 SM.scalar_typed (get_sort e) (eval (F.extend r i project) e rho))
      = lemma_retract_shape r.F.symbols (F.number r i project) scope e;
        lemma_eval_retract r i project rho e in
    FStar.Classical.forall_intro_3 aux

let rec lemma_context_bv_model (rs:list F.reconstruction) (i:interpretation value)
                              (project:pos -> value -> int)
  : Lemma (requires F.valid_context rs /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i)
          (ensures (let j = F.extend_context rs i project in
                    BV.bv_model j project /\ SM.literal_model j /\ quant_extensional j))
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      lemma_context_bv_model rest i project;
      let older = F.extend_context rest i project in
      let j = F.extend r older project in
      lemma_bv_model r older project;
      lemma_official_literals r older project;
      SK.lemma_quantifier_fields older j

let rec lemma_scoped_context_models (rs:list F.reconstruction) (i:interpretation value)
                                    (project:pos -> value -> int)
  : Lemma (requires F.valid_context rs /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i /\ SM.model i /\ SM.reflexive_equality i)
          (ensures (let j = F.extend_context rs i project in
                    BV.bv_model j project /\ SM.literal_model j /\ SM.model j /\
                    SM.reflexive_equality j /\ quant_extensional j))
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      lemma_scoped_context_models rest i project;
      let older = F.extend_context rest i project in
      let j = F.extend r older project in
      lemma_bv_model r older project;
      lemma_official_literals r older project;
      lemma_scoped_model r older project;
      SK.lemma_quantifier_fields older j

let rec lemma_matched_context (rs:list F.reconstruction) (es:list expr)
                             (j:interpretation value) (rho:env value)
  : Lemma (requires F.matches rs es /\ SM.reflexive_equality j /\
                    (forall r. L.mem r rs ==> eval j (F.word r) rho == eval j (F.source r) rho))
          (ensures conj_holds j rho es)
          (decreases rs)
  = match rs, es with
    | r :: rest, _ :: tail ->
      lemma_matched_context rest tail j rho;
      assert (eval j (F.word r) rho == eval j (F.source r) rho);
      let v = eval j (F.source r) rho in
      assert (j.interp_app (eq_decl (get_sort (F.source r))) [v; v] == VBool true)
    | _, _ -> ()

let lemma_scoped_context_extension (inputs es:list expr) (rs:list F.reconstruction)
                                   (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires F.check_context inputs es == Some rs /\ quant_extensional i /\
                    BV.bv_model i project /\ SM.literal_model i /\ SM.model i /\ SM.reflexive_equality i)
          (ensures (let j = F.extend_context rs i project in
                    BV.bv_model j project /\ SM.literal_model j /\ SM.model j /\
                    SM.reflexive_equality j /\ quant_extensional j /\
                    eval_args j inputs rho == eval_args i inputs rho /\ conj_holds j rho es))
  = lemma_scoped_context_models rs i project;
    F.lemma_context_inputs rs inputs i project rho;
    let j = F.extend_context rs i project in
    let values (r:F.reconstruction)
      : Lemma (L.mem r rs ==> eval j (F.word r) rho == eval j (F.source r) rho)
      = if L.mem r rs then F.lemma_context_value rs r i project rho in
    FStar.Classical.forall_intro values;
    lemma_matched_context rs es j rho

let rec lemma_context_models (rs:list F.reconstruction) (i:interpretation value)
                             (project:pos -> value -> int)
  : Lemma (requires F.valid_context rs /\ safe_context rs /\ quant_extensional i /\
                    BV.bv_model i project /\ B.boolean_rewrite_model i)
          (ensures (let j = F.extend_context rs i project in
                    BV.bv_model j project /\ B.boolean_rewrite_model j /\ quant_extensional j))
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      lemma_context_models rest i project;
      let older = F.extend_context rest i project in
      let j = F.extend r older project in
      lemma_bv_model r older project;
      lemma_boolean_model r older project;
      SK.lemma_quantifier_fields older j

let lemma_context_extension (inputs es:list expr) (rs:list F.reconstruction)
                            (i:interpretation value) (project:pos -> value -> int) (rho:env value)
  : Lemma (requires check_context inputs es == Some rs /\ quant_extensional i /\
                    BV.bv_model i project /\ B.boolean_rewrite_model i)
          (ensures (let j = F.extend_context rs i project in
                    BV.bv_model j project /\ B.boolean_rewrite_model j /\ quant_extensional j /\
                    eval_args j inputs rho == eval_args i inputs rho /\ conj_holds j rho es))
  = lemma_context_models rs i project;
    SM.lemma_legacy_reflexivity i;
    F.lemma_context_model_extension inputs es rs i project rho;
    let j = F.extend_context rs i project in
    let rec matched (rs:list F.reconstruction) (es:list expr)
      : Lemma (requires F.matches rs es /\ conj_holds j rho (F.equations rs))
              (ensures conj_holds j rho es)
              (decreases rs)
      = match rs, es with
        | r :: rest, _ :: tail -> matched rest tail
        | _, _ -> () in
    matched rs es
