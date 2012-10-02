(** Module test_mlapi - ML test and demo program for Z3.  Matches test_capi.ml - JakobL@2007-09-08 *)

module Z3 = Z3.V3

(*
   @name Auxiliary Functions
*)

(**
   printf
*)
let printf = Printf.printf;;

(**
   fprintf
*)
let fprintf = Printf.fprintf;;

(**
   Exit gracefully in case of error.
*)
let exitf message = fprintf stderr "BUG: %s.\n" message; exit 1;;

(**
   Create a logical context.  Enable model construction.
   Also enable tracing to stderr.
*)
let mk_context ctx = 
  let ctx = Z3.mk_context_x (Array.append [|("MODEL", "true")|] ctx) in
  (* You may comment out the following line to disable tracing: *)
  (* Z3.trace_to_stderr ctx; *)
  ctx;;

(**
   Create a variable using the given name and type.
*)
let mk_var ctx name ty = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) ty;;

(**
   Create a boolean variable using the given name.
*)
let mk_bool_var ctx name = mk_var ctx name (Z3.mk_bool_sort ctx);;

(**
   Create an integer variable using the given name.
*)
let mk_int_var ctx name = mk_var ctx name (Z3.mk_int_sort ctx);;

(**
   Create a Z3 integer node using a C int. 
*)
let mk_int ctx v = Z3.mk_int ctx v (Z3.mk_int_sort ctx);;

(**
   Create a real variable using the given name.
*)
let mk_real_var ctx name = mk_var ctx name (Z3.mk_real_sort ctx);;

(**
   Create the unary function application: {e (f x) }.
*)
let mk_unary_app ctx f x = Z3.mk_app ctx f [|x|];;

(**
   Create the binary function application: {e (f x y) }.
*)
let mk_binary_app ctx f x y = Z3.mk_app ctx f [|x;y|];;

(**
   Auxiliary function to check whether two Z3 types are equal or not.
*)
let equal_sorts ctx t1 t2 = Z3.is_eq_sort ctx t1 t2;;

(**
   Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*)
let check ctx expected_result =
  begin
    let (result, m) = Z3.check_and_get_model ctx in
    (match result with
    | Z3.L_FALSE -> printf "unsat\n";
    | Z3.L_UNDEF ->
      printf "unknown\n";
      printf "potential model:\n%s\n" (Z3.model_to_string ctx m);
      (Z3.del_model ctx m);
    | Z3.L_TRUE -> printf "sat\n%s\n" (Z3.model_to_string ctx m);
      (Z3.del_model ctx m);
     );
    if result != expected_result then exitf "unexpected result";
  end;;

(**
   Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.
   Z3 is a satisfiability checker. So, one can prove {e f } by showing
   that {e (not f) } is unsatisfiable.
   The context {e ctx } is not modified by this function.
*)
let prove ctx f is_valid =
  begin
    (* save the current state of the context *)
    Z3.push ctx;

    let not_f = Z3.mk_not ctx f in
    Z3.assert_cnstr ctx not_f;
    
    (match Z3.check_and_get_model ctx with
    | (Z3.L_FALSE,_) ->
        (* proved *)
        printf "valid\n";
        if not is_valid then exitf "unexpected result";
    | (Z3.L_UNDEF,m) ->
        (* Z3 failed to prove/disprove f. *)
        printf "unknown\n";
        (* m should be viewed as a potential counterexample. *)
        printf "potential counterexample:\n%s\n" (Z3.model_to_string ctx m);
        if is_valid then exitf "unexpected result";
        (Z3.del_model ctx m);
    | (Z3.L_TRUE,m) ->
        (* disproved *)
        printf "invalid\n";
        (* the model returned by Z3 is a counterexample *)
        printf "counterexample:\n%s\n" (Z3.model_to_string ctx m);
        if is_valid then exitf "unexpected result";
        (Z3.del_model ctx m);
    );
    (* restore context *)
    Z3.pop ctx 1;
  end;;

(**
   Assert the axiom: function f is injective in the i-th argument.
   
   The following axiom is asserted into the logical context:

   forall (x_1, ..., x_n) finv(f(x_1, ..., x_i, ..., x_n)) = x_i

   Where, {e finv } is a fresh function declaration.
*)
let assert_inj_axiom ctx f i = 
  begin
    let sz = Z3.get_domain_size ctx f in
    if i >= sz then exitf "failed to create inj axiom";
    
    (* declare the i-th inverse of f: finv *)
    let finv_domain = Z3.get_range ctx f in
    let finv_range  = Z3.get_domain ctx f i in
    let finv        = Z3.mk_fresh_func_decl ctx "inv" [|finv_domain|] finv_range in

    (* allocate temporary arrays *)
    (* fill types, names and xs *)
    let types       = Z3.get_domains ctx f in
    let names       = Array.init sz (Z3.mk_int_symbol ctx) in
    let xs          = Array.init sz (fun j->Z3.mk_bound ctx j (types.(j))) in

    (* create f(x_0, ..., x_i, ..., x_{n-1}) *)
    let fxs         = Z3.mk_app ctx f xs in

    (* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) *)
    let finv_fxs    = mk_unary_app ctx finv fxs in

    (* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i *)
    let eq          = Z3.mk_eq ctx finv_fxs (xs.(i)) in

    (* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier *)
    let p           = Z3.mk_pattern ctx [|fxs|] in
    printf "pattern: %s\n" (Z3.pattern_to_string ctx p);
    printf "\n";

    (* create & assert quantifier *)
    let q           = Z3.mk_forall ctx 
                                   0 (* using default weight *)
                                   [|p|] (* the "array" of patterns *)
                                   types
                                   names
                                   eq
    in
    printf "assert axiom:\n%s\n" (Z3.ast_to_string ctx q);
    Z3.assert_cnstr ctx q;
  end;;

(**
   Assert the axiom: function f is commutative. 
   
   This example uses the SMT-LIB parser to simplify the axiom construction.
*)
let assert_comm_axiom ctx f =
  begin
    let t      = Z3.get_range ctx f in
    if Z3.get_domain_size ctx f != 2 || not (equal_sorts ctx (Z3.get_domain ctx f 0) t) || not (equal_sorts ctx (Z3.get_domain ctx f 1) t) then 
      exitf "function must be binary, and argument types must be equal to return type";
    (* Inside the parser, function f will be referenced using the symbol 'f'. *)
    let f_name = Z3.mk_string_symbol ctx "f" in
    (* Inside the parser, type t will be referenced using the symbol 'T'. *)
    let t_name = Z3.mk_string_symbol ctx "T" in
    let str    = "(benchmark comm :formula (forall (x T) (y T) (= (f x y) (f y x))))" in
    let q = Z3.parse_smtlib_string_formula ctx str [|t_name|] [|t|] [|f_name|] [|f|] in
    printf "assert axiom:\n%s\n" (Z3.ast_to_string ctx q);
    Z3.assert_cnstr ctx q;
  end;;

(**
   Z3 does not support explicitly tuple updates. They can be easily implemented 
   as macros. The argument {e t } must have tuple type. 
   A tuple update is a new tuple where field {e i } has value {e new_val }, and all
   other fields have the value of the respective field of {e t }.

   {e update(t, i, new_val) } is equivalent to
   {e mk_tuple(proj_0(t), ..., new_val, ..., proj_n(t)) } 
*)
let mk_tuple_update c t i new_val =
  begin
    let ty = Z3.get_sort c t in
    let (mk_tuple_decl,fields)=Z3.get_tuple_sort c ty in
    if i>=Array.length fields then exitf "invalid tuple update, index is too big";
    let f j = 
      if i = j then (* use new_val at position i: *) new_val
      else (* use field j of t: *) (mk_unary_app c (fields.(j)) t)
    in let new_fields = Array.init (Array.length fields) f in
    Z3.mk_app c (Z3.get_tuple_sort_mk_decl c ty) new_fields;
  end;;

(**
   Display a symbol in the given output stream.
*)
let display_symbol c out s =
  match Z3.symbol_refine c s with
  | Z3.Symbol_int i -> fprintf out "#%d" i;
  | Z3.Symbol_string r ->fprintf out "%s" r;
  | Z3.Symbol_unknown -> ();;

(**
   Display the given type.
*)
let rec display_sort c out ty =
  begin
    match Z3.sort_refine c ty with 
    | Z3.Sort_uninterpreted s -> display_symbol c out s;
    | Z3.Sort_bool -> fprintf out "bool";
    | Z3.Sort_int -> fprintf out "int";
    | Z3.Sort_real -> fprintf out "real";
    | Z3.Sort_relation -> fprintf out "relation";
    | Z3.Sort_finite_domain -> fprintf out "finite-domain";
    | Z3.Sort_bv sz -> fprintf out "bv%d" sz;
    | Z3.Sort_array (domain, range) ->
      fprintf out "[";
      display_sort c out domain;
      fprintf out "->";
      display_sort c out range;
      fprintf out "]";
    | Z3.Sort_datatype cons ->
      Array.iter (fun (dt_con : Z3.datatype_constructor_refined) -> 
       let fields = dt_con.Z3.accessors in
       fprintf out "(";
       let f i v = 
         if i>0 then fprintf out ", ";
         display_sort c out (Z3.get_range c v);
       in Array.iteri f fields;
       fprintf out ")") cons
    | Z3.Sort_unknown s ->
      fprintf out "unknown[";
      display_symbol c out s;
      fprintf out "unknown]";
  end;;

(**
   Custom ast pretty printer. 

   This function demonstrates how to use the API to navigate terms.
*)

let rec display_numeral c out nm = 
   match nm with 
   | Z3.Numeral_small(n,1L) -> 
     Printf.fprintf out "%Ld" n
   | Z3.Numeral_small(n,d) -> 
     Printf.fprintf out "%Ld/%Ld" n d
   | Z3.Numeral_large s -> 
     Printf.fprintf out "%s" s

let rec display_ast c out v =
  begin
    match Z3.term_refine c v with
    | Z3.Term_app(k, f, args) -> 
      let num_fields = Array.length args in
      let a = Z3.to_app c v in
      let d = Z3.get_app_decl c a in
      Printf.fprintf out "%s" (Z3.func_decl_to_string c d);
      if num_fields > 0 then 
         begin
           Printf.fprintf out "[";
           for i = 0 to num_fields - 1 do
               if i > 0 then Printf.fprintf out ", ";
 	       display_ast c out (Z3.get_app_arg c a i)
           done;
           Printf.fprintf out "]"
         end
    | Z3.Term_numeral(nm, s) -> 
      display_numeral c out nm;
      Printf.fprintf out ":";
      display_sort c out s 
    | Z3.Term_var(idx, s) ->
	printf "#unknown"
    | Z3.Term_quantifier(b, w, pats, bound, body) ->
	printf "quantifier"
  end;;

(**
   Custom function for traversing a term and replacing the constant 
   'x' by the bound variable having index 'idx'.
   This function illustrates how to walk Z3 terms and 
   reconstruct them.
**)

let rec abstract c x idx term =
    if Z3.is_eq_ast c term x then Z3.mk_bound c idx (Z3.get_sort c x) else
    match Z3.term_refine c term with
    | Z3.Term_app(k, f, args) -> Z3.mk_app c f (Array.map (abstract c x idx) args)
    | Z3.Term_numeral(nm, s) -> term
    | Z3.Term_var(idx, s) -> term
    | Z3.Term_quantifier(b, w, pats, bound, body) -> 
      let idx = (idx + Array.length bound) in
      let body = abstract c x idx body in 
      let is_forall = b = Z3.Forall in
      let mk_pattern terms = Z3.mk_pattern c (Array.map (abstract c x idx) terms) in
      let patterns = Array.map mk_pattern pats in
      Z3.mk_quantifier c is_forall w patterns
	(Array.map snd bound) (Array.map fst bound) body

(**
   Example abstraction function.
**)
	

let abstract_example() = 
  begin
    printf "\nabstract_example\n";
    let ctx          = mk_context [||] in
    let x            = mk_int_var ctx "x" in
    let x_decl       = Z3.get_app_decl ctx (Z3.to_app ctx x) in
    let y            = mk_int_var ctx "y" in
    let y_decl       = Z3.get_app_decl ctx (Z3.to_app ctx y) in
    let decls        = [| x_decl; y_decl |] in
    let a            = Z3.mk_string_symbol ctx "a" in
    let b            = Z3.mk_string_symbol ctx "b" in
    let names        = [| a; b |] in
    let str          = "(benchmark tst :formula (> a b))" in
    let f  = Z3.parse_smtlib_string_formula ctx str [||] [||] names decls in
    printf "formula: %s\n" (Z3.ast_to_string ctx f);

    let f2 = abstract ctx x 0 f in

    printf "abstracted formula: %s\n" (Z3.ast_to_string ctx f2);
    (* delete logical context *)
    Z3.del_context ctx;

  end;;

(**
   Custom function interpretations pretty printer.
*)
let display_function_interpretations c out m =
  begin
    fprintf out "function interpretations:\n";
    let display_function (name, entries, func_else) =
      begin
        display_symbol c out name;
        fprintf out " = {";
        let display_entry j (args,valu) =
          if j > 0 then fprintf out ", ";
          fprintf out "(";
          let f k arg =
            if k > 0 then fprintf out ", ";
            display_ast c out arg
          in Array.iteri f args;
          fprintf out "|->";
          display_ast c out valu;
          fprintf out ")";
        in Array.iteri display_entry entries;
        if Array.length entries > 0 then fprintf out ", ";
        fprintf out "(else|->";
        display_ast c out func_else;
        fprintf out ")}\n";
      end;
    in
    Array.iter display_function (Z3.get_model_funcs c m);
  end;;

(**
   Custom model pretty printer.
*)
let display_model c out m = 
  begin
    let constants=Z3.get_model_constants c m in
    let f i e =
      let name = Z3.get_decl_name c e in
      let (ok, v)  = Z3.eval_func_decl c m e in
      display_symbol c out name;
      fprintf out " = ";
      display_ast c out v;
      fprintf out "\n"
    in Array.iteri f constants;
    display_function_interpretations c out m;
  end;;

(**
   Similar to #check, but uses #display_model instead of #Z3_model_to_string.
*)
let check2 ctx expected_result =
  begin
    let (result,m) = Z3.check_and_get_model ctx in
    (match result with
    | Z3.L_FALSE ->
      printf "unsat\n";
    | Z3.L_UNDEF ->
      printf "unknown\n";
      printf "potential model:\n";
      display_model ctx stdout m;
      (Z3.del_model ctx m);
    | Z3.L_TRUE ->
      printf "sat\n";
      display_model ctx stdout m;
      (Z3.del_model ctx m);
    );
    if result != expected_result then exitf "unexpected result";
  end;;

(**
   Display Z3 version in the standard output.
*)
let display_version() =
  begin
    let (major, minor, build, revision)=Z3.get_version() in
    printf "Z3 %d.%d.%d.%d\n" major minor build revision;
  end;;

(*
   @name Examples
*)

(**
   "Hello world" example: create a Z3 logical context, and delete it.
*)
let simple_example() =
  begin
    printf "\nsimple_example\n";
    let ctx = mk_context [||] in
    (* do something with the context *)
    printf "CONTEXT:\n%sEND OF CONTEXT\n" (Z3.context_to_string ctx);
    (* delete logical context *)
    Z3.del_context ctx;
  end;;

(**
  Demonstration of how Z3 can be used to prove validity of
  De Morgan's Duality Law: {e not(x and y) <-> (not x) or ( not y) }
*)
let demorgan() =
  begin
    printf "\nDeMorgan\n";
    let ctx = mk_context [||] in
    let bool_sort = Z3.mk_bool_sort ctx in
    let symbol_x = Z3.mk_int_symbol ctx 0 in
    let symbol_y = Z3.mk_int_symbol ctx 1 in
    let x = Z3.mk_const ctx symbol_x bool_sort in
    let y = Z3.mk_const ctx symbol_y bool_sort in
  
    (* De Morgan - with a negation around: *)  
    (* !(!(x && y) <-> (!x || !y)) *)
    let not_x = Z3.mk_not ctx x in
    let not_y = Z3.mk_not ctx y in
    let x_and_y = Z3.mk_and ctx [|x;y|] in
    let ls = Z3.mk_not ctx x_and_y in
    let rs = Z3.mk_or ctx [|not_x;not_y|] in
    let conjecture = Z3.mk_iff ctx ls rs in
    let negated_conjecture = Z3.mk_not ctx conjecture in

    Z3.assert_cnstr ctx negated_conjecture;
    (match Z3.check ctx with
    | Z3.L_FALSE ->
      (* The negated conjecture was unsatisfiable, hence the conjecture is valid *)
      printf "DeMorgan is valid\n"
    | Z3.L_UNDEF ->
      (* Check returned undef *)
      printf "Undef\n"
    | Z3.L_TRUE ->
      (* The negated conjecture was satisfiable, hence the conjecture is not valid *)
      Printf.printf "DeMorgan is not valid\n");
    Z3.del_context ctx;
  end;;

(**
   Find a model for {e x xor y }.
*)
let find_model_example1() =
  begin
    printf "\nfind_model_example1\n";
    let ctx     = mk_context [||] in
    let x       = mk_bool_var ctx "x" in
    let y       = mk_bool_var ctx "y" in
    let x_xor_y = Z3.mk_xor ctx x y in
    Z3.assert_cnstr ctx x_xor_y;
    printf "model for: x xor y\n";
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Find a model for {e x < y + 1, x > 2 }.
   Then, assert {e not(x = y) }, and find another model.
*)
let find_model_example2() =
  begin
    printf "\nfind_model_example2\n";
    let ctx        = mk_context [||] in
    let x          = mk_int_var ctx "x" in
    let y          = mk_int_var ctx "y" in
    let one        = mk_int ctx 1 in
    let two        = mk_int ctx 2 in
    let y_plus_one = Z3.mk_add ctx [|y;one|] in
    let c1         = Z3.mk_lt ctx x y_plus_one in
    let c2         = Z3.mk_gt ctx x two in
    Z3.assert_cnstr ctx c1;
    Z3.assert_cnstr ctx c2;
    printf "model for: x < y + 1, x > 2\n";
    check ctx Z3.L_TRUE;

    (* assert not(x = y) *)
    let x_eq_y     = Z3.mk_eq ctx x y in
    let c3         = Z3.mk_not ctx x_eq_y in
    Z3.assert_cnstr ctx c3;
    printf "model for: x < y + 1, x > 2, not(x = y)\n";
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Prove {e x = y implies g(x) = g(y) }, and
   disprove {e x = y implies g(g(x)) = g(y) }.

   This function demonstrates how to create uninterpreted types and
   functions.
*)
let prove_example1() =
  begin
    printf "\nprove_example1\n";

    let ctx        = mk_context [||] in
    
    (* create uninterpreted type. *)
    let u_name     = Z3.mk_string_symbol ctx "U" in
    let u          = Z3.mk_uninterpreted_sort ctx u_name in
    
    (* declare function g *)
    let g_name      = Z3.mk_string_symbol ctx "g" in
    let g           = Z3.mk_func_decl ctx g_name [|u|] u in

    (* create x and y *)
    let x_name      = Z3.mk_string_symbol ctx "x" in
    let y_name      = Z3.mk_string_symbol ctx "y" in
    let x           = Z3.mk_const ctx x_name u in
    let y           = Z3.mk_const ctx y_name u in
    (* create g(x), g(y) *)
    let gx          = mk_unary_app ctx g x in
    let gy          = mk_unary_app ctx g y in
    
    (* assert x = y *)
    let eq          = Z3.mk_eq ctx x y in
    Z3.assert_cnstr ctx eq;

    (* prove g(x) = g(y) *)
    let f           = Z3.mk_eq ctx gx gy in
    printf "prove: x = y implies g(x) = g(y)\n";
    prove ctx f true;

    (* create g(g(x)) *)
    let ggx         = mk_unary_app ctx g gx in
    
    (* disprove g(g(x)) = g(y) *)
    let f           = Z3.mk_eq ctx ggx gy in
    printf "disprove: x = y implies g(g(x)) = g(y)\n";
    prove ctx f false;

    Z3.del_context ctx;
  end;;

(**
   Prove {e not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0  }.
   Then, show that {e z < -1 } is not implied.

   This example demonstrates how to combine uninterpreted functions and arithmetic.
*)
let prove_example2() =
  begin
    printf "\nprove_example2\n";
    
    let ctx        = mk_context [||] in

    (* declare function g *)
    let int_sort    = Z3.mk_int_sort ctx in
    let g_name      = Z3.mk_string_symbol ctx "g" in
    let g           = Z3.mk_func_decl ctx g_name [|int_sort|] int_sort in

    (* create x, y, and z *)
    let x           = mk_int_var ctx "x" in
    let y           = mk_int_var ctx "y" in
    let z           = mk_int_var ctx "z" in

    (* create gx, gy, gz *)
    let gx          = mk_unary_app ctx g x in
    let gy          = mk_unary_app ctx g y in
    let gz          = mk_unary_app ctx g z in
    
    (* create zero *)
    let zero        = mk_int ctx 0 in

    (* assert not(g(g(x) - g(y)) = g(z)) *)
    let gx_gy       = Z3.mk_sub ctx [|gx;gy|] in
    let ggx_gy      = mk_unary_app ctx g gx_gy in
    let eq          = Z3.mk_eq ctx ggx_gy gz in
    let c1          = Z3.mk_not ctx eq in
    Z3.assert_cnstr ctx c1;

    (* assert x + z <= y *)
    let x_plus_z    = Z3.mk_add ctx [|x;z|] in
    let c2          = Z3.mk_le ctx x_plus_z y in
    Z3.assert_cnstr ctx c2;

    (* assert y <= x *)
    let c3          = Z3.mk_le ctx y x in
    Z3.assert_cnstr ctx c3;

    (* prove z < 0 *)
    let f           = Z3.mk_lt ctx z zero in
    printf "prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0\n";
    prove ctx f true;

    (* disprove z < -1 *)
    let minus_one   = mk_int ctx (-1) in
    let f           = Z3.mk_lt ctx z minus_one in
    printf "disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1\n";
    prove ctx f false;

    Z3.del_context ctx;
  end;;

(**
   Show how push & pop can be used to create "backtracking"
   points.

   This example also demonstrates how big numbers can be created in Z3.
*)
let push_pop_example1() =
  begin
    printf "\npush_pop_example1\n";
    let ctx        = mk_context [||] in

    (* create a big number *)
    let int_sort   = Z3.mk_int_sort ctx in
    let big_number = Z3.mk_numeral ctx "1000000000000000000000000000000000000000000000000000000" int_sort in
    
    (* create number 3 *)
    let three      = Z3.mk_numeral ctx "3" int_sort in

    (* create x *)
    let x_sym      = Z3.mk_string_symbol ctx "x" in
    let x          = Z3.mk_const ctx x_sym int_sort in

    (* assert x >= "big number" *)
    let c1         = Z3.mk_ge ctx x big_number in
    printf "assert: x >= 'big number'\n";
    Z3.assert_cnstr ctx c1;

    (* create a backtracking point *)
    printf "push\n";
    Z3.push ctx;

    printf "number of scopes: %d\n" (Z3.get_num_scopes ctx);

    (* assert x <= 3 *)
    let c2         = Z3.mk_le ctx x three in
    printf "assert: x <= 3\n";
    Z3.assert_cnstr ctx c2;

    (* context is inconsistent at this point *)
    check2 ctx Z3.L_FALSE;

    (* backtrack: the constraint x <= 3 will be removed, since it was
       asserted after the last push. *)
    printf "pop\n";
    Z3.pop ctx 1;

    printf "number of scopes: %d\n" (Z3.get_num_scopes ctx);

    (* the context is consistent again. *)
    check2 ctx Z3.L_TRUE;

    (* new constraints can be asserted... *)
    
    (* create y *)
    let y_sym      = Z3.mk_string_symbol ctx "y" in
    let y          = Z3.mk_const ctx y_sym int_sort in

    (* assert y > x *)
    let c3         = Z3.mk_gt ctx y x in
    printf "assert: y > x\n";
    Z3.assert_cnstr ctx c3;

    (* the context is still consistent. *)
    check2 ctx Z3.L_TRUE;
    
    Z3.del_context ctx;
  end;;

(**
   Prove that {e f(x, y) = f(w, v) implies y = v } when 
   {e f } is injective in the second argument.
*)
let quantifier_example1() =
  begin
    printf "\nquantifier_example1\n";

    (* If quantified formulas are asserted in a logical context, then
       Z3 may return L_UNDEF. In this case, the model produced by Z3 should be viewed as a potential/candidate model.
       Limiting the number of iterations of the model finder for quantified formulas.
    *)
    let ctx = mk_context [|("MBQI_MAX_ITERATIONS", "10")|] in

    (* declare function f *)
    let int_sort    = Z3.mk_int_sort ctx in
    let f_name      = Z3.mk_string_symbol ctx "f" in
    let f           = Z3.mk_func_decl ctx f_name [|int_sort; int_sort|] int_sort in
  
    (* assert that f is injective in the second argument. *)
    assert_inj_axiom ctx f 1;
    
    (* create x, y, v, w, fxy, fwv *)
    let x           = mk_int_var ctx "x" in
    let y           = mk_int_var ctx "y" in
    let v           = mk_int_var ctx "v" in
    let w           = mk_int_var ctx "w" in
    let fxy         = mk_binary_app ctx f x y in
    let fwv         = mk_binary_app ctx f w v in
    
    (* assert f(x, y) = f(w, v) *)
    let p1          = Z3.mk_eq ctx fxy fwv in
    Z3.assert_cnstr ctx p1;

    (* prove f(x, y) = f(w, v) implies y = v *)
    let p2          = Z3.mk_eq ctx y v in
    printf "prove: f(x, y) = f(w, v) implies y = v\n";
    prove ctx p2 true;

    (* disprove f(x, y) = f(w, v) implies x = w *)
    (* using check2 instead of prove *)
    let p3          = Z3.mk_eq ctx x w in
    let not_p3      = Z3.mk_not ctx p3 in
    Z3.assert_cnstr ctx not_p3;
    printf "disprove: f(x, y) = f(w, v) implies x = w\n";
    printf "that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable\n";
    check2 ctx Z3.L_UNDEF;
    Printf.printf
	"reason for last failure: %d (7 = quantifiers)\n" 
        (if Z3.get_search_failure(ctx) = Z3.QUANTIFIERS then 7 else -1);


    Z3.del_context ctx;
  end;;

(**
   Prove {e store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) }.
   
   This example demonstrates how to use the array theory.
*)
let array_example1() =
  begin
    printf "\narray_example1\n";

    let ctx = mk_context [||] in

    let int_sort    = Z3.mk_int_sort ctx in
    let array_sort  = Z3.mk_array_sort ctx int_sort int_sort in

    let a1          = mk_var ctx "a1" array_sort in
    let a2          = mk_var ctx "a2" array_sort in
    let i1          = mk_var ctx "i1" int_sort in
    let i2          = mk_var ctx "i2" int_sort in
    let i3          = mk_var ctx "i3" int_sort in
    let v1          = mk_var ctx "v1" int_sort in
    let v2          = mk_var ctx "v2" int_sort in
    
    let st1         = Z3.mk_store ctx a1 i1 v1 in
    let st2         = Z3.mk_store ctx a2 i2 v2 in
    
    let sel1        = Z3.mk_select ctx a1 i3 in
    let sel2        = Z3.mk_select ctx a2 i3 in

    (* create antecedent *)
    let antecedent  = Z3.mk_eq ctx st1 st2 in

    (* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) *)
    let ds = [|
        Z3.mk_eq ctx i1 i3;
        Z3.mk_eq ctx i2 i3;
        Z3.mk_eq ctx sel1 sel2;
      |] in

    let consequent  = Z3.mk_or ctx ds in

    (* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) *)
    let thm         = Z3.mk_implies ctx antecedent consequent in
    printf "prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))\n";
    printf "%s\n" (Z3.ast_to_string ctx thm);
    prove ctx thm true;

    Z3.del_context ctx;
  end;;

(**
   Show that {e distinct(a_0, ... , a_n) } is
   unsatisfiable when {e a_i's } are arrays from boolean to
   boolean and n > 4.

   This example also shows how to use the {e distinct } construct.
*)
let array_example2() =
  begin
    printf "\narray_example2\n";

    for n = 2 to 5 do
      printf "n = %d\n" n;
      let ctx = mk_context [||] in
      
      let bool_sort   = Z3.mk_bool_sort ctx in
      let array_sort  = Z3.mk_array_sort ctx bool_sort bool_sort in
      
      (* create arrays *)
      let a = Array.init n
        (fun i->Z3.mk_const ctx (Z3.mk_int_symbol ctx i) array_sort) in
      
      (* assert distinct(a[0], ..., a[n]) *)
      let d = Z3.mk_distinct ctx a in
      printf "%s\n" (Z3.ast_to_string ctx d);
      Z3.assert_cnstr ctx d;

      (* context is satisfiable if n < 5 *)
      check2 ctx (if n < 5 then Z3.L_TRUE else Z3.L_FALSE);

      Z3.del_context ctx;
    done
  end;;

(**
   Simple array type construction/deconstruction example.
*)
let array_example3() =
  begin
    printf "\narray_example3\n";

    let ctx      = mk_context [||] in

    let bool_sort  = Z3.mk_bool_sort ctx in
    let int_sort   = Z3.mk_int_sort ctx in
    let array_sort = Z3.mk_array_sort ctx int_sort bool_sort in

    let (domain,range) = Z3.get_array_sort ctx array_sort in
    printf "domain: ";
    display_sort ctx stdout domain;
    printf "\n";
    printf "range:  ";
    display_sort ctx stdout range;
    printf "\n";

    if (not (Z3.is_eq_sort ctx int_sort domain)) ||
       (not (Z3.is_eq_sort ctx bool_sort range)) then
        exitf "invalid array type";
    Z3.del_context ctx;
  end;;

(**
   Simple tuple type example. It creates a tuple that is a pair of real numbers.
*)
let tuple_example1() =
  begin
    printf "\ntuple_example1\n";
    let ctx       = mk_context [||] in

    let real_sort = Z3.mk_real_sort ctx in

    (* Create pair (tuple) type *)
    let mk_tuple_name = Z3.mk_string_symbol ctx "mk_pair" in
    let proj_names_0 = Z3.mk_string_symbol ctx "get_x" in
    let proj_names_1 = Z3.mk_string_symbol ctx "get_y" in
    let proj_names = [|proj_names_0; proj_names_1|] in
    let proj_sorts = [|real_sort;real_sort|] in
    (* Z3_mk_tuple_sort will set mk_tuple_decl and proj_decls *)
    let (pair_sort,mk_tuple_decl,proj_decls) = Z3.mk_tuple_sort ctx mk_tuple_name proj_names proj_sorts in
    let get_x_decl    = proj_decls.(0) in (* function that extracts the first element of a tuple. *)
    let get_y_decl    = proj_decls.(1) in (* function that extracts the second element of a tuple. *)

    printf "tuple_sort: ";
    display_sort ctx stdout pair_sort;
    printf "\n";

    begin
      (* prove that get_x(mk_pair(x,y)) == 1 implies x = 1*)
      let x    = mk_real_var ctx "x" in
      let y    = mk_real_var ctx "y" in
      let app1 = mk_binary_app ctx mk_tuple_decl x y in
      let app2 = mk_unary_app ctx get_x_decl app1 in 
      let one  = Z3.mk_numeral ctx "1" real_sort in
      let eq1  = Z3.mk_eq ctx app2 one in
      let eq2  = Z3.mk_eq ctx x one in
      let thm  = Z3.mk_implies ctx eq1 eq2 in
      printf "prove: get_x(mk_pair(x, y)) = 1 implies x = 1\n";
      prove ctx thm true;

      (* disprove that get_x(mk_pair(x,y)) == 1 implies y = 1*)
      let eq3  = Z3.mk_eq ctx y one in
      let thm  = Z3.mk_implies ctx eq1 eq3 in
      printf "disprove: get_x(mk_pair(x, y)) = 1 implies y = 1\n";
      prove ctx thm false;
    end;

    begin
      (* prove that get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2 *)
      let p1          = mk_var ctx "p1" pair_sort in
      let p2          = mk_var ctx "p2" pair_sort in
      let x1          = mk_unary_app ctx get_x_decl p1 in
      let y1          = mk_unary_app ctx get_y_decl p1 in
      let x2          = mk_unary_app ctx get_x_decl p2 in
      let y2          = mk_unary_app ctx get_y_decl p2 in
      let antecedents_0 = Z3.mk_eq ctx x1 x2 in
      let antecedents_1 = Z3.mk_eq ctx y1 y2 in
      let antecedents = [|antecedents_0; antecedents_1|] in
      let antecedent  = Z3.mk_and ctx antecedents in
      let consequent  = Z3.mk_eq ctx p1 p2 in
      let thm         = Z3.mk_implies ctx antecedent consequent in
      printf "prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2\n";
      prove ctx thm true;

      (* disprove that get_x(p1) = get_x(p2) implies p1 = p2 *)
      let thm         = Z3.mk_implies ctx (antecedents.(0)) consequent in
      printf "disprove: get_x(p1) = get_x(p2) implies p1 = p2\n";
      prove ctx thm false;
    end;

    begin
      (* demonstrate how to use the mk_tuple_update function *)
      (* prove that p2 = update(p1, 0, 10) implies get_x(p2) = 10 *)
      let p1             = mk_var ctx "p1" pair_sort in
      let p2             = mk_var ctx "p2" pair_sort in
      let one            = Z3.mk_numeral ctx "1" real_sort in
      let ten            = Z3.mk_numeral ctx "10" real_sort in
      let updt           = mk_tuple_update ctx p1 0 ten in
      let antecedent     = Z3.mk_eq ctx p2 updt in
      let x              = mk_unary_app ctx get_x_decl p2 in
      let consequent     = Z3.mk_eq ctx x ten in
      let thm            = Z3.mk_implies ctx antecedent consequent in
      printf "prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10\n";
      prove ctx thm true;

      (* disprove that p2 = update(p1, 0, 10) implies get_y(p2) = 10 *)
      let y              = mk_unary_app ctx get_y_decl p2 in
      let consequent     = Z3.mk_eq ctx y ten in
      let thm            = Z3.mk_implies ctx antecedent consequent in
      printf "disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10\n";
      prove ctx thm false;
    end;

    Z3.del_context ctx;
  end;;

(**
   Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
 *)
let bitvector_example1() =
  begin
    printf "\nbitvector_example1\n";
    
    let ctx       = mk_context [||] in
    
    let bv_sort   = Z3.mk_bv_sort ctx 32 in
    
    let x           = mk_var ctx "x" bv_sort in
    let zero        = Z3.mk_numeral ctx "0" bv_sort in
    let ten         = Z3.mk_numeral ctx "10" bv_sort in
    let x_minus_ten = Z3.mk_bvsub ctx x ten in
    (* bvsle is signed less than or equal to *)
    let c1          = Z3.mk_bvsle ctx x ten in
    let c2          = Z3.mk_bvsle ctx x_minus_ten zero in
    let thm         = Z3.mk_iff ctx c1 c2 in
    printf "disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers\n";
    prove ctx thm false;
    
    Z3.del_context ctx;
  end;;

(**
   Find x and y such that: x ^ y - 103 == x * y
 *)
let bitvector_example2() =
  begin
    printf "\nbitvector_example2\n";
    let ctx       = mk_context [||] in
    (* construct x ^ y - 103 == x * y *)
    let bv_sort   = Z3.mk_bv_sort ctx 32 in
    let x         = mk_var ctx "x" bv_sort in
    let y         = mk_var ctx "y" bv_sort in
    let x_xor_y   = Z3.mk_bvxor ctx x y in
    let c103      = Z3.mk_numeral ctx "103" bv_sort in
    let lhs       = Z3.mk_bvsub ctx x_xor_y c103 in
    let rhs       = Z3.mk_bvmul ctx x y in
    let ctr       = Z3.mk_eq ctx lhs rhs in
    printf "find values of x and y, such that x ^ y - 103 == x * y\n";
    Z3.assert_cnstr ctx ctr;
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Demonstrate how to use #Z3_eval.
*)
let eval_example1() =
  begin
    printf "\neval_example1\n";
    
    let ctx        = mk_context [||] in
    let x          = mk_int_var ctx "x" in
    let y          = mk_int_var ctx "y" in
    let two        = mk_int ctx 2 in
    
    (* assert x < y *)
    let c1         = Z3.mk_lt ctx x y in
    Z3.assert_cnstr ctx c1;

    (* assert x > 2 *)
    let c2         = Z3.mk_gt ctx x two in
    Z3.assert_cnstr ctx c2;

    (* find model for the constraints above *)
    (match Z3.check_and_get_model ctx with
    | (Z3.L_TRUE, m) ->
      begin
        let args = [|x; y|] in
        printf "MODEL:\n%s" (Z3.model_to_string ctx m);
        let x_plus_y = Z3.mk_add ctx args in
        printf "\nevaluating x+y\n";
        (match Z3.eval ctx m x_plus_y with
        | (true,v) ->
          printf "result = ";
          display_ast ctx stdout v;
          printf "\n";
        | _ -> 
          exitf "failed to evaluate: x+y";
        );
        (Z3.del_model ctx m);
      end;
    | (_,_) ->
      exitf "the constraints are satisfiable";
    );
    Z3.del_context ctx;
  end;;

(**
   Several logical context can be used simultaneously.
*)
let two_contexts_example1() =
  begin
    printf "\ntwo_contexts_example1\n";
    (* using the same (default) configuration to initialized both logical contexts. *)
    let ctx1 = mk_context [||] in
    let ctx2 = mk_context [||] in
    let x1 = Z3.mk_const ctx1 (Z3.mk_int_symbol ctx1 0) (Z3.mk_bool_sort ctx1) in
    let x2 = Z3.mk_const ctx2 (Z3.mk_int_symbol ctx2 0) (Z3.mk_bool_sort ctx2) in
    Z3.del_context ctx1;
    (* ctx2 can still be used. *)
    printf "%s\n" (Z3.ast_to_string ctx2 x2);
    Z3.del_context ctx2;
  end;;

(**
   Demonstrates how error codes can be read insted of registering an error handler.
 *)
let error_code_example1() =
  begin
    printf "\nerror_code_example1\n";
    
    let ctx        = mk_context [||] in
    let x          = mk_bool_var ctx "x" in
    let x_decl     = Z3.get_app_decl ctx (Z3.to_app ctx x) in
    Z3.assert_cnstr ctx x;
    
    match Z3.check_and_get_model ctx with
    | (Z3.L_TRUE,m) ->
      begin
        let (ok, v) = Z3.eval_func_decl ctx  m x_decl in
        printf "last call succeeded.\n";

        (* The following call will fail since the value of x is a boolean *)
        (try ignore(Z3.get_numeral_string ctx v)
        with | _ -> printf "last call failed.\n");
        (Z3.del_model ctx m);
        Z3.del_context ctx;
      end
    | (_,_) -> exitf "unexpected result";
  end;;

(**
   Demonstrates how Z3 exceptions can be used.
*)
let error_code_example2() =
  begin
    printf "\nerror_code_example2\n%!";

    let ctx   = mk_context [||] in
    try
      let x   = mk_int_var ctx "x" in
      let y   = mk_bool_var ctx "y" in
      printf "before Z3_mk_iff\n";
      let app = Z3.mk_iff ctx x y in
      printf "unreachable";
    with | _ -> printf "Z3 error: type error.\n";
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to use the SMTLIB parser.
 *)
let parser_example1() =
  begin
    printf "\nparser_example1\n";
    
    let ctx          = mk_context [||] in
    let str          = "(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))" in
    let (formulas,_,_) = Z3.parse_smtlib_string_x ctx str [||] [||] [||] [||] in
    let f i c        =
      printf "formula %d: %s\n" i (Z3.ast_to_string ctx c);
      Z3.assert_cnstr ctx c;
    in Array.iteri f formulas;
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to initialize the parser symbol table.
 *)
let parser_example2() =
  begin
    printf "\nparser_example2\n%!";
    
    let ctx          = mk_context [||] in
    let x            = mk_int_var ctx "x" in
    let x_decl       = Z3.get_app_decl ctx (Z3.to_app ctx x) in
    let y            = mk_int_var ctx "y" in
    let y_decl       = Z3.get_app_decl ctx (Z3.to_app ctx y) in
    let decls        = [| x_decl; y_decl |] in
    let a            = Z3.mk_string_symbol ctx "a" in
    let b            = Z3.mk_string_symbol ctx "b" in
    let names        = [| a; b |] in
    let str          = "(benchmark tst :formula (> a b))" in
    let f  = Z3.parse_smtlib_string_formula ctx str [||] [||] names decls in
    printf "formula: %s\n" (Z3.ast_to_string ctx f);
    Z3.assert_cnstr ctx f;
    check ctx Z3.L_TRUE;
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to initialize the parser symbol table.
 *)
let parser_example3() =
  begin
    printf "\nparser_example3\n%!";
    
    let ctx      = mk_context [| |] in
    let int_sort = Z3.mk_int_sort ctx in
    let g_name   = Z3.mk_string_symbol ctx "g" in
    let g        = Z3.mk_func_decl ctx g_name [| int_sort; int_sort |] int_sort in
    let str      = "(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (g x 0) (g 0 y)))))" in
    assert_comm_axiom ctx g;
    let thm = Z3.parse_smtlib_string_formula ctx str [||] [||] [|g_name|] [|g|] in
    printf "formula: %s\n" (Z3.ast_to_string ctx thm);
    prove ctx thm true;
    Z3.del_context ctx;
  end;;

(**
   Display the declarations, assumptions and formulas in a SMT-LIB string.
 *)
let parser_example4() =
  begin
    printf "\nparser_example4\n%!";
    
    let ctx          = mk_context [||] in
    let str          = "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))" in
    (* arithmetic theory is automatically initialized, when an
       int/real variable or arith operation is created using the API.
       Since no such function is invoked in this example, we should do
       that manually.
     *)
    let (formulas, assumptions, decls) = Z3.parse_smtlib_string_x ctx str [||] [||] [||] [||] in
    let f prefix i n = printf "%s %d: %s\n" prefix i (Z3.ast_to_string ctx n) in
    Array.iteri (fun i n -> printf "declaration %d: %s\n" i (Z3.func_decl_to_string ctx n)) decls;
    Array.iteri (f "assumption") assumptions;
    Array.iteri (f "formula") formulas;
    Z3.del_context ctx;
  end;;

(**
   Demonstrates how to handle parser errors using Z3 exceptions.
 *)
let parser_example5() =
  begin
    printf "\nparser_example5\n";
    let ctx = mk_context [||] in
    try 
      (* the following string has a parsing error: missing parenthesis *)
      let str = "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))" in
      ignore(Z3.parse_smtlib_string_x ctx str [||] [||] [||] [||]);
    with | _ -> (printf "Z3 error: parser error.\n";
                 printf "Error message: '%s'.\n" (Z3.get_smtlib_error ctx)
                 );
    Z3.del_context ctx;    
  end;;

(**
  Example for creating an if-then-else expression.
 *)
let ite_example() =
  begin
    printf "\nite_example\n%!";
    let ctx         = mk_context [||] in
    let f           = Z3.mk_false ctx in
    let one         = mk_int ctx 1 in
    let zero        = mk_int ctx 0 in
    let ite         = Z3.mk_ite ctx f one zero in
    printf "term: %s\n" (Z3.ast_to_string ctx ite);
    Z3.del_context ctx;
  end;;


(**
   Create an enumeration data type.

   Several more examples of creating and using data-types (lists, trees, records) 
   are provided for the C-based API.
   The translation from the examples in C to use the OCaml API follow the same pattern
   that is used here.
*)
let enum_example() =
  begin
    printf "\nenum_example\n";
    let ctx         = mk_context [||] in
    let name = Z3.mk_string_symbol ctx "fruit" in
    let enum_names = [| Z3.mk_string_symbol ctx "apple"; 
                        Z3.mk_string_symbol ctx "banana";
                        Z3.mk_string_symbol ctx "orange" |] in
    let (fruit, enum_consts, enum_testers) = Z3.mk_enumeration_sort ctx name enum_names in

    printf "%s\n" (Z3.func_decl_to_string ctx enum_consts.(0));
    printf "%s\n" (Z3.func_decl_to_string ctx enum_consts.(1));
    printf "%s\n" (Z3.func_decl_to_string ctx enum_consts.(2));
    printf "%s\n" (Z3.func_decl_to_string ctx enum_testers.(0));
    printf "%s\n" (Z3.func_decl_to_string ctx enum_testers.(1));
    printf "%s\n" (Z3.func_decl_to_string ctx enum_testers.(2));          

    let apple  = Z3.mk_app ctx (enum_consts.(0)) [||] in
    let banana = Z3.mk_app ctx (enum_consts.(1)) [||] in
    let orange = Z3.mk_app ctx (enum_consts.(2)) [||] in

    (* Apples are different from oranges *)
    prove ctx (Z3.mk_not ctx (Z3.mk_eq ctx apple orange)) true;

    (* Apples pass the apple test *)
    prove ctx (Z3.mk_app ctx enum_testers.(0) [| apple |]) true;

    (* Oranges fail the apple test *)
    prove ctx (Z3.mk_app ctx enum_testers.(0) [| orange |]) false;
    prove ctx (Z3.mk_not ctx (Z3.mk_app ctx enum_testers.(0) [| orange |])) true;

    let fruity = mk_var ctx "fruity" fruit in

    (* If something is fruity, then it is an apple, banana, or orange *)
    let ors = [| Z3.mk_eq ctx fruity apple; 
                 Z3.mk_eq ctx fruity banana; 
                 Z3.mk_eq ctx fruity orange |] in

    prove ctx  (Z3.mk_or ctx ors) true;
    Z3.del_context ctx;
 end;;

(**
  Example for extracting unsatisfiable core and proof.
  The example uses the function check_assumptions which allows passing in additional 
  hypotheses. The unsatisfiable core is a subset of these additional hypotheses. 
 *)
let unsat_core_and_proof_example() = 
  begin
    printf "\nunsat_core_and_proof_example\n%!";
    let ctx = mk_context [| ("PROOF_MODE","2") |] in
    let pa = mk_bool_var ctx "PredA" in
    let pb = mk_bool_var ctx "PredB" in
    let pc = mk_bool_var ctx "PredC" in
    let pd = mk_bool_var ctx "PredD" in
    let p1 = mk_bool_var ctx "P1" in
    let p2 = mk_bool_var ctx "P2" in
    let p3 = mk_bool_var ctx "P3" in
    let p4 = mk_bool_var ctx "P4" in
    let assumptions = [| Z3.mk_not ctx p1; Z3.mk_not ctx p2; Z3.mk_not ctx p3; Z3.mk_not ctx p4 |] in
    let f1 = Z3.mk_and ctx [| pa; pb; pc |] in
    let f2 = Z3.mk_and ctx [| pa; Z3.mk_not ctx pc; pb |] in
    let f3 = Z3.mk_or ctx [| Z3.mk_not ctx pa; Z3.mk_not ctx pc |] in
    let f4 = pd in
    let core_dummy = [| pa; pa; pa; pa |] in
    Z3.assert_cnstr ctx (Z3.mk_or ctx [| f1; p1 |]);
    Z3.assert_cnstr ctx (Z3.mk_or ctx [| f2; p2 |]);
    Z3.assert_cnstr ctx (Z3.mk_or ctx [| f3; p3 |]);
    Z3.assert_cnstr ctx (Z3.mk_or ctx [| f4; p4 |]);
    let result = Z3.check_assumptions ctx assumptions 4 core_dummy in
    (match result with
    | (Z3.L_FALSE, _, proof, core_size, core) -> 
        printf "unsat\n";
        printf "proof: %s\n" (Z3.ast_to_string ctx proof);
        printf("\ncore:\n");
        for i = 0 to core_size - 1 do 
	   printf "%s\n" (Z3.ast_to_string ctx (core.(i)));
        done;
        printf("\n")
    | (_,_,_,_,_)-> assert false;
    );
    (* delete logical context *)
    Z3.del_context(ctx);
 end

(** 

*)

let get_implied_equalities_example() = 
  begin
    printf "\nget_implied_equalities example\n%!";
    let ctx = mk_context [| |] in
    let int_ty = Z3.mk_int_sort ctx in
    let a = mk_int_var ctx "a" in
    let b = mk_int_var ctx "b" in
    let c = mk_int_var ctx "c" in
    let d = mk_int_var ctx "d" in
    let f = Z3.mk_func_decl ctx (Z3.mk_string_symbol ctx "f") [| int_ty |] int_ty in
    let fa = Z3.mk_app ctx f [| a |] in
    let fb = Z3.mk_app ctx f [| b |] in
    let fc = Z3.mk_app ctx f [| c |] in
    let terms = [| a; b; c; d; fa; fb; fc |] in
    Z3.assert_cnstr ctx (Z3.mk_eq ctx a b);
    Z3.assert_cnstr ctx (Z3.mk_eq ctx b c);
    Z3.assert_cnstr ctx (Z3.mk_le ctx fc b);
    Z3.assert_cnstr ctx (Z3.mk_le ctx b fa);        
    let is_sat, class_ids = Z3.get_implied_equalities ctx terms in
    for i = 0 to 6 do
       printf "Class %s |-> %d\n" (Z3.ast_to_string ctx (terms.(i))) (class_ids.(i));       
    done;
    printf "asserting f(a) <= b\n";
    Z3.assert_cnstr ctx (Z3.mk_le ctx fa b);
    let is_sat, class_ids = Z3.get_implied_equalities ctx terms in
    for i = 0 to 6 do
       printf "Class %s |-> %d\n" (Z3.ast_to_string ctx (terms.(i))) (class_ids.(i));       
    done;
    (* delete logical context *)
    Z3.del_context(ctx)
  end;;

let main() =
  begin
    ignore (Z3.open_log("ml.log"));
    display_version();
    simple_example();
    demorgan();
    find_model_example1();
    find_model_example2();
    prove_example1();
    prove_example2();
    push_pop_example1();
    quantifier_example1();
    array_example1();
    array_example2();
    array_example3();
    tuple_example1();
    bitvector_example1();
    bitvector_example2();
    eval_example1();
    two_contexts_example1();
    error_code_example1(); 
    error_code_example2();
    parser_example1();
    parser_example2();
    parser_example3();
    parser_example4();
    parser_example5();
(*     numeral_example(); *)
    ite_example();
(*     list_example(); *)
(*     tree_example(); *)
(*     forest_example(); *)
(*     binary_tree_example(); *)
    enum_example();
    unsat_core_and_proof_example();
    abstract_example();
    get_implied_equalities_example();
(*     incremental_example1(); *)
(*     reference_counter_example(); *)
(*     smt2parser_example(); *)
(*     substitute_example(); *)
(*     substitute_vars_example(); *)
  end;;

let _ = main();;
