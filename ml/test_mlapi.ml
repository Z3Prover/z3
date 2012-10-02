(** Examples of using the OCaml API for Z3. *)

(**/**)
(* pause documentation *)

(*
   @name Auxiliary Functions
*)

(**
   printf
*)
let printf = Printf.printf
;;

(**
   fprintf
*)
let fprintf = Printf.fprintf
;;

(**
   Exit gracefully in case of error.
*)
let exitf message = fprintf stderr "BUG: %s.\n" message ; exit 1
;;

(**
   Create and print datatypes
*)
let mk_datatypes ctx generator =
  let datatypes = Z3.mk_datatypes ctx generator in
  printf "datatype created:\n%!" ;
  Array.iter (fun (sort, ctors) ->
    printf "sort: %s\n%!" (Z3.sort_to_string ctx sort) ;
    Array.iter (fun {Z3.constructor; recognizer; accessors} ->
      printf "constructor: %s%! recognizer: %s%! accessors:"
        (Z3.func_decl_to_string ctx constructor)
        (Z3.func_decl_to_string ctx recognizer) ;
      Array.iter (fun accessor ->
        printf " %s%!" (Z3.func_decl_to_string ctx accessor)
      ) accessors ;
      printf "\n"
    ) ctors
  ) datatypes ;
  printf "\n" ;
  datatypes
;;


(**
   Create a variable using the given name and type.
*)
let mk_var ctx name ty = Z3.mk_const ctx (Z3.mk_string_symbol ctx name) ty
;;

(* resume documentation *)
(**/**)


(**
   Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.
   Z3 is a satisfiability checker. So, one can prove {e f } by showing
   that {e (not f) } is unsatisfiable.
   The context {e ctx } is not modified by this function.
*)
let prove ctx slv f is_valid =
  (* save the current state of the context *)
  Z3.solver_push ctx slv ;

  let not_f = Z3.mk_not ctx f in
  Z3.solver_assert ctx slv not_f ;

  (match Z3.solver_check ctx slv with
  | Z3.L_FALSE ->
      (* proved *)
      printf "valid\n" ;
      if not is_valid then exitf "unexpected result"
  | Z3.L_UNDEF ->
      (* Z3 failed to prove/disprove f. *)
      printf "unknown\n" ;
      let m = Z3.solver_get_model ctx slv in
      (* m should be viewed as a potential counterexample. *)
      printf "potential counterexample:\n%s\n" (Z3.model_to_string ctx m) ;
      if is_valid then exitf "unexpected result"
  | Z3.L_TRUE ->
      (* disproved *)
      printf "invalid\n" ;
      let m = Z3.solver_get_model ctx slv in
      (* the model returned by Z3 is a counterexample *)
      printf "counterexample:\n%s\n" (Z3.model_to_string ctx m) ;
      if is_valid then exitf "unexpected result"
  );
  (* restore context *)
  Z3.solver_pop ctx slv 1
;;


(* n-ary trees and forests in OCaml *)
type tree = Leaf of int | Node of forest
and forest = tree list

(**
   Demonstrates the usage of {!Z3.mk_datatypes} with an example of forests of trees.
*)
let forest_example () =
  let ctx = Z3.mk_context [] in
  let slv = Z3.mk_solver ctx
  in
  let int_sort = Z3.mk_int_sort ctx in
  let sym name = Z3.mk_string_symbol ctx name
  in
  (* n-ary trees and forests in Z3 *)
  match
    mk_datatypes ctx
      (function [|tree; forest|] -> Some
        [|(sym"tree",
           [|{Z3.constructor_desc= sym"leaf"; recognizer_desc= sym"is_leaf"; accessor_descs= [|(sym"data", int_sort)|]};
             {Z3.constructor_desc= sym"node"; recognizer_desc= sym"is_node"; accessor_descs= [|(sym"children", forest)|]}|]);
          (sym"forest",
           [|{Z3.constructor_desc= sym"nil" ; recognizer_desc= sym"is_nil" ; accessor_descs= [||]};
             {Z3.constructor_desc= sym"cons"; recognizer_desc= sym"is_cons"; accessor_descs= [|(sym"hd", tree); (sym"tl", forest)|]}|])|]
        | _ -> None
      )
  with
    [|(tree,
       [|{Z3.constructor= leaf; recognizer= is_leaf; accessors= [|data|]};
         {Z3.constructor= node; recognizer= is_node; accessors= [|children|]}|]);
      (forest,
       [|{Z3.constructor= nil ; recognizer= is_nil ; accessors= [||]};
         {Z3.constructor= cons; recognizer= is_cons; accessors= [|hd; tl|]}|])|]
    ->
      (* translate from OCaml to Z3 *)
      let rec ml2z3_tree = function
        | Leaf(i) -> Z3.mk_app ctx leaf [|Z3.mk_int ctx i (Z3.mk_int_sort ctx)|]
        | Node(f) -> Z3.mk_app ctx node [|ml2z3_forest f|]

      and ml2z3_forest = function
        | [] -> Z3.mk_app ctx nil [||]
        | t :: f -> Z3.mk_app ctx cons [|ml2z3_tree t; ml2z3_forest f|]
      in

      (* construct some OCaml trees *)
      let t0 = Leaf 0 in
      let t12 = Node [Leaf 1; Leaf 2] in
      let t123 = Node [t12; Leaf 3] in
      let t1212 = Node [t12; t12] in
      let t412 = Node [Leaf 4; t12] in

      (* construct some Z3 trees using the translation from OCaml *)
      let t1 = ml2z3_tree t12 in		printf "t1: %s\n%!" (Z3.ast_to_string ctx t1) ;
      let t2 = ml2z3_tree t123 in		printf "t2: %s\n%!" (Z3.ast_to_string ctx t2) ;
      let t3 = ml2z3_tree t1212 in		printf "t3: %s\n%!" (Z3.ast_to_string ctx t3) ;
      let t4 = ml2z3_tree t412 in		printf "t4: %s\n%!" (Z3.ast_to_string ctx t4) ;
      let f1 = ml2z3_forest [t0] in		printf "f1: %s\n%!" (Z3.ast_to_string ctx f1) ;
      let f2 = ml2z3_forest [t12] in		printf "f2: %s\n%!" (Z3.ast_to_string ctx f2) ;
      let f3 = ml2z3_forest [t12; t0] in	printf "f3: %s\n%!" (Z3.ast_to_string ctx f3) ;

      (* or using the Z3 API *)
      let nil = Z3.mk_app ctx nil [||] in
      let cons t f = Z3.mk_app ctx cons [|t; f|] in
      let leaf i = Z3.mk_app ctx leaf [|Z3.mk_int ctx i (Z3.mk_int_sort ctx)|] in
      let node f = Z3.mk_app ctx node [|f|] in

      let t0 = leaf 0 in
      let t12 = node (cons (leaf 1) (cons (leaf 2) nil)) in
      let t123 = node (cons t12 (cons (leaf 3) nil)) in
      let t1212 = node (cons t12 (cons t12 nil)) in
      let t412 = node (cons (leaf 4) (cons t12 nil)) in

      let t1 = t12 in				printf "t1: %s\n%!" (Z3.ast_to_string ctx t1) ;
      let t2 = t123 in				printf "t2: %s\n%!" (Z3.ast_to_string ctx t2) ;
      let t3 = t1212 in				printf "t3: %s\n%!" (Z3.ast_to_string ctx t3) ;
      let t4 = t412 in				printf "t4: %s\n%!" (Z3.ast_to_string ctx t4) ;
      let f1 = cons t0 nil in			printf "f1: %s\n%!" (Z3.ast_to_string ctx f1) ;
      let f2 = cons t12 nil in			printf "f2: %s\n%!" (Z3.ast_to_string ctx f2) ;
      let f3 = cons t12 f1 in			printf "f3: %s\n%!" (Z3.ast_to_string ctx f3) ;

      (* nil != cons(nil,nil) *)
      prove ctx slv (Z3.mk_not ctx (Z3.mk_eq ctx nil f1)) true ;
      prove ctx slv (Z3.mk_not ctx (Z3.mk_eq ctx (leaf 5) t1)) true ;

      (* cons(x,u) = cons(x, v) => u = v *)
      let u = mk_var ctx "u" forest in
      let v = mk_var ctx "v" forest in
      let x = mk_var ctx "x" tree in
      let y = mk_var ctx "y" tree in
      let l1 = cons x u in			printf "l1: %s\n%!" (Z3.ast_to_string ctx l1) ;
      let l2 = cons y v in			printf "l2: %s\n%!" (Z3.ast_to_string ctx l2) ;

      prove ctx slv (Z3.mk_implies ctx (Z3.mk_eq ctx l1 l2) (Z3.mk_eq ctx u v)) true ;
      prove ctx slv (Z3.mk_implies ctx (Z3.mk_eq ctx l1 l2) (Z3.mk_eq ctx x y)) true ;

      (* is_nil(u) or is_cons(u) *)
      prove ctx slv (Z3.mk_or ctx [|Z3.mk_app ctx is_nil [|u|]; Z3.mk_app ctx is_cons [|u|]|]) true ;

      (* occurs check u != cons(x,u) *)
      prove ctx slv (Z3.mk_not ctx (Z3.mk_eq ctx u l1)) true ;

  | _ ->
      exitf "unexpected datatype signature"
;;

let _ =
  ignore( Z3.open_log "test_mlapi.log" );
  forest_example () ;
;;
