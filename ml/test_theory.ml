module Z3 = Z3.V3

let print_lbool lb = 
    match lb with
    | Z3.L_FALSE -> Printf.printf "false\n"
    | Z3.L_TRUE -> Printf.printf "true\n"
    | Z3.L_UNDEF -> Printf.printf "undef\n"

(* simple sanity test of theory plugin *)
let test_theory() =
    let ctx = Z3.mk_context_x [| |] in
    let th  = Z3.mk_theory ctx "test-theory" in
    let _   = Z3.set_push_callback th (fun () -> Printf.printf "push\n") in 
    let _   = Z3.set_pop_callback th (fun () -> Printf.printf "pop\n") in 
    let _   = Z3.set_delete_callback th (fun () -> Printf.printf "delete\n") in 
    let _   = Z3.set_final_check_callback th (fun () -> (Printf.printf "final\n"; true)) in 
    let _   = Z3.set_delete_callback th (fun () -> Printf.printf "deleted\n") in
    let f_sym = Z3.mk_string_symbol ctx "f" in
    let a_sym = Z3.mk_string_symbol ctx "a" in
    let b_sym = Z3.mk_string_symbol ctx "b" in
    let int_sort = Z3.mk_int_sort ctx in
    let f   = Z3.theory_mk_func_decl ctx th f_sym [|int_sort |] int_sort in
    let a   = Z3.theory_mk_constant ctx th a_sym int_sort in
    let b   = Z3.theory_mk_constant ctx th b_sym int_sort in
    let reduce_f g args =
        Printf.printf "reduce %s\n" (Z3.func_decl_to_string ctx g);
        match g, args with
        | _, [| a' |] when Z3.is_eq_func_decl ctx g f && Z3.is_eq_ast ctx a' a -> Some b
        | _, _ -> None
    in
    let _   = Z3.set_reduce_app_callback th reduce_f in 
    (* b != f(b) is consistent *)
    let _   = Z3.assert_cnstr ctx (Z3.mk_not ctx (Z3.mk_eq ctx b (Z3.mk_app ctx f [| b |]))) in
    let res = Z3.check ctx in
    print_lbool res;
    (* b != f(a) is not consistent *)
    let _   = Z3.assert_cnstr ctx (Z3.mk_not ctx (Z3.mk_eq ctx b (Z3.mk_app ctx f [| a |]))) in
    let res = Z3.check ctx in
    print_lbool res;
    Z3.del_context ctx

let _ = test_theory() 
