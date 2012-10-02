quote (ml,"


(* Internal auxillary functions: *)

(* Transform a pair of arrays into an array of pairs *)
let array_combine a b =
  if Array.length a <> Array.length b then raise (Invalid_argument \"array_combine\");
  Array.init (Array.length a) (fun i->(a.(i),b.(i)));;

(* [a |> b] is the pipeline operator for [b(a)] *)
let ( |> ) x f = f x;;


(* Extensions, except for refinement: *)
let mk_context_x configs = 
  let config = mk_config() in
  let f(param_id,param_value) = set_param_value config param_id param_value in
  Array.iter f configs;
  let context = mk_context config in
  del_config config;
  context;;

let get_app_args c a =
  Array.init (get_app_num_args c a) (get_app_arg c a);;

let get_domains c d =
  Array.init (get_domain_size c d) (get_domain c d);;

let get_array_sort c t = (get_array_sort_domain c t, get_array_sort_range c t);;

let get_tuple_sort c ty = 
  (get_tuple_sort_mk_decl c ty,
   Array.init (get_tuple_sort_num_fields c ty) (get_tuple_sort_field_decl c ty));;

type datatype_constructor_refined = { 
   constructor : func_decl; 
   recognizer : func_decl; 
   accessors : func_decl array 
}

let get_datatype_sort c ty = 
  Array.init (get_datatype_sort_num_constructors c ty)
  (fun idx_c -> 
   let constr = get_datatype_sort_constructor c ty idx_c in
   let recog = get_datatype_sort_recognizer  c ty idx_c in
   let num_acc = get_domain_size c constr in
   { constructor = constr;
     recognizer = recog;
     accessors = Array.init num_acc (get_datatype_sort_constructor_accessor c ty idx_c);
   })

let get_model_constants c m =
  Array.init (get_model_num_constants c m) (get_model_constant c m);;


let get_model_func_entry c m i j =
  (Array.init
     (get_model_func_entry_num_args c m i j)
     (get_model_func_entry_arg c m i j),
   get_model_func_entry_value c m i j);;

let get_model_func_entries c m i =
  Array.init (get_model_func_num_entries c m i) (get_model_func_entry c m i);;

let get_model_funcs c m =
  Array.init (get_model_num_funcs c m)
    (fun i->(get_model_func_decl c m i |> get_decl_name c,
             get_model_func_entries c m i,
             get_model_func_else c m i));;
 
let get_smtlib_formulas c = 
  Array.init (get_smtlib_num_formulas c) (get_smtlib_formula c);;

let get_smtlib_assumptions c = 
  Array.init (get_smtlib_num_assumptions c) (get_smtlib_assumption c);;

let get_smtlib_decls c =
  Array.init (get_smtlib_num_decls c) (get_smtlib_decl c);;

let get_smtlib_parse_results c =
  (get_smtlib_formulas c, get_smtlib_assumptions c, get_smtlib_decls c);;

let parse_smtlib_string_formula c a1 a2 a3 a4 a5 = 
  (parse_smtlib_string c a1 a2 a3 a4 a5;
   match get_smtlib_formulas c with [|f|] -> f | _ -> failwith \"Z3: parse_smtlib_string_formula\");;

let parse_smtlib_file_formula c a1 a2 a3 a4 a5 = 
  (parse_smtlib_file c a1 a2 a3 a4 a5;
   match get_smtlib_formulas c with [|f|] -> f | _ -> failwith \"Z3: parse_smtlib_file_formula\");;

let parse_smtlib_string_x c a1 a2 a3 a4 a5 = 
  (parse_smtlib_string c a1 a2 a3 a4 a5; get_smtlib_parse_results c);;

let parse_smtlib_file_x c a1 a2 a3 a4 a5 = 
  (parse_smtlib_file c a1 a2 a3 a4 a5; get_smtlib_parse_results c);;

(* Refinement: *)

type symbol_refined =
  | Symbol_int of int
  | Symbol_string of string
  | Symbol_unknown;;

let symbol_refine c s =
  match get_symbol_kind c s with
  | INT_SYMBOL -> Symbol_int (get_symbol_int c s)
  | STRING_SYMBOL -> Symbol_string (get_symbol_string c s);;

type sort_refined =
  | Sort_uninterpreted of symbol
  | Sort_bool
  | Sort_int
  | Sort_real
  | Sort_bv of int
  | Sort_array of (sort * sort)
  | Sort_datatype of datatype_constructor_refined array
  | Sort_relation
  | Sort_finite_domain
  | Sort_unknown of symbol;;

let sort_refine c ty =
  match get_sort_kind c ty with
  | UNINTERPRETED_SORT -> Sort_uninterpreted (get_sort_name c ty)
  | BOOL_SORT -> Sort_bool
  | INT_SORT -> Sort_int
  | REAL_SORT -> Sort_real
  | BV_SORT -> Sort_bv (get_bv_sort_size c ty)
  | ARRAY_SORT -> Sort_array (get_array_sort_domain c ty, get_array_sort_range c ty)
  | DATATYPE_SORT -> Sort_datatype (get_datatype_sort c ty)
  | RELATION_SORT -> Sort_relation 
  | FINITE_DOMAIN_SORT -> Sort_finite_domain
  | UNKNOWN_SORT -> Sort_unknown (get_sort_name c ty);;

let get_pattern_terms c p = 
  Array.init (get_pattern_num_terms c p) (get_pattern c p)

type binder_type = | Forall | Exists 

type numeral_refined = 
  | Numeral_small  of int64 * int64
  | Numeral_large  of string

type term_refined = 
  | Term_app        of decl_kind * func_decl * ast array
  | Term_quantifier of binder_type * int * ast array array * (symbol *sort) array * ast
  | Term_numeral    of numeral_refined * sort
  | Term_var        of int * sort

let term_refine c t = 
  match get_ast_kind c t with
  | NUMERAL_AST -> 
      let (is_small, n, d) = get_numeral_small c t in
      if is_small then 
	Term_numeral(Numeral_small(n,d), get_sort c t)
      else
	Term_numeral(Numeral_large(get_numeral_string c t), get_sort c t)
  | APP_AST   -> 
      let t' = to_app c t in
      let f =  get_app_decl c t' in
      let num_args = get_app_num_args c t' in
      let args = Array.init num_args (get_app_arg c t') in
      let k = get_decl_kind c f in
      Term_app (k, f, args)
  | QUANTIFIER_AST -> 
      let bt = if is_quantifier_forall c t then Forall else Exists in
      let w = get_quantifier_weight c t                            in
      let np = get_quantifier_num_patterns c t                     in
      let pats = Array.init np (get_quantifier_pattern_ast c t)    in
      let pats = Array.map (get_pattern_terms c) pats              in
      let nb = get_quantifier_num_bound c t                        in
      let bound = Array.init nb 
	  (fun i -> (get_quantifier_bound_name c t i, get_quantifier_bound_sort c t i)) in
      let body = get_quantifier_body c t in
      Term_quantifier(bt, w, pats, bound, body)
  | VAR_AST -> 
      Term_var(get_index_value c t, get_sort c t)
  | _ -> assert false
  
type theory_callbacks = 
  {
     mutable delete_theory : unit -> unit;
     mutable reduce_eq : ast -> ast -> ast option;
     mutable reduce_app : func_decl -> ast array -> ast option;
     mutable reduce_distinct : ast array -> ast option;
     mutable final_check : unit -> bool;
     mutable new_app : ast -> unit;
     mutable new_elem : ast -> unit;
     mutable init_search: unit -> unit;
     mutable push: unit -> unit;
     mutable pop: unit -> unit;
     mutable restart : unit -> unit;
     mutable reset: unit -> unit;
     mutable new_eq : ast -> ast -> unit;
     mutable new_diseq : ast -> ast -> unit;
     mutable new_assignment: ast -> bool -> unit;
     mutable new_relevant : ast -> unit;
  }

let mk_theory_callbacks() = 
    {
     delete_theory = (fun () -> ());
     reduce_eq = (fun _ _ -> None);
     reduce_app = (fun _ _ -> None);
     reduce_distinct = (fun _ -> None);
     final_check = (fun _ -> true);
     new_app = (fun _ -> ());
     new_elem = (fun _ -> ());
     init_search= (fun () -> ());
     push= (fun () -> ());
     pop= (fun () -> ());
     restart = (fun () -> ());
     reset= (fun () -> ());
     new_eq = (fun _ _ -> ());
     new_diseq = (fun _ _ -> ());
     new_assignment = (fun _ _ -> ());
     new_relevant = (fun _ -> ());
    }


external get_theory_callbacks : theory -> theory_callbacks = \"get_theory_callbacks\"
external mk_theory_register : context -> string -> theory_callbacks -> theory = \"mk_theory_register\"
external set_delete_callback_register : theory -> unit = \"set_delete_callback_register\"
external set_reduce_app_callback_register : theory -> unit = \"set_reduce_app_callback_register\"
external set_reduce_eq_callback_register : theory -> unit = \"set_reduce_eq_callback_register\"
external set_reduce_distinct_callback_register : theory -> unit = \"set_reduce_distinct_callback_register\"
external set_new_app_callback_register : theory -> unit = \"set_new_app_callback_register\"
external set_new_elem_callback_register : theory -> unit = \"set_new_elem_callback_register\"
external set_init_search_callback_register : theory -> unit = \"set_init_search_callback_register\"
external set_push_callback_register : theory -> unit = \"set_push_callback_register\"
external set_pop_callback_register : theory -> unit = \"set_pop_callback_register\"
external set_restart_callback_register : theory -> unit = \"set_restart_callback_register\"
external set_reset_callback_register : theory -> unit = \"set_reset_callback_register\"
external set_final_check_callback_register : theory -> unit = \"set_final_check_callback_register\"
external set_new_eq_callback_register : theory -> unit = \"set_new_eq_callback_register\"
external set_new_diseq_callback_register : theory -> unit = \"set_new_diseq_callback_register\"
external set_new_assignment_callback_register : theory -> unit = \"set_new_assignment_callback_register\"
external set_new_relevant_callback_register : theory -> unit = \"set_new_relevant_callback_register\"

let is_some opt = 
    match opt with
    | Some v -> true
    | None   -> false

let get_some opt = 
    match opt with
    | Some v -> v
    | None   -> failwith \"None unexpected\"

  


let apply_delete (th:theory_callbacks) = th.delete_theory ()
let set_delete_callback th cb = 
    let cbs = get_theory_callbacks th in
    cbs.delete_theory <- cb;
    set_delete_callback_register th

let mk_theory context name = 
    Callback.register \"is_some\" is_some;
    Callback.register \"get_some\" get_some;
    Callback.register \"apply_delete\" apply_delete;
    let cbs = mk_theory_callbacks() in
    mk_theory_register context name cbs


let apply_reduce_app (th:theory_callbacks) f args = th.reduce_app f args
let set_reduce_app_callback th cb = 
    Callback.register \"apply_reduce_app\" apply_reduce_app;
    let cbs = get_theory_callbacks th in
    cbs.reduce_app <- cb;
    set_reduce_app_callback_register th

let apply_reduce_eq (th:theory_callbacks) a b = th.reduce_eq a b
let set_reduce_eq_callback th cb = 
    Callback.register \"apply_reduce_eq\" apply_reduce_eq;
    let cbs = get_theory_callbacks th in
    cbs.reduce_eq <- cb;
    set_reduce_eq_callback_register th

let apply_reduce_distinct (th:theory_callbacks) args = th.reduce_distinct args
let set_reduce_distinct_callback th cb = 
    Callback.register \"apply_reduce_distinct\" apply_reduce_distinct;
    let cbs = get_theory_callbacks th in
    cbs.reduce_distinct <- cb;
    set_reduce_distinct_callback_register th
 

let apply_new_app (th:theory_callbacks) a = th.new_app a
let set_new_app_callback th cb = 
    Callback.register \"apply_new_app\" apply_new_app;
    let cbs = get_theory_callbacks th in
    cbs.new_app <- cb;
    set_new_app_callback_register th

let apply_new_elem (th:theory_callbacks) a = th.new_elem a
let set_new_elem_callback th cb = 
    Callback.register \"apply_new_elem\" apply_new_elem;
    let cbs = get_theory_callbacks th in
    cbs.new_elem <- cb;
    set_new_elem_callback_register th


let apply_init_search (th:theory_callbacks) = th.init_search()
let set_init_search_callback th cb = 
    Callback.register \"apply_init_search\" apply_init_search;
    let cbs = get_theory_callbacks th in
    cbs.init_search <- cb;
    set_init_search_callback_register th


let apply_push (th:theory_callbacks) = th.push()
let set_push_callback th cb = 
    Callback.register \"apply_push\" apply_push;
    let cbs = get_theory_callbacks th in
    cbs.push <- cb;
    set_push_callback_register th

let apply_pop (th:theory_callbacks) = th.pop()
let set_pop_callback th cb = 
    Callback.register \"apply_pop\" apply_pop;
    let cbs = get_theory_callbacks th in
    cbs.pop <- cb;
    set_pop_callback_register th
 

let apply_restart (th:theory_callbacks) = th.restart()
let set_restart_callback th cb = 
    Callback.register \"apply_restart\" apply_restart;
    let cbs = get_theory_callbacks th in
    cbs.restart <- cb;
    set_restart_callback_register th
 

let apply_reset (th:theory_callbacks) = th.reset()
let set_reset_callback th cb = 
    Callback.register \"apply_reset\" apply_reset;
    let cbs = get_theory_callbacks th in
    cbs.reset <- cb;
    set_reset_callback_register th

let apply_final_check (th:theory_callbacks) = th.final_check()
let set_final_check_callback th cb = 
    Callback.register \"apply_final_check\" apply_final_check;
    let cbs = get_theory_callbacks th in
    cbs.final_check <- cb;
    set_final_check_callback_register th

let apply_new_eq (th:theory_callbacks) a b = th.new_eq a b
let set_new_eq_callback th cb = 
    Callback.register \"apply_new_eq\" apply_new_eq;
    let cbs = get_theory_callbacks th in
    cbs.new_eq <- cb;
    set_new_eq_callback_register th


let apply_new_diseq (th:theory_callbacks) a b = th.new_diseq a b
let set_new_diseq_callback th cb = 
    Callback.register \"apply_new_diseq\" apply_new_diseq;
    let cbs = get_theory_callbacks th in
    cbs.new_diseq <- cb;
    set_new_diseq_callback_register th

let apply_new_assignment (th:theory_callbacks) a b = th.new_assignment a b
let set_new_assignment_callback th cb = 
    Callback.register \"apply_new_assignment\" apply_new_assignment;
    let cbs = get_theory_callbacks th in
    cbs.new_assignment <- cb;
    set_new_assignment_callback_register th

let apply_new_relevant (th:theory_callbacks) a = th.new_relevant a
let set_new_relevant_callback th cb = 
    Callback.register \"apply_new_relevant\" apply_new_relevant;
    let cbs = get_theory_callbacks th in
    cbs.new_relevant <- cb;
    set_new_relevant_callback_register th

");
