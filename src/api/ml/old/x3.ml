/* Copyright (c) Microsoft Corporation */

quote (ml,"

(* Internal auxiliary functions: *)
(*
(* Transform a pair of arrays into an array of pairs *)
let array_combine a b =
  if Array.length a <> Array.length b then raise (Invalid_argument \"array_combine\");
  Array.init (Array.length a) (fun i -> (a.(i), b.(i)))

(* [a |> b] is the pipeline operator for [b(a)] *)
let ( |> ) x f = f x
*)

(* Find the index of an element in an array, raises Not_found is missing *)
let find equal x a =
  let len = Array.length a in
  let rec find_ i =
    if i >= len then
      raise Not_found
    else
      if equal x a.(i) then
        i
      else
        find_ (i+1)
  in
  find_ 0


(* Symbols *)

let symbol_refine c s =
  match get_symbol_kind c s with
  | INT_SYMBOL -> Symbol_int (get_symbol_int c s)
  | STRING_SYMBOL -> Symbol_string (get_symbol_string c s)

let mk_symbol c = function
  | Symbol_int(i) -> mk_int_symbol c i
  | Symbol_string(s) -> mk_string_symbol c s


(* Sorts *)

let get_datatype_sort c s = 
  Array.init (get_datatype_sort_num_constructors c s) (fun i -> 
    let constructor = get_datatype_sort_constructor c s i in
    let recognizer = get_datatype_sort_recognizer c s i in
    let accessors =
      Array.init (get_domain_size c constructor) (fun j ->
        get_datatype_sort_constructor_accessor c s i j
      ) in
    {constructor; recognizer; accessors}
  )

let sort_refine c s =
  match get_sort_kind c s with
  | UNINTERPRETED_SORT -> Sort_uninterpreted (get_sort_name c s)
  | BOOL_SORT -> Sort_bool
  | INT_SORT -> Sort_int
  | BV_SORT -> Sort_bv (get_bv_sort_size c s)
  | FINITE_DOMAIN_SORT ->
      (match get_finite_domain_sort_size c s with
      | Some(sz) -> Sort_finite_domain (get_sort_name c s, sz)
      | None -> failwith \"Z3.sort_refine: failed to get size of finite-domain sort\"
      )
  | REAL_SORT -> Sort_real
  | ARRAY_SORT -> Sort_array (get_array_sort_domain c s, get_array_sort_range c s)
  | DATATYPE_SORT -> Sort_datatype (get_datatype_sort c s)
  | RELATION_SORT -> Sort_relation (Array.init (get_relation_arity c s) (fun i -> get_relation_column c s i))
  | UNKNOWN_SORT -> Sort_unknown

let mk_sort c = function
  | Sort_uninterpreted(s) -> mk_uninterpreted_sort c s
  | Sort_bool -> mk_bool_sort c
  | Sort_int -> mk_int_sort c
  | Sort_bv(size) -> mk_bv_sort c size
  | Sort_finite_domain(name,size) -> mk_finite_domain_sort c name size
  | Sort_real -> mk_real_sort c
  | Sort_array(domain,range) -> mk_array_sort c domain range
  | Sort_datatype(constructors) -> get_range c constructors.(0).constructor
  | Sort_relation(_) -> invalid_arg \"Z3.mk_sort: cannot construct relation sorts\"
  | Sort_unknown(_) -> invalid_arg \"Z3.mk_sort: cannot construct unknown sorts\"


(* Replacement datatypes creation API *)

let mk_datatypes ctx generator =
  let usort0 = mk_uninterpreted_sort ctx (mk_int_symbol ctx 0)
  in
  let rec find_num_sorts i =
    if i = max_int then invalid_arg \"mk_datatypes: too many sorts\"
    else
    match generator (Array.make i usort0) with
    | None -> find_num_sorts (i+1)
    | Some(a) when Array.length a = i -> i
    | Some _ -> invalid_arg \"mk_datatypes: number of sorts and datatype descriptors must be equal\"
  in
  let num_sorts = find_num_sorts 0
  in
  let sorts0 = Array.init num_sorts (fun i -> mk_uninterpreted_sort ctx (mk_int_symbol ctx i))
  in
  let ctorss_descriptors =
    match generator sorts0 with
    | Some(ctorss_descriptors) -> ctorss_descriptors
    | None -> invalid_arg \"mk_datatypes: generator failed\"
  in
  let names = Array.map fst ctorss_descriptors
  in
  let ctorss =
    Array.map (fun (_, ctors_descriptor) ->
      Array.map (fun {constructor_desc; recognizer_desc; accessor_descs} ->
        let field_names = Array.map fst accessor_descs
        in
        let sort_refs = Array.make (Array.length accessor_descs) 0
        in
        let field_sorts =
          Array.mapi (fun i (_, sort) ->
            try
              let j = find (fun s t -> is_eq_sort ctx s t) sort sorts0 in
              sort_refs.(i) <- j ;
              None
            with Not_found ->
              Some(sort)
          ) accessor_descs
        in
        mk_constructor ctx constructor_desc recognizer_desc field_names field_sorts sort_refs
      ) ctors_descriptor
    ) ctorss_descriptors
  in
  let constructor_lists = Array.map (mk_constructor_list ctx) ctorss
  in
  let sorts,_ = mk_datatypes ctx names constructor_lists
  in
  let datatypes =
    Array.mapi (fun i sort ->
      (sort,
       Array.mapi (fun j ctor ->
         let num_fields = Array.length (snd ctorss_descriptors.(i)).(j).accessor_descs in
         let constructor, recognizer, accessors = query_constructor ctx ctor num_fields in
         {constructor; recognizer; accessors}
       ) ctorss.(i))
    ) sorts
  in
  Array.iter (fun ctor_list ->
    del_constructor_list ctx ctor_list
  ) constructor_lists
  ;
  Array.iter (fun ctors ->
    Array.iter (fun ctor ->
      del_constructor ctx ctor
    ) ctors
  ) ctorss
  ;
  datatypes


(* Numerals *)

let rec numeral_refine c t =
  assert( get_ast_kind c t = NUMERAL_AST );
  let sort = get_sort c t in
  let is_int, i = get_numeral_int c t in
  if is_int then 
    Numeral_int (i, sort)
  else
  let is_int64, i = get_numeral_int64 c t in
  if is_int64 then 
    Numeral_int64 (i, sort)
  else
  if get_sort_kind c sort <> REAL_SORT then
    Numeral_large (get_numeral_string c t, sort)
  else
    let n = numeral_refine c (get_numerator c t) in
    let d = numeral_refine c (get_denominator c t) in
    Numeral_rational (n, d)


let to_real c x =
  if get_sort_kind c (get_sort c x) = REAL_SORT then
    x
  else
    mk_int2real c x

let rec embed_numeral c = function
  | Numeral_int (i, s) -> mk_int c i s
  | Numeral_int64 (i, s) -> mk_int64 c i s
  | Numeral_large (l, s) -> mk_numeral c l s
  | Numeral_rational (Numeral_int(n,_), Numeral_int(d,_)) -> mk_real c n d
  | Numeral_rational (n, d) ->
      mk_div c (to_real c (embed_numeral c n)) (to_real c (embed_numeral c d))
      (* Or should the following be used instead?
      let n_str = get_numeral_string c (embed_numeral c n) in
      let d_str = get_numeral_string c (embed_numeral c d) in
      mk_numeral c (n_str ^ \" / \" ^ d_str) (mk_real_sort c)
      *)

(* Terms *)

let get_app_args c a =
  Array.init (get_app_num_args c a) (get_app_arg c a);;

let get_domains c d =
  Array.init (get_domain_size c d) (get_domain c d);;


let get_pattern_terms c p = 
  Array.init (get_pattern_num_terms c p) (get_pattern c p)


let term_refine c t = 
  match get_ast_kind c t with
  | NUMERAL_AST ->
      Term_numeral (numeral_refine c t)
  | APP_AST ->
      let t' = to_app c t in
      let f = get_app_decl c t' in
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
      let bound =
        Array.init nb (fun i ->
          (get_quantifier_bound_name c t i, get_quantifier_bound_sort c t i)
        ) in
      let body = get_quantifier_body c t in
      Term_quantifier (bt, w, pats, bound, body)
  | VAR_AST -> 
      Term_var (get_index_value c t, get_sort c t)
  | _ ->
      assert false


(* let mk_term c = function *)
(*   | Term_numeral (numeral, sort) -> mk_numeral c numeral sort *)
(*   | Term_app (kind, decl, args) -> *)
(*   | Term_quantifier (strength, weight, pats, bound, body) -> *)
(*   | Term_var (index, sort) -> *)



(* Refined model API *)

let model_refine c m =
  let num_sorts = model_get_num_sorts c m in
  let sorts = Hashtbl.create num_sorts in
  for i = 0 to num_sorts - 1 do
    let sort = model_get_sort c m i in
    let universe = model_get_sort_universe c m sort in
    Hashtbl.add sorts sort universe
  done;
  let num_consts = model_get_num_consts c m in
  let consts = Hashtbl.create num_consts in
  let arrays = Hashtbl.create 0 in
  for i = 0 to num_consts - 1 do
    let const_decl = model_get_const_decl c m i in
    match model_get_const_interp c m const_decl with
    | Some(const_interp) ->
        if is_as_array c const_interp then
          let array_decl = get_as_array_func_decl c const_interp in
          match model_get_func_interp c m array_decl with
          | Some(array_interp) ->
              let num_entries = func_interp_get_num_entries c array_interp in
              let tbl = Hashtbl.create num_entries in
              for i = 0 to num_entries - 1 do
                let entry = func_interp_get_entry c array_interp i in
                assert( func_entry_get_num_args c entry = 1 );
                let arg = func_entry_get_arg c entry 0 in
                let value = func_entry_get_value c entry in
                Hashtbl.add tbl arg value
              done;
              let default = func_interp_get_else c array_interp in
              Hashtbl.add arrays const_decl (tbl, default)
          | None ->
              ()
        else
          Hashtbl.add consts const_decl const_interp
    | None ->
        ()
  done;
  let num_funcs = model_get_num_funcs c m in
  let funcs = Hashtbl.create num_funcs in
  for i = 0 to num_funcs - 1 do
    let func_decl = model_get_func_decl c m i in
    if not (Hashtbl.mem arrays func_decl) then
      match model_get_func_interp c m func_decl with
      | Some(func_interp) ->
          let num_entries = func_interp_get_num_entries c func_interp in
          let tbl = Hashtbl.create num_entries in
          for i = 0 to num_entries - 1 do
            let entry = func_interp_get_entry c func_interp i in
            let num_args = func_entry_get_num_args c entry in
            let args = Array.init num_args (fun i -> func_entry_get_arg c entry i) in
            let value = func_entry_get_value c entry in
            Hashtbl.add tbl args value
          done;
          let default = func_interp_get_else c func_interp in
          Hashtbl.add funcs func_decl (tbl, default)
      | None ->
          ()
  done;
  {sorts; consts; arrays; funcs}


(* Extended parser API *)

let get_smtlib_formulas c = 
  Array.init (get_smtlib_num_formulas c) (get_smtlib_formula c)

let get_smtlib_assumptions c = 
  Array.init (get_smtlib_num_assumptions c) (get_smtlib_assumption c)

let get_smtlib_decls c =
  Array.init (get_smtlib_num_decls c) (get_smtlib_decl c)

let get_smtlib_parse_results c =
  (get_smtlib_formulas c, get_smtlib_assumptions c, get_smtlib_decls c)

let parse_smtlib_string_x c a1 a2 a3 a4 a5 = 
  parse_smtlib_string c a1 a2 a3 a4 a5 ;
  get_smtlib_parse_results c

let parse_smtlib_file_x c a1 a2 a3 a4 a5 = 
  parse_smtlib_file c a1 a2 a3 a4 a5 ;
  get_smtlib_parse_results c

let parse_smtlib_string_formula c a1 a2 a3 a4 a5 = 
  parse_smtlib_string c a1 a2 a3 a4 a5 ;
  match get_smtlib_formulas c with [|f|] -> f | _ -> failwith \"Z3: parse_smtlib_string_formula\"

let parse_smtlib_file_formula c a1 a2 a3 a4 a5 = 
  parse_smtlib_file c a1 a2 a3 a4 a5 ;
  match get_smtlib_formulas c with [|f|] -> f | _ -> failwith \"Z3: parse_smtlib_file_formula\"


(* Error handling *)

let get_error_msg c e =
  match e with
  | PARSER_ERROR -> (get_error_msg_ex c e) ^ \": \" ^ (get_smtlib_error c)
  | _ -> get_error_msg_ex c e


(* Refined stats API *)

let stats_refine c s =
  let num_stats = stats_size c s in
  let tbl = Hashtbl.create num_stats in
  for i = 0 to num_stats - 1 do
    let key = stats_get_key c s i in
    let datum =
      if stats_is_uint c s i then
        Stat_int(stats_get_uint_value c s i)
      else
        Stat_float(stats_get_double_value c s i) in
    Hashtbl.add tbl key datum
  done;
  tbl
");
