(*
  queen.exe - JakobL@2007-09-22

  Demonstration of how Z3 can be used to find solutions to the
  N-Queens problem.

  See: http://en.wikipedia.org/wiki/Eight_queens_puzzle

  Problem specification: Is the following constraint system satisfiable,
  for increasing n>=1, what are the models?

    constant
      n: 8;

    variable
      row: array n of [0..n-1];

    rule
      forall i in [0..n-2]:
        (forall j in [i+1..n-1]:
           ((row[i] <> row[j]) and 
           (i+row[i]) <> (j+row[j]) and
           (i+row[j]) <> (j+row[i])));

  The answer is yes for n different from 2 and 3.  The number of solutions are:
    * n=1: 1
    * n=2: 0
    * n=3: 0
    * n=4: 2
    * n=5: 10
    * n=6: 4
    * n=7: 40
    * n=8: 92
    * n=9: 352
    * n=10: 724
    ...
*)

module Z3 = Z3.V3

(* Auxillary functions *)
let ( |> ) x f = f x;;
let printf = Printf.printf;;
let mk_var ctx name ty = Z3.mk_const ctx (Z3.mk_int_symbol ctx name) ty;;
let mk_int_var ctx name = Z3.mk_int_sort ctx |> mk_var ctx name;;
let mk_int ctx v = Z3.mk_int ctx v (Z3.mk_int_sort ctx);;
let checkreturn v = match v with | (true,r) -> r | _ -> failwith "checkreturn";;
let get_numeral_value_int a1 a2 = Z3.get_numeral_int a1 a2 |> checkreturn;;
let iterate_x lower upper f = for i = lower to upper do f i done;;
let forall_x ctx lower upper f = Z3.mk_and ctx (Array.init (1+upper-lower) (fun i->f (i+lower)))
let exist_x ctx lower upper f = Z3.mk_or ctx (Array.init (1+upper-lower) (fun i->f (i+lower)))
let get_value ctx model f = let (ok, v) = Z3.eval_func_decl ctx model f in (assert ok; v)

let queen_n n =
  let ctx = Z3.mk_context_x
    [|("MODEL","true");
      ("RELEVANCY","0")|] in
  let ( &&& ) x y = Z3.mk_and ctx [|x;y|] in
  let ( <~> ) x y = Z3.mk_not ctx (Z3.mk_eq ctx x y) in
  let ( <<= ) x y = Z3.mk_le ctx x y in
  let ( +++ ) x y = Z3.mk_add ctx [|x;y|] in
  let row = Array.init n (fun i->mk_int_var ctx i) in
  let c x =  mk_int ctx x in (* make constant *)
  let v x =  row.(x) in (* make variable *)
  let constraint_domain=forall_x ctx (0) (n-1) (fun x-> ((c 0) <<= (v x)) &&& ((v x) <<= (c (n-1)))) in
  let constraint_queen=
    forall_x ctx (0) (n-2) (fun i->
      forall_x ctx (i+1) (n-1) (fun j->
         ((v i) <~> (v j)) &&&
         (((c i)+++(v i)) <~> ((c j)+++(v j))) &&&
         (((c i)+++(v j)) <~> ((c j)+++(v i)))
       )
    ) in
  let res = constraint_domain &&& constraint_queen in
  Z3.assert_cnstr ctx res;
  let rec f i =
    (match Z3.check_and_get_model ctx with
    | (Z3.L_FALSE,_) ->
      printf "queen %d, total models: %d\n" n i;
      flush stdout;
    | (Z3.L_UNDEF,_) -> failwith "Z3.L_UNDEF"
    | (Z3.L_TRUE,model) ->
    begin
      let model_constants=Z3.get_model_constants ctx model in
      let vars=Array.map (fun mc->Z3.mk_app ctx mc [||]) model_constants in
      let vals=Array.map (fun mc->get_value ctx model mc |> get_numeral_value_int ctx) model_constants in
      Z3.del_model ctx model;

      let line = String.make n '-' in
      let q_line i = let r = String.make n ' ' in String.set r i 'Q'; r in
      printf "queen %d, model #%d:\n" n (i+1);
      printf "\n";
      printf "  /%s\\\n" line;
      iterate_x 0 (n-1) (fun x->printf "  |%s|\n" (q_line (vals.(x))));
      printf "  \\%s/\n" line;
      printf "\n";
      flush stdout;
      let negated_model = exist_x ctx 0 (n-1) (fun x->(vars.(x)) <~> (c (vals.(x)))) in
      Z3.assert_cnstr ctx negated_model;
      f (i+1);
    end
    ) in
  f 0;
  Z3.del_context ctx;
  ();;

let queen() =
  for n = 1 to 8 do
    queen_n n
  done;;

let _ = queen();;
