(*
   Z3CheckedGraphTests.fst

   Executable tests of the checked expression graph (`Z3CheckedGraph`), run
   natively (the OCaml bridge tests and `Z3CherryTests.run`) and verified with
   the F* test modules:

   * a shared subterm is one node, and every node stores exactly its
     expression (a variable used twice, an application of it, a quantifier
     over the application, an array sort and a lambda);
   * a child that is not a node of the graph is refused (`BuildInvalid`);
   * at the exact units of a build it succeeds and one unit short it is
     exhausted in that phase, never refused.
*)
module Z3CheckedGraphTests

open Z3AstTheory
module CG = Z3CheckedGraph
module T = Z3CheckedTerms

let int_s : sort = BaseSort "Int"

noeq
type sample = { graph: CG.cgraph; var: nat; app: nat; quant: nat; lam: nat }

(* x = Var 0 Int; f(x, x) : Bool; forall Int. f(x, x); lambda Int. x : Array Int Int. *)
let build (prep store:nat) : option sample =
  let g = CG.empty prep store in
  match CG.base_sort g "Int" with
  | CG.Sorted g i ->
    (match CG.base_sort g "Bool" with
     | CG.Sorted g b ->
       (match CG.add_var g 0 i with
        | CG.Built g x ->
          (match CG.new_decl g "f" None [] [x; x] b with
           | CG.Declared g d ->
             (match CG.add_app g d [x; x] with
              | CG.Built g a ->
                (match CG.add_quant g Forall_k [i] a with
                 | CG.Built g q ->
                   (match CG.add_quant g Lambda_k [i] x with
                    | CG.Built g l -> Some { graph = g; var = x; app = a; quant = q; lam = l }
                    | _ -> None)
                 | _ -> None)
              | _ -> None)
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

let f_decl : func_decl =
  { decl_name = "f"; domain = [int_s; int_s]; range = bool_sort; interp = None; int_params = [] }

let x_e : expr = Var 0 int_s

let shared_cases () : bool =
  match build 100000 100000 with
  | Some s ->
    CG.node_count s.graph = 4 &&
    CG.value_of s.graph s.app = Some (App f_decl [x_e; x_e]) &&
    CG.value_of s.graph s.quant = Some (Quantifier Forall_k [int_s] bool_sort (App f_decl [x_e; x_e])) &&
    CG.value_of s.graph s.lam = Some (Quantifier Lambda_k [int_s] (ArraySort [int_s] int_s) x_e) &&
    (match CG.node_of s.graph s.app with
     | Some (T.ENApp ok [c1; c2] _) -> ok && c1 = s.var && c2 = s.var
     | _ -> false)
  | None -> false

let invalid_cases () : bool =
  match build 100000 100000 with
  | Some s ->
    let g = s.graph in
    (match CG.base_sort g "Bool" with
     | CG.Sorted g b ->
       (match CG.new_decl g "f" None [] [s.var; s.var] b with
        | CG.Declared g d ->
          CG.BuildInvalid? (CG.add_app g d [s.var; 7]) &&
          CG.BuildInvalid? (CG.add_quant g Forall_k [] 4) &&
          CG.DeclInvalid? (CG.new_decl g "f" None [] [9] b)
        | _ -> false)
     | _ -> false)
  | None -> false

let outcome (prep store:nat) : int =
  match build prep store with
  | Some _ -> 0
  | None -> 1

(* The units of `build`: the smallest budgets with which it succeeds, and
   with one unit less it fails (by exhaustion: `build` refuses nothing). *)
let boundary_cases () : bool =
  match build 100000 100000 with
  | Some s ->
    s.graph.CG.prep < 100000 && s.graph.CG.store < 100000 &&
    (let p : nat = 100000 - s.graph.CG.prep in
     let st : nat = 100000 - s.graph.CG.store in
     outcome p st = 0 && outcome (p - 1) st = 1 && outcome p (st - 1) = 1)
  | None -> false

let run () : bool = shared_cases () && invalid_cases () && boundary_cases ()
