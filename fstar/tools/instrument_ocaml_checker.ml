open Asttypes
open Parsetree
open Ast_helper

let timed = [
  "Z3ProofDocument.check_document_with_lookup"; "Z3ProofDocument.check_entry_with_lookup";
  "Z3UnifiedProof.check_node_with_membership"; "Z3UnifiedProof.relational_step";
  "Z3UnifiedProof.fast_arguments_match";
  "Z3BooleanRewrite.boolean_equiv"; "Z3BooleanRewrite.boolean_search";
  "Z3ArrayRewrite.equivalent"; "Z3ArithmeticRewrite.equivalent";
  "Z3QuantifierReduce.equivalent"; "Z3LambdaRewrite.rewrite";
  "Z3ConditionalRewrite.equivalent"; "Z3IntegerRewrite.equivalent";
  "Z3QuantifierVacuity.equivalent"; "Z3TheoryNormalize.equivalent";
  "Z3TheoryNormalize.root"; "Z3TheoryNormalize.consequence";
  "Z3DestructiveEquality.check"; "Z3LinearArithmeticAst.check";
  "Z3NativeProof.marshal";
]

let counted = [
  "Z3BooleanRewrite.boolean_height"; "Z3BooleanRewrite.boolean_cut";
  "Z3BooleanNormalForm.normalize"; "Z3BooleanNormalForm.shannon";
  "Z3Definitions.scoped"; "Z3Definitions.expand"; "Z3Definitions.tautology";
  "Z3TheoryNormalize.normalize"; "Z3BinderSubstitution.apply";
  "Z3LinearArithmeticAst.linearize"; "Z3UnifiedProof.extend_reachable";
  "Z3UnifiedProof.arguments_match";
]

let expression text = Parse.expression (Lexing.from_string text)

let apply name args =
  let identifier = match Longident.unflatten (String.split_on_char '.' name) with
    | Some identifier -> identifier
    | None -> invalid_arg ("Invalid profiling identifier: " ^ name) in
  Exp.apply (Exp.ident (Location.mknoloc identifier))
    (List.map (fun arg -> Nolabel, arg) args)

let rule_label structure =
  let constructors = List.concat_map (fun item ->
    match item.pstr_desc with
    | Pstr_type (_, declarations) ->
        List.concat_map (fun declaration ->
          match declaration.ptype_name.txt, declaration.ptype_kind with
          | "rule", Ptype_variant cases -> cases
          | _ -> []) declarations
    | _ -> []) structure in
  if constructors = [] then invalid_arg "Missing extracted rule datatype";
  let arms = List.map (fun constructor ->
    let name = constructor.pcd_name.txt in
    match name, constructor.pcd_args with
    | "Unverified", Pcstr_tuple [_] ->
        "| Unverified name -> \"rule/\" ^ name"
    | _, Pcstr_tuple [] -> Printf.sprintf "| %s -> \"rule/%s\"" name name
    | _, Pcstr_tuple [_] -> Printf.sprintf "| %s _ -> \"rule/%s\"" name name
    | _ -> invalid_arg ("Unexpected extracted rule constructor: " ^ name)) constructors in
  expression ("match node.kind with " ^ String.concat " " arms)

let instrument module_name structure =
  let count = ref 0 in
  let binding binding =
    match binding.pvb_pat.ppat_desc with
    | Ppat_var name ->
        let key = module_name ^ "." ^ name.txt in
        let timing = List.mem key timed in
        if not timing && not (List.mem key counted) then binding
        else
          let label =
            if key = "Z3UnifiedProof.check_node_with_membership" then rule_label structure
            else Exp.constant (Const.string key) in
          let wrap body =
            incr count;
            if timing then
              let thunk = match (expression "fun () -> ()").pexp_desc with
                | Pexp_function (parameters, constraint_, Pfunction_body _) ->
                    Exp.mk (Pexp_function (parameters, constraint_, Pfunction_body body))
                | _ -> assert false in
              apply "Z3Profile.measure" [label; thunk]
            else Exp.sequence (apply "Z3Profile.visit" [label]) body in
          let rec function_body expr =
            match expr.pexp_desc with
            | Pexp_function (parameters, constraint_, Pfunction_body body) ->
                { expr with pexp_desc =
                    Pexp_function (parameters, constraint_, Pfunction_body (wrap body)) }
            | Pexp_constraint (body, typ) ->
                { expr with pexp_desc = Pexp_constraint (function_body body, typ) }
            | _ -> invalid_arg ("Unexpected extracted function shape: " ^ key) in
          { binding with pvb_expr = function_body binding.pvb_expr }
    | _ -> binding in
  let structure = List.map (fun item ->
    match item.pstr_desc with
    | Pstr_value (recursive, bindings) ->
        { item with pstr_desc = Pstr_value (recursive, List.map binding bindings) }
    | _ -> item) structure in
  structure, !count

let rewrite path =
  let input = open_in path in
  let structure = Fun.protect ~finally:(fun () -> close_in input) (fun () ->
    let lexbuf = Lexing.from_channel input in
    Location.init lexbuf path;
    Parse.implementation lexbuf) in
  let module_name = Filename.basename path |> Filename.remove_extension in
  let structure, count = instrument module_name structure in
  if count > 0 then begin
    let temporary = path ^ ".profile" in
    let output = open_out temporary in
    Fun.protect ~finally:(fun () -> close_out output) (fun () ->
      let formatter = Format.formatter_of_out_channel output in
      Pprintast.structure formatter structure;
      Format.pp_print_newline formatter ());
    Sys.rename temporary path
  end;
  count

let () =
  let count = Array.fold_left (fun count path -> count + rewrite path)
    0 (Array.sub Sys.argv 1 (Array.length Sys.argv - 1)) in
  if count <> List.length timed + List.length counted then
    failwith (Printf.sprintf "Expected %d profiling functions, instrumented %d"
      (List.length timed + List.length counted) count);
  Printf.printf "Instrumented %d checker functions (profiling build only)\n%!" count
