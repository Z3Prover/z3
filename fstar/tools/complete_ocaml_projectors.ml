open Asttypes
open Parsetree
open Ast_helper

module Names = Set.Make (String)

(* Extraction erases a constructor projector's domain refinement. Add a
   rejecting arm, never a value-producing fallback, to that generated code. *)
let complete structure =
  let constructors = List.fold_left (fun names item ->
      match item.pstr_desc with
      | Pstr_type (_, types) ->
          List.fold_left (fun names declaration ->
              match declaration.ptype_kind with
              | Ptype_variant (_ :: _ :: _ as cases) ->
                  List.fold_left (fun names case ->
                      Names.add case.pcd_name.txt names) names cases
              | _ -> names) names types
      | _ -> names) Names.empty structure in
  let count = ref 0 in
  let binding binding =
    match binding.pvb_pat.ppat_desc with
    | Ppat_var name when String.starts_with ~prefix:"__proj__" name.txt ->
        let expr self expression =
          let expression = Ast_mapper.default_mapper.expr self expression in
          match expression.pexp_desc with
          | Pexp_match (value, [{ pc_lhs = { ppat_desc =
                  Ppat_construct ({ txt = Longident.Lident constructor; _ }, _); _ };
                  pc_guard = None; _ } as case])
              when Names.mem constructor constructors ->
              incr count;
              let error = Exp.apply (Exp.ident (Location.mknoloc
                  (Longident.Ldot (Longident.Lident "Stdlib", "invalid_arg"))))
                  [Nolabel, Exp.constant (Const.string
                      ("Invalid extracted constructor projector: " ^ name.txt))] in
              { expression with pexp_desc =
                  Pexp_match (value, [case; Exp.case (Pat.any ()) error]) }
          | _ -> expression in
        let mapper = { Ast_mapper.default_mapper with expr } in
        { binding with pvb_expr = mapper.expr mapper binding.pvb_expr }
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
  let structure, count = complete structure in
  if count > 0 then begin
    let temporary = path ^ ".complete" in
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
  Printf.printf "Made %d extracted constructor projectors exhaustive\n%!" count
