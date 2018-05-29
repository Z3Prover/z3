open Cil
open Core
open Core.Std
open Yojson

(* Includes types UInt64, Bool and Array that NAPI does not define but should *)
type napi_prim = 
    | Int
    | UInt
    | Int64
    | UInt64
    | Bool
    | Double
    | String
    | External
    | Array
    | Empty

exception NotSupported of string



type ir_arg = {arg_c_type: string; arg_napi_type: napi_prim; arg_name: string}
type ir_decl = {fn_name: string; arg_list: ir_arg list; fn_c_type: string; fn_napi_type: napi_prim}

class cSerializer = object
    inherit defaultCilPrinterClass

    method! pAttrs () _ = Pretty.nil
end

let serializer = new cSerializer

(* Check if pointer declaration is annotated with const (inferred as array) *)
let has_const = List.exists ~f:(function | Attr(x, _) -> (String.equal "const" x))

let print_c_type t = Pretty.sprint ~width:80 (printType serializer () t)

let print_c_type' t = Pretty.sprint ~width:80 (printType defaultCilPrinter () t)

let print_loc loc  = Pretty.sprint ~width:80 (d_loc () loc)

let print_attrs attrs  = Pretty.sprint ~width:80 (d_attrlist () attrs)


(* Used in API type check *)
let print_napi_type = function
    | Int 
    | UInt 
    | Int64 
    | UInt64 
    | Bool 
    | Double -> "number"
    | String -> "string"
    | External -> "external"
    | Array -> "array"
    | Empty -> ""

(* Used in API type coercion *)
let print_napi_builder = function
    | Int -> "int32"
    | UInt -> "uint32"
    | Int64 
    | UInt64 -> "int64"
    | Bool -> "int32"
    | Double -> "double"
    | String -> "string"
    | External -> "external"
    | Array -> "array"
    | Empty -> ""

let rec c_to_napi no_void ct vdecl = 
   match ct with
     | TEnum(_) -> Int
     | TInt(itype, _) ->
       (
       match itype with
         | IBool -> Bool
         | IInt | IShort | ILong -> Int
         | IUInt | IUShort | IULong -> UInt
         | ILongLong | IULongLong -> Int64
         | _ -> raise (NotSupported ("Int type not supported: "^(print_loc vdecl)^" "^(print_c_type ct)))
       )
     | TFloat(_) -> Double
     | TPtr(TInt(IChar, _), _) | TPtr(TInt(ISChar, _), _) | TPtr(TInt(IUChar, _), _) -> String
     | TPtr(TNamed(_, (x::y)), _) -> if has_const (x::y) then Array else External
     | TPtr(_) -> External
     | TVoid(_) -> if no_void then raise (NotSupported "Void arg not supported") else Empty
     | TNamed(tinfo,_) -> c_to_napi no_void (tinfo.ttype) vdecl
     | _ -> raise (NotSupported ("Type not supported: "^(print_loc vdecl)^" " ^(print_c_type ct)))

let carg_to_napi = c_to_napi true
let cret_to_napi = c_to_napi false

let vfdec prefix fn_name rtype args vdecl =
    let process = 
        match prefix with
        | None -> true
        | Some(p) -> String.is_prefix fn_name ~prefix:p
    in
    if process then
    begin
      let map_arg (arg_name, ct, _) =
          { arg_name; arg_c_type = print_c_type ct; arg_napi_type = carg_to_napi ct vdecl }
      in 
      let real_args = 
          match args with
          | None -> []
          | Some(a) -> a
      in
      let arg_list = List.map ~f:map_arg real_args in
      let fn_napi_type = cret_to_napi rtype vdecl in
      let fn_c_type = print_c_type rtype in
      let decl = {fn_name; arg_list; fn_napi_type; fn_c_type} in
          Some (decl)
    end
    else None

let arg_to_json arg : Yojson.Basic.json =
  `Assoc [("name", `String arg.arg_name);("c_type", `String arg.arg_c_type);("napi_type", `String (print_napi_type arg.arg_napi_type));("napi_builder", `String (print_napi_builder arg.arg_napi_type))]

let decl_to_json def : Yojson.Basic.json =
  let arg_list_json = (List.map ~f:arg_to_json (def.arg_list)) in
    `Assoc [("name", `String def.fn_name);("c_type", `String def.fn_c_type);("napi_type", `String (print_napi_type def.fn_napi_type));("arg_list", `List arg_list_json);("napi_builder", `String (print_napi_builder def.fn_napi_type))]

let const_to_json (n, i)  =
  let i32 = Int64.to_int i in
  match i32 with
  | None -> raise (NotSupported "64 bit enum")
  | Some(smalli) ->
      `Assoc [(n, `Int smalli)]
   
let decls_to_json defs (cdefs: (string * int64) list)  =
  `Assoc [("api", `List (List.map ~f:decl_to_json defs));("consts", `List (List.map ~f:const_to_json cdefs))]
      
class cdeclToJSON prefix = object
  inherit nopCilVisitor 
 
  val mutable acc = []
  val mutable enums = []

  method get_acc () : (ir_decl list) = acc
  method get_consts () : ((string*int64) list) = enums
  
  method! vglob = function
    (* typedef named enum *)
    | GType({ttype = 
               TNamed({ttype=
                         TEnum({eitems = items;_},_);_},_);_},_) 
    (* named enum *)
    | GType({ttype = 
                         TEnum({eitems = items;_},_);_},_) -> 
                 let fenums = List.filter ~f:(function | (_, Const(_), _) -> true | _ -> false) items in
                 let menums = List.map ~f:(function | (name, Const(CInt64(i, _, _)), _) -> (name, i) | _ -> raise (NotSupported "Unsupported enum variant")) fenums in
                  enums <- enums @ menums;
                  SkipChildren
    | _ -> DoChildren
   
    
  method! vvdec {vtype;vname;vdecl;_} : varinfo visitAction = 
    (
    match vtype with
      | TFun(rtype, args, _, _) -> 
	    let decl = vfdec prefix vname rtype args vdecl in
            (
            match decl with
              | None -> ()
              | Some(d) -> acc <- d::acc
            )
      | _ -> ()
    );SkipChildren
end

let print_defs chan defs cdefs = 
  let json = decls_to_json defs cdefs in
    Yojson.Basic.pretty_to_channel chan json 

let convert prefix chan filename = 
  let jsonifyVisitor = new cdeclToJSON prefix in
  let f = Frontc.parse filename () in
    visitCilFileSameGlobals (jsonifyVisitor :> nopCilVisitor) f;
    let defs = jsonifyVisitor#get_acc() in
    let cdefs = jsonifyVisitor#get_consts() in
      print_defs chan (List.rev defs) (List.rev cdefs)

let command =
    Command.basic
        ~summary: "Convert C function declarations to JSON to be fed into a template-based pretty printer"
        Command.Spec.(
          empty
          +> flag "-prefix" (optional string) ~doc:"string Filter to files with this prefix"
          +> flag "-o" (optional string) ~doc:"string Output json file (default: <filename>.json)"
          +> anon ("filename" %: string)
        )
        (fun prefix ofilename filename () ->
	    let output_file = match ofilename with None -> filename ^ ".json" | Some(output_file_name) -> output_file_name in
	    let chan = Out_channel.create output_file in
	        convert prefix chan filename
	)

let () =
    Command.run ~version:"0.1" command
