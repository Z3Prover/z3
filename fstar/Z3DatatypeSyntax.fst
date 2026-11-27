module Z3DatatypeSyntax

open Z3AstTheory
module L = FStar.List.Tot

let op_constructor : decl_kind = 200
let op_recognizer : decl_kind = 201
let op_accessor : decl_kind = 202

let constructor (f:func_decl) (args:list expr) : option (int & int) =
  if f.interp <> Some op_constructor || not (sorts_match args f.domain) then None
  else match f.int_params with
  | [owner; tag; arity] ->
    if owner >= 0 && tag >= 0 && arity = L.length args then Some (owner, tag) else None
  | _ -> None

let recognizer (f:func_decl) (arg:expr) : option (int & int) =
  if f.interp <> Some op_recognizer || f.range <> bool_sort || f.domain <> [get_sort arg]
  then None
  else match f.int_params with
  | [owner; tag] -> if owner >= 0 && tag >= 0 then Some (owner, tag) else None
  | _ -> None

let accessor (f:func_decl) (arg:expr) : option (int & int & nat) =
  if f.interp <> Some op_accessor || f.domain <> [get_sort arg] then None
  else match f.int_params with
  | [owner; tag; index] ->
    if owner >= 0 && tag >= 0 && index >= 0 then Some (owner, tag, index) else None
  | _ -> None
