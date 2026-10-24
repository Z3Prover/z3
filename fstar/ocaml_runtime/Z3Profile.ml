type counter = {
  name : string;
  mutable calls : int;
  mutable seconds : float;
  mutable self_seconds : float;
  mutable bytes : float;
  mutable self_bytes : float;
}

type frame = {
  mutable child_seconds : float;
  mutable child_bytes : float;
}

let counters = Hashtbl.create 64
let stack = ref []
let enabled = match Sys.getenv_opt "Z3_FSTAR_PROFILE" with
  | None | Some "0" -> false
  | Some "1" -> true
  | Some _ -> invalid_arg "Z3_FSTAR_PROFILE must be 0 or 1"

let counter name =
  match Hashtbl.find_opt counters name with
  | Some entry -> entry
  | None ->
      let entry = {
        name; calls = 0; seconds = 0.; self_seconds = 0.;
        bytes = 0.; self_bytes = 0.;
      } in
      Hashtbl.add counters name entry;
      entry

let visit name =
  if enabled then begin
    let entry = counter name in
    entry.calls <- entry.calls + 1
  end

let measure name action =
  if not enabled then action () else
  let entry = counter name in
  entry.calls <- entry.calls + 1;
  let frame = { child_seconds = 0.; child_bytes = 0. } in
  let parent = !stack in
  stack := frame :: parent;
  let allocated = Gc.allocated_bytes () in
  let started = Unix.gettimeofday () in
  Fun.protect action ~finally:(fun () ->
    let seconds = Unix.gettimeofday () -. started in
    let bytes = Gc.allocated_bytes () -. allocated in
    stack := parent;
    entry.seconds <- entry.seconds +. seconds;
    entry.self_seconds <- entry.self_seconds +. seconds -. frame.child_seconds;
    entry.bytes <- entry.bytes +. bytes;
    entry.self_bytes <- entry.self_bytes +. bytes -. frame.child_bytes;
    match parent with
    | [] -> ()
    | outer :: _ ->
        outer.child_seconds <- outer.child_seconds +. seconds;
        outer.child_bytes <- outer.child_bytes +. bytes)

let json_string text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter (function
    | '"' -> Buffer.add_string buffer "\\\""
    | '\\' -> Buffer.add_string buffer "\\\\"
    | '\n' -> Buffer.add_string buffer "\\n"
    | '\r' -> Buffer.add_string buffer "\\r"
    | '\t' -> Buffer.add_string buffer "\\t"
    | c when Char.code c < 32 ->
        Printf.bprintf buffer "\\u%04x" (Char.code c)
    | c -> Buffer.add_char buffer c) text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let report () =
  Hashtbl.to_seq_values counters |> List.of_seq |>
  List.sort (fun a b ->
    let order = Float.compare b.self_seconds a.self_seconds in
    if order = 0 then String.compare a.name b.name else order) |>
  List.iter (fun entry ->
    Printf.eprintf
      "profile\t{\"name\":%s,\"calls\":%d,\"inclusive_ms\":%.6f,\"self_ms\":%.6f,\"allocated_bytes\":%.0f,\"self_allocated_bytes\":%.0f}\n"
      (json_string entry.name) entry.calls (1000. *. entry.seconds)
      (1000. *. entry.self_seconds) entry.bytes entry.self_bytes)

let () = if enabled then at_exit report
