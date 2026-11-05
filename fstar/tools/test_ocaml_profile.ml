let require condition message = if not condition then failwith message

let () =
  require Z3Profile.enabled "profiling fixture requires Z3_FSTAR_PROFILE=1";
  let result = Z3Profile.measure "parent" (fun () ->
    Z3Profile.visit "visits";
    Z3Profile.visit "visits";
    Z3Profile.measure "child" (fun () -> 42)) in
  require (result = 42) "profiling changed the returned value";
  let raised =
    try Z3Profile.measure "raises" (fun () -> raise Exit)
    with Exit -> true in
  require raised "profiling swallowed an exception";
  require (!(Z3Profile.stack) = []) "exception left a profiling frame active";
  let visits = Hashtbl.find Z3Profile.counters "visits" in
  require (visits.calls = 2) "recursive visit counts were not retained";
  let parent = Hashtbl.find Z3Profile.counters "parent" in
  let child = Hashtbl.find Z3Profile.counters "child" in
  require (parent.calls = 1 && child.calls = 1) "timed call counts changed";
  require (parent.seconds >= child.seconds && parent.bytes >= child.bytes)
    "nested inclusive accounting is inconsistent";
  require (parent.self_seconds >= 0. && parent.self_bytes >= 0.)
    "nested exclusive accounting is negative";
  require (Z3Profile.json_string "\"\\\n\r\t\000" = "\"\\\"\\\\\\n\\r\\t\\u0000\"")
    "profile names were not JSON escaped";
  print_endline "PASS profile-accounting-and-exceptions"
