module Z3NameUnits

[@@custard_extern "z3_name_units_scan"]
let scan_units s limit =
  let n = FStar.String.strlen s in
  if n <= limit then n else -1
