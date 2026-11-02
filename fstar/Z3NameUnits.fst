module Z3NameUnits

let scan_units s limit =
  let n = FStar.String.strlen s in
  if n <= limit then n else -1
