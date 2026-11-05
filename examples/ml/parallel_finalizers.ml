(* Contexts and their solvers must be finalized on different domain heaps.
   Keep the allocating domain alive while the main domain requests major GCs. *)
let run cross_domain =
  let contexts = Atomic.make [] in
  let requested = Atomic.make false in
  let ready = Atomic.make false in
  let stop = Atomic.make false in
  let worker = Domain.spawn (fun () ->
    while not (Atomic.get stop) do
      if Atomic.exchange requested false then begin
        Atomic.set contexts (List.init 30 (fun _ ->
          let ctx = Z3.mk_context [] in
          let solver =
            if cross_domain then None
            else Some (Z3.Solver.mk_solver ctx None)
          in
          ctx, solver));
        Atomic.set ready true
      end else
        Domain.cpu_relax ()
    done)
  in
  let[@inline never] make_solvers () =
    let batch = Atomic.exchange contexts [] in
    let solvers = List.map (fun (ctx, solver) ->
      match solver with
      | Some solver -> solver
      | None -> Z3.Solver.mk_solver ctx None) batch
    in
    ignore (Sys.opaque_identity solvers)
  in
  for _ = 1 to 40 do
    Atomic.set requested true;
    while not (Atomic.get ready) do Domain.cpu_relax () done;
    Atomic.set ready false;
    make_solvers ();
    Gc.full_major ()
  done;
  Atomic.set stop true;
  Domain.join worker;
  Gc.full_major ()

let () =
  run false;
  run true;
  print_endline "Parallel context finalizers: OK"
