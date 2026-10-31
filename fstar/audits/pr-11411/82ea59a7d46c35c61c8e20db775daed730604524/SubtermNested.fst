module SubtermNested
open FStar.List.Tot

(* Model of the PR's worklist in mk_subterm. Sorts are nat ids; d is domain[0].
   succ s = accessor ranges (if s is a datatype) @ sort parameters. *)
type succ_t = nat -> list nat

(* None = raise_exception. Fuel exhaustion also conservatively raises. *)
let rec run (succ:succ_t) (d:nat) (fuel:nat) (todo visited:list nat) : Tot (option (list nat)) (decreases fuel) =
  if fuel = 0 then None else
  match todo with
  | [] -> Some visited
  | s :: rest ->
    if mem s visited then run succ d (fuel-1) rest visited
    else if s = d then None
    else run succ d (fuel-1) (succ s @ rest) (s :: visited)

let closed (succ:succ_t) (v:list nat) = forall x y. mem x v /\ mem y (succ x) ==> mem y v

let inv (succ:succ_t) (d:nat) (init todo visited:list nat) =
  ~(mem d visited) /\
  (forall x. mem x init ==> mem x visited \/ mem x todo) /\
  (forall x y. mem x visited /\ mem y (succ x) ==> mem y visited \/ mem y todo)

let rec sound (succ:succ_t) (d:nat) (init:list nat) (fuel:nat) (todo visited:list nat)
  : Lemma (requires inv succ d init todo visited)
          (ensures (match run succ d fuel todo visited with
                    | None -> True
                    | Some v -> ~(mem d v) /\ (forall x. mem x init ==> mem x v) /\ closed succ v))
          (decreases fuel) =
  if fuel = 0 then () else
  match todo with
  | [] -> ()
  | s :: rest ->
    if mem s visited then sound succ d init (fuel-1) rest visited
    else if s = d then ()
    else begin
      FStar.Classical.forall_intro (append_mem (succ s) rest);
      sound succ d init (fuel-1) (succ s @ rest) (s :: visited)
    end

(* Top-level: if no exception, every sort reachable from the initial todo
   (the non-self accessor ranges of d) is distinct from d. *)
let rec reach (succ:succ_t) (init:list nat) (x:nat) (n:nat) : Tot prop (decreases n) =
  if n = 0 then mem x init
  else mem x init \/ (exists y. reach succ init y (n-1) /\ mem x (succ y))

let rec reach_in (succ:succ_t) (init v:list nat) (x n:nat)
  : Lemma (requires (forall z. mem z init ==> mem z v) /\ closed succ v /\ reach succ init x n)
          (ensures mem x v) (decreases n) =
  if n = 0 then () else if mem x init then () else begin
    eliminate exists y. reach succ init y (n-1) /\ mem x (succ y)
    with (reach_in succ init v y (n-1))
  end

let no_nested (succ:succ_t) (d:nat) (init:list nat) (fuel:nat) (x n:nat)
  : Lemma (requires Some? (run succ d fuel init []) /\ reach succ init x n)
          (ensures x <> d) =
  sound succ d init fuel init [];
  match run succ d fuel init [] with
  | Some v -> reach_in succ init v x n
