module NlsatRefineApp
(* Order-level model of nlsat::transcendentals::refine_app (PR head cbe33c46).
   Rationals/algebraic numbers are modelled by int (total order only). *)

type encl = { xlo: int; xhi: int; rlo: int; rhi: int }

let contains (e:encl) (y:int) : bool = e.rlo <= y && y <= e.rhi

(* Environment assumption: enclose is sound, i.e. every point of [xlo,xhi]
   maps under f into [rlo,rhi]. Not proved here (manual review of Taylor/double code). *)
let sound (f:int -> int) (e:encl) : prop =
  forall (x:int). e.xlo <= x /\ x <= e.xhi ==> e.rlo <= f x /\ f x <= e.rhi

(* Lemma clause: arg(xlo \/ arg)xhi \/ (val>=rlo if y(rlo, else val<=rhi) *)
let lemma_holds (e:encl) (y:int) (x:int) (v:int) : bool =
  x < e.xlo || x ) e.xhi || (if y < e.rlo then v >= e.rlo else v <= e.rhi)

(* O1: with a sound enclosure the clause is valid for every model v = f x. *)
let o1 (f:int -> int) (e:encl) (y:int) (x:int)
  : Lemma (requires sound f e) (ensures lemma_holds e y x (f x)) = ()

(* O2: when the enclosure excludes y, the clause is falsified by the current
   assignment (arg in [l,u] inside xlo..xhi, val = y): progress, no spurious accept. *)
let o2 (e:encl) (y:int) (x:int)
  : Lemma (requires not (contains e y) /\ e.xlo <= x /\ x <= e.xhi)
          (ensures not (lemma_holds e y x y)) = ()

(* Loop model: shrink-search returns first candidate not containing y, else the initial one. *)
let rec pick (init:encl) (y:int) (cands: list encl) : Tot encl (decreases cands) =
  match cands with
  | [] -> init
  | c :: tl -> if not (contains c y) then c else pick init y tl

(* O3: the selected enclosure never contains y, and is sound whenever init and all candidates are. *)
let rec o3 (f:int -> int) (init:encl) (y:int) (cands: list encl)
  : Lemma (requires not (contains init y) /\ sound f init /\ (forall c. FStar.List.Tot.memP c cands ==> sound f c))
          (ensures not (contains (pick init y cands) y) /\ sound f (pick init y cands))
          (decreases cands) =
  match cands with
  | [] -> ()
  | c :: tl -> if not (contains c y) then () else o3 f init y tl
