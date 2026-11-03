module SkolemComponentAudit
module L = FStar.List.Tot

(* Abstract model of Z3SortedSkolem.component/lemma_component: witnesses are a list
   of function symbols (e:eqtype); component returns the first matching index. *)
let rec component (#e:eqtype) (f:e) (ws:list e) : option nat =
  match ws with
  | [] -> None
  | g :: rest -> if f = g then Some 0
                 else (match component f rest with Some n -> Some (n + 1) | None -> None)

(* O1: a found index is in range and selects f. *)
let rec lemma_component (#e:eqtype) (f:e) (ws:list e)
  : Lemma (ensures (match component f ws with
                    | Some n -> n < L.length ws /\ L.index ws n == f
                    | None -> True))
  = match ws with
    | [] -> ()
    | g :: rest -> if f = g then () else lemma_component f rest

(* O2: with no duplicate witnesses, a symbol absent from ws is untouched (None). *)
let rec lemma_absent (#e:eqtype) (f:e) (ws:list e)
  : Lemma (requires ~(L.mem f ws)) (ensures component f ws == None)
  = match ws with [] -> () | _ :: rest -> lemma_absent f rest
