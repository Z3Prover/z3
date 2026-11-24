module PulseClaimInspection

open FStar.Tactics.V2
module R = FStar.Reflection.V2

let rec is_lemma (t:term) : Tot bool (decreases t) =
  match R.inspect_ln t with
  | R.Tv_Arrow _ c ->
    let cv = R.inspect_comp c in
    (match R.inspect_ln cv.R.result_typ with
     | R.Tv_Arrow _ _ -> R.is_tot_or_gtot_comp cv && is_lemma cv.R.result_typ
     | _ -> cv.R.source_effect_name = ["FStar"; "Pervasives"; "Lemma"])
  | _ -> false

let report (e:env) (modname:string) (tag:string) : Tac unit =
  iter (fun fv ->
    let name = R.inspect_fv fv in
    match R.lookup_typ e name with
    | Some se -> if FStar.List.Tot.existsb (fun q -> R.Assumption? q || R.InternalAssumption? q) (R.sigelt_quals se) then () else
      (match R.inspect_sigelt se with
       | R.Sg_Let _ lbs -> iter (fun lb ->
         let v = R.inspect_lb lb in
         if R.inspect_fv v.R.lb_fv = name && is_lemma v.R.lb_typ then (
           let (file, l, c, l', c') = FStar.Range.explode (R.range_of_sigelt se) in
           let (tf, tl, tc, _, _) = FStar.Range.explode (R.range_of_term v.R.lb_typ) in
           let (df, dl, dc, dl', dc') = FStar.Range.explode (R.range_of_term v.R.lb_def) in
           let (l,c,l',c') = match lbs with
             | [_] -> (l,c,l',c')
             | _ -> if tf = file && df = file && tl >= l && tl <= dl
                    then (tl,tc,dl',dc') else (dl,dc,dl',dc') in
           let typ = term_to_string v.R.lb_typ in
           print (tag ^ "\n" ^ FStar.String.concat "." name ^ "\n" ^ file ^ "\n" ^
             FStar.String.concat ":" (FStar.List.Tot.map string_of_int [l;c;l';c']) ^ "\n" ^ typ ^ "\n" ^ tag ^ " END")
         ) else ()) lbs
       | _ -> ())
    | _ -> ()) (R.defs_in_module e [modname]);
  print (tag ^ " DONE")
