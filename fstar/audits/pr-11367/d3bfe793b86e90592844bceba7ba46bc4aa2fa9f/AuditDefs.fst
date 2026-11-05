module AuditDefs
(* O3: bit_definitions assigns symbol k (0-based) bit start+k, one definition per symbol. *)
module L = FStar.List.Tot
type def = { sym:string; bit:nat }
let rec bit_definitions (start:nat) (symbols:list string) : Tot (list def) (decreases symbols) =
  match symbols with [] -> [] | f :: r -> {sym=f; bit=start} :: bit_definitions (start+1) r

let rec o3 (start:nat) (symbols:list string)
  : Lemma (ensures L.length (bit_definitions start symbols) == L.length symbols /\
                   (forall (k:nat). k < L.length symbols ==>
                      (L.index (bit_definitions start symbols) k).sym == L.index symbols k /\
                      (L.index (bit_definitions start symbols) k).bit == start + k))
          (decreases symbols)
  = match symbols with [] -> () | _ :: r -> o3 (start+1) r
