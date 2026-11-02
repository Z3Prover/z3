module NameUnitsScanAudit
module S = FStar.Seq

(* Lead-byte width, as kernel.c z3_name_width and Z3NameUnits.ml width. *)
let width (b:nat{b < 256}) : pos = if b < 128 then 1 else if b < 224 then 2 else if b < 240 then 3 else 4

let bytes = S.seq (b:nat{b < 256})

let meas (s:bytes) (i:nat) : nat = if i >= S.length s then 0 else S.length s - i

(* Character count from byte offset i; a width past the end ends the string. *)
let rec units (s:bytes) (i:nat) : Tot nat (decreases meas s i) =
  if i >= S.length s then 0 else 1 + units s (i + width (S.index s i))

(* The native loop. The C advance `width < n - i ? i + width : n` is the clamped step. *)
let step (s:bytes) (i:nat{i < S.length s}) : nat =
  let w = width (S.index s i) in
  if w < S.length s - i then i + w else S.length s

let rec scan (s:bytes) (cap:nat) (i:nat) (k:nat) : Tot int (decreases meas s i) =
  if i >= S.length s then k
  else if k = cap then -1
  else scan s cap (step s i) (k + 1)

let lemma_step (s:bytes) (i:nat{i < S.length s})
  : Lemma (units s (step s i) == units s (i + width (S.index s i)) /\ step s i > i) = ()

(* O1: for every cap, scan = (k + units <= cap ? k + units : -1). *)
let rec lemma_scan (s:bytes) (cap:nat) (i:nat) (k:nat)
  : Lemma (requires k <= cap)
          (ensures scan s cap i k == (if k + units s i <= cap then k + units s i else -1))
          (decreases meas s i) =
  if i >= S.length s then ()
  else if k = cap then assert (units s i >= 1)
  else (lemma_step s i; lemma_scan s cap (step s i) (k + 1))

let rec lemma_units_le (s:bytes) (i:nat)
  : Lemma (ensures units s i <= meas s i) (decreases meas s i) =
  if i >= S.length s then () else lemma_units_le s (i + width (S.index s i))

let scan_units (s:bytes) (limit:nat) : int =
  let n = S.length s in
  scan s (if limit < n then limit else n) 0 0

(* O2: the cap clamp to the byte size n is exact for every limit (incl. limit >= n). *)
let lemma_scan_units (s:bytes) (limit:nat)
  : Lemma (scan_units s limit == (if units s 0 <= limit then units s 0 else -1)) =
  lemma_scan s (if limit < S.length s then limit else S.length s) 0 0;
  lemma_units_le s 0

(* O3: lead bytes read are at most min(units, cap), never at or past the end. *)
let rec reads (s:bytes) (cap:nat) (i:nat) (k:nat) : Tot nat (decreases meas s i) =
  if i >= S.length s || k = cap then k else reads s cap (step s i) (k + 1)

let rec lemma_reads (s:bytes) (cap:nat) (i:nat) (k:nat)
  : Lemma (requires k <= cap)
          (ensures reads s cap i k <= cap /\ reads s cap i k <= k + units s i)
          (decreases meas s i) =
  if i >= S.length s || k = cap then ()
  else (lemma_step s i; lemma_reads s cap (step s i) (k + 1))
