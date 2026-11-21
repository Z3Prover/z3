module Z3IndependentFiniteFieldMonomial

module FF = Z3SortedFiniteField
module F = FStar.Math.Fermat
module L = FStar.List.Tot
module M = FStar.Math.Lemmas
module P = Z3IndependentModPow

let rec compress (m:FF.mono) : Tot compact (decreases m) =
  match m with
  | [] -> []
  | x :: rest ->
    (match compress rest with
     | (y, n) :: tail -> if x = y then (y, n + 1) :: tail else (x, 1) :: (y, n) :: tail
     | [] -> [(x, 1)])

let rec prepend (x:nat) (n:nat) (rest:FF.mono) : Tot FF.mono (decreases n) =
  if n = 0 then rest else x :: prepend x (n - 1) rest

let rec expand (m:compact) : Tot FF.mono (decreases m) =
  match m with
  | [] -> []
  | (x, n) :: rest -> prepend x n (expand rest)

let rec evaluate (v:nat -> int) (m:compact) : Tot int (decreases m) =
  match m with
  | [] -> 1
  | (x, n) :: rest -> F.pow (v x) n * evaluate v rest

let rec multiply (a b:compact) : Tot compact (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | (x, n) :: ar, (y, m) :: br ->
    if x = y then (x, n + m) :: multiply ar br
    else if x < y then (x, n) :: multiply ar b
    else (y, m) :: multiply a br

let rec less (a b:compact) : Tot bool (decreases (L.length a + L.length b)) =
  match a, b with
  | [], [] -> false
  | [], _ -> true
  | _, [] -> false
  | (x, n) :: ar, (y, m) :: br ->
    if x < y then true
    else if x > y then false
    else if n = m then less ar br
    else if n < m then less ar ((y, m - n) :: br)
    else less ((x, n - m) :: ar) br

let rec equal_metered (fuel:nat) (a b:compact)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match a, b with
    | [], [] -> Some (true, 1)
    | [], _ | _, [] -> Some (false, 1)
    | (x, n) :: ar, (y, m) :: br ->
      if x <> y || n <> m then Some (false, 1)
      else
        match equal_metered (fuel - 1) ar br with
        | None -> None
        | Some (result, work) -> Some (result, work + 1)

let rec lemma_equal_metered (fuel:nat) (a b:compact)
  : Lemma (match equal_metered fuel a b with
           | None -> fuel < L.length a + L.length b + 1
           | Some (result, work) ->
             result == (a = b) /\ work <= fuel /\
             work <= L.length a + L.length b + 1)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match a, b with
    | [], _ | _, [] -> ()
    | (x, n) :: ar, (y, m) :: br ->
      if x <> y || n <> m then ()
      else lemma_equal_metered (fuel - 1) ar br

let rec less_metered (fuel:nat) (a b:compact)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match a, b with
    | [], [] -> Some (false, 1)
    | [], _ -> Some (true, 1)
    | _, [] -> Some (false, 1)
    | (x, n) :: ar, (y, m) :: br ->
      if x < y then Some (true, 1)
      else if x > y then Some (false, 1)
      else
        let next =
          if n = m then less_metered (fuel - 1) ar br
          else if n < m then less_metered (fuel - 1) ar ((y, m - n) :: br)
          else less_metered (fuel - 1) ((x, n - m) :: ar) br in
        match next with
        | None -> None
        | Some (result, work) -> Some (result, work + 1)

let rec lemma_less_metered (fuel:nat) (a b:compact)
  : Lemma (match less_metered fuel a b with
           | None -> fuel < L.length a + L.length b + 1
           | Some (result, work) ->
             result == less a b /\ work <= fuel /\
             work <= L.length a + L.length b + 1)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match a, b with
    | [], _ -> ()
    | _, [] -> ()
    | (x, n) :: ar, (y, m) :: br ->
      if x < y || x > y then ()
      else if n = m then lemma_less_metered (fuel - 1) ar br
      else if n < m then lemma_less_metered (fuel - 1) ar ((y, m - n) :: br)
      else lemma_less_metered (fuel - 1) ((x, n - m) :: ar) br

let after (x:nat) (m:compact) : bool =
  match m with [] -> true | (y, _) :: _ -> x < y

let rec ordered (m:compact) : Tot bool (decreases m) =
  match m with
  | [] -> true
  | (x, _) :: rest -> after x rest && ordered rest

let rec sorted (m:FF.mono) : Tot bool (decreases m) =
  match m with
  | [] -> true
  | x :: rest ->
    (match rest with [] -> true | y :: _ -> x <= y && sorted rest)

let rec degree (m:compact) : Tot nat (decreases m) =
  match m with [] -> 0 | (_, n) :: rest -> n + degree rest

let lemma_degree_empty () : Lemma (degree [] == 0) = ()

let lemma_degree_cons (x:nat) (n:pos) (rest:compact)
  : Lemma (degree ((x, n) :: rest) == n + degree rest) = ()

let rec lemma_prepend_length (x n:nat) (rest:FF.mono)
  : Lemma (L.length (prepend x n rest) == n + L.length rest) (decreases n) =
  if n > 0 then lemma_prepend_length x (n - 1) rest

let rec lemma_degree (m:compact)
  : Lemma (L.length (expand m) == degree m /\ L.length m <= degree m)
          (decreases m) =
  match m with
  | [] -> ()
  | (x, n) :: rest ->
    lemma_degree rest;
    lemma_prepend_length x n (expand rest)

let rec lemma_expand_compress (m:FF.mono)
  : Lemma (expand (compress m) == m) (decreases m) =
  match m with
  | [] -> ()
  | _ :: rest -> lemma_expand_compress rest

let lemma_compress_head (m:FF.mono)
  : Lemma (match m, compress m with
           | [], [] -> True
           | x :: _, (y, _) :: _ -> x == y
           | _, _ -> False) =
  match m with
  | [] -> ()
  | _ :: rest -> (match compress rest with [] -> () | _ :: _ -> ())

let rec lemma_compress_ordered (m:FF.mono)
  : Lemma (requires sorted m) (ensures ordered (compress m))
          (decreases m) =
  match m with
  | [] -> ()
  | _ :: rest ->
    lemma_compress_ordered rest;
    lemma_compress_head rest

let rec lemma_compress_prepend (x:nat) (n:pos) (rest:FF.mono)
  : Lemma (requires (match rest with [] -> True | y :: _ -> x < y))
          (ensures compress (prepend x n rest) == (x, n) :: compress rest)
          (decreases n) =
  if n = 1 then lemma_compress_head rest
  else lemma_compress_prepend x (n - 1) rest

let lemma_expand_head (m:compact)
  : Lemma (match m, expand m with
           | [], [] -> True
           | (x, _) :: _, y :: _ -> x == y
           | _, _ -> False) =
  match m with [] -> () | _ :: _ -> ()

let rec lemma_compress_expand (m:compact)
  : Lemma (requires ordered m) (ensures compress (expand m) == m)
          (decreases m) =
  match m with
  | [] -> ()
  | (x, n) :: rest ->
    lemma_compress_expand rest;
    lemma_expand_head rest;
    lemma_compress_prepend x n (expand rest)

let lemma_ordered_injective (a b:compact)
  : Lemma (requires ordered a /\ ordered b /\ expand a == expand b) (ensures a == b) =
  lemma_compress_expand a;
  lemma_compress_expand b

let rec lemma_prepend (v:nat -> int) (x n:nat) (rest:FF.mono)
  : Lemma (FF.mval v (prepend x n rest) == F.pow (v x) n * FF.mval v rest)
          (decreases n) =
  if n = 0 then () else lemma_prepend v x (n - 1) rest

let rec lemma_evaluate (v:nat -> int) (m:compact)
  : Lemma (evaluate v m == FF.mval v (expand m)) (decreases m) =
  match m with
  | [] -> ()
  | (x, n) :: rest ->
    lemma_prepend v x n (expand rest);
    lemma_evaluate v rest

let rec lemma_multiply (v:nat -> int) (a b:compact)
  : Lemma (evaluate v (multiply a b) == evaluate v a * evaluate v b)
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (x, n) :: ar, (y, m) :: br ->
    if x = y then (
      lemma_multiply v ar br;
      P.lemma_pow_plus (v x) n m;
      FF.lemma_mul4 (F.pow (v x) n) (F.pow (v x) m) (evaluate v ar) (evaluate v br))
    else if x < y then (
      lemma_multiply v ar b;
      M.paren_mul_right (F.pow (v x) n) (evaluate v ar) (evaluate v b))
    else (
      lemma_multiply v a br;
      FF.lemma_mul_swap3 (evaluate v a) (F.pow (v y) m) (evaluate v br))

let lemma_multiply_expanded (v:nat -> int) (a b:compact)
  : Lemma (evaluate v (multiply a b) == FF.mval v (FF.mono_mul (expand a) (expand b))) =
  lemma_multiply v a b;
  lemma_evaluate v a;
  lemma_evaluate v b;
  FF.lemma_mval_mul v (expand a) (expand b)

let rec lemma_prepend_sum (x n m:nat) (rest:FF.mono)
  : Lemma (prepend x n (prepend x m rest) == prepend x (n + m) rest)
          (decreases n) =
  if n > 0 then lemma_prepend_sum x (n - 1) m rest

let rec lemma_lt_prepend (x n:nat) (a b:FF.mono)
  : Lemma (FF.mono_lt (prepend x n a) (prepend x n b) == FF.mono_lt a b)
          (decreases n) =
  if n > 0 then lemma_lt_prepend x (n - 1) a b

let rec lemma_less (a b:compact)
  : Lemma (less a b == FF.mono_lt (expand a) (expand b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], [] -> ()
  | [], _ -> ()
  | _, [] -> ()
  | (x, n) :: ar, (y, m) :: br ->
    if x < y || x > y then ()
    else if n = m then (
      lemma_less ar br;
      lemma_lt_prepend x n (expand ar) (expand br))
    else if n < m then (
      lemma_less ar ((y, m - n) :: br);
      lemma_prepend_sum x n (m - n) (expand br);
      lemma_lt_prepend x n (expand ar) (prepend x (m - n) (expand br)))
    else (
      lemma_less ((x, n - m) :: ar) br;
      lemma_prepend_sum x m (n - m) (expand ar);
      lemma_lt_prepend x m (prepend x (n - m) (expand ar)) (expand br))

let rec lemma_merge_left (x n:nat) (a b:FF.mono)
  : Lemma (requires (match b with [] -> True | y :: _ -> x <= y))
          (ensures FF.mono_mul (prepend x n a) b == prepend x n (FF.mono_mul a b))
          (decreases n) =
  if n > 0 then
    match b with
    | [] -> ()
    | _ :: _ -> lemma_merge_left x (n - 1) a b

let rec lemma_merge_right (x n:nat) (a b:FF.mono)
  : Lemma (requires (match a with [] -> True | y :: _ -> x < y))
          (ensures FF.mono_mul a (prepend x n b) == prepend x n (FF.mono_mul a b))
          (decreases n) =
  if n > 0 then
    match a with
    | [] -> ()
    | _ :: _ -> lemma_merge_right x (n - 1) a b

let rec lemma_multiply_structure (a b:compact)
  : Lemma (requires ordered a /\ ordered b)
          (ensures expand (multiply a b) == FF.mono_mul (expand a) (expand b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (x, n) :: ar, (y, m) :: br ->
    if x = y then (
      lemma_multiply_structure ar br;
      lemma_merge_left x n (expand ar) (expand b);
      lemma_merge_right y m (expand ar) (expand br);
      lemma_prepend_sum x n m (FF.mono_mul (expand ar) (expand br)))
    else if x < y then (
      lemma_multiply_structure ar b;
      lemma_merge_left x n (expand ar) (expand b))
    else (
      lemma_multiply_structure a br;
      lemma_merge_right y m (expand a) (expand br))

let lemma_multiply_after (x:nat) (a b:compact)
  : Lemma (requires after x a /\ after x b)
          (ensures after x (multiply a b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | _ :: _, _ :: _ -> ()

let rec lemma_multiply_ordered (a b:compact)
  : Lemma (requires ordered a /\ ordered b)
          (ensures ordered (multiply a b))
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (x, _) :: ar, (y, _) :: br ->
    if x = y then (
      lemma_multiply_ordered ar br;
      lemma_multiply_after x ar br)
    else if x < y then (
      lemma_multiply_ordered ar b;
      lemma_multiply_after x ar b)
    else (
      lemma_multiply_ordered a br;
      lemma_multiply_after y a br)

let rec lemma_multiply_size (a b:compact)
  : Lemma (degree (multiply a b) == degree a + degree b /\
           L.length (multiply a b) <= L.length a + L.length b)
          (decreases (L.length a + L.length b)) =
  match a, b with
  | [], _ -> ()
  | _, [] -> ()
  | (x, _) :: ar, (y, _) :: br ->
    if x = y then lemma_multiply_size ar br
    else if x < y then lemma_multiply_size ar b
    else lemma_multiply_size a br

let rec multiply_metered (fuel:nat) (a b:compact)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match a, b with
    | [], _ -> Some (b, 1)
    | _, [] -> Some (a, 1)
    | (x, n) :: ar, (y, m) :: br ->
      let (head, next) =
        if x = y then ((x, n + m), multiply_metered (fuel - 1) ar br)
        else if x < y then ((x, n), multiply_metered (fuel - 1) ar b)
        else ((y, m), multiply_metered (fuel - 1) a br) in
      match next with
      | None -> None
      | Some (tail, work) -> Some (head :: tail, work + 1)

let rec lemma_multiply_metered (fuel:nat) (a b:compact)
  : Lemma (match multiply_metered fuel a b with
           | None -> fuel < L.length a + L.length b + 1
           | Some (result, work) ->
             result == multiply a b /\ 0 < work /\ work <= fuel /\
             work <= L.length a + L.length b + 1)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match a, b with
    | [], _ | _, [] -> ()
    | (x, _) :: ar, (y, _) :: br ->
      if x = y then lemma_multiply_metered (fuel - 1) ar br
      else if x < y then lemma_multiply_metered (fuel - 1) ar b
      else lemma_multiply_metered (fuel - 1) a br

let rec compress_metered (fuel:nat) (m:FF.mono)
  : Tot (option (compact & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match m with
    | [] -> Some ([], 1)
    | x :: rest ->
      match compress_metered (fuel - 1) rest with
      | None -> None
      | Some (tail, work) ->
        let result =
          match tail with
          | (y, n) :: more -> if x = y then (y, n + 1) :: more else (x, 1) :: tail
          | [] -> [(x, 1)] in
        Some (result, work + 1)

let rec lemma_compress_metered (fuel:nat) (m:FF.mono)
  : Lemma (match compress_metered fuel m with
           | None -> fuel < L.length m + 1
           | Some (result, work) ->
             result == compress m /\ work == L.length m + 1 /\ work <= fuel)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match m with
    | [] -> ()
    | _ :: rest -> lemma_compress_metered (fuel - 1) rest

let rec sorted_metered (fuel:nat) (m:FF.mono)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match m with
    | [] | [_] -> Some (true, 1)
    | x :: y :: rest ->
      if x > y then Some (false, 1)
      else
        match sorted_metered (fuel - 1) (y :: rest) with
        | None -> None
        | Some (result, work) -> Some (result, work + 1)

let rec lemma_sorted_metered (fuel:nat) (m:FF.mono)
  : Lemma (match sorted_metered fuel m with
           | None -> fuel < L.length m + 1
           | Some (result, work) ->
             result == sorted m /\ 0 < work /\ work <= fuel /\ work <= L.length m + 1)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match m with
    | [] | [_] -> ()
    | x :: y :: rest ->
      if x <= y then lemma_sorted_metered (fuel - 1) (y :: rest)

let rec ordered_metered (fuel:nat) (m:compact)
  : Tot (option (bool & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match m with
    | [] -> Some (true, 1)
    | (x, _) :: rest ->
     if not (after x rest) then Some (false, 1)
     else
       match ordered_metered (fuel - 1) rest with
       | None -> None
       | Some (result, work) -> Some (result, work + 1)

let rec lemma_ordered_metered (fuel:nat) (m:compact)
  : Lemma (match ordered_metered fuel m with
          | None -> fuel < L.length m + 1
          | Some (result, work) ->
            result == ordered m /\ 0 < work /\ work <= fuel /\
            work <= L.length m + 1)
         (decreases fuel) =
  if fuel = 0 then ()
  else
    match m with
    | [] -> ()
    | (x, _) :: rest ->
     if after x rest then lemma_ordered_metered (fuel - 1) rest

let rec lemma_expanded_irreflexive (a:FF.mono)
  : Lemma (not (FF.mono_lt a a)) (decreases a) =
  match a with [] -> () | _ :: rest -> lemma_expanded_irreflexive rest

let rec lemma_expanded_transitive (a b c:FF.mono)
  : Lemma (requires FF.mono_lt a b /\ FF.mono_lt b c)
          (ensures FF.mono_lt a c) (decreases a) =
  match a, b, c with
  | x :: ar, y :: br, z :: cr ->
    if x = y && y = z then lemma_expanded_transitive ar br cr
  | _ -> ()

let rec lemma_expanded_total (a b:FF.mono)
  : Lemma (FF.mono_lt a b \/ FF.mono_lt b a \/ a == b) (decreases a) =
  match a, b with
  | x :: ar, y :: br -> if x = y then lemma_expanded_total ar br
  | _ -> ()

let lemma_less_irreflexive (a:compact) : Lemma (not (less a a)) =
  lemma_less a a;
  lemma_expanded_irreflexive (expand a)

let lemma_less_transitive (a b c:compact)
  : Lemma (requires less a b /\ less b c) (ensures less a c) =
  lemma_less a b;
  lemma_less b c;
  lemma_less a c;
  lemma_expanded_transitive (expand a) (expand b) (expand c)

let lemma_less_total (a b:compact)
  : Lemma (requires ordered a /\ ordered b /\ a <> b)
          (ensures less a b \/ less b a) =
  lemma_less a b;
  lemma_less b a;
  lemma_expanded_total (expand a) (expand b);
  if expand a = expand b then lemma_ordered_injective a b
