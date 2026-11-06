module Sql.Cherry

open Sql.Optimize
module N = Sql.Native

let rec decode_mapping (fuel:nat) (t:N.term) : Tot mapping (decreases fuel) =
  if fuel = 0 then Mapping (N.identifier t) else
  match N.opcode t with
  | 20ul -> Identity
  | 22ul -> Compose (decode_mapping (fuel - 1) (N.child t 0ul))
                   (decode_mapping (fuel - 1) (N.child t 1ul))
  | _ -> Mapping (N.identifier t)
let rec decode_condition (fuel:nat) (t:N.term) : Tot condition (decreases fuel) =
  if fuel = 0 then Predicate (N.identifier t) else
  match N.opcode t with
  | 30ul -> Always
  | 31ul -> Never
  | 33ul -> Both (decode_condition (fuel - 1) (N.child t 0ul))
                (decode_condition (fuel - 1) (N.child t 1ul))
  | 34ul -> Preimage (decode_condition (fuel - 1) (N.child t 0ul))
                    (decode_mapping (fuel - 1) (N.child t 1ul))
  | 35ul -> NotNull (N.identifier (N.child t 0ul))
  | _ -> Predicate (N.identifier t)
let rec decode (fuel:nat) (t:N.term) : Tot plan (decreases fuel) =
  if fuel = 0 then Base (N.identifier t) else
  let sub = fuel - 1 in
  match N.opcode t with
  | 1ul -> Empty
  | 2ul -> Filter (decode_condition sub (N.child t 0ul)) (decode sub (N.child t 1ul))
  | 3ul -> Project (decode_mapping sub (N.child t 0ul)) (decode sub (N.child t 1ul))
  | 4ul -> UnionAll (decode sub (N.child t 0ul)) (decode sub (N.child t 1ul))
  | 5ul -> Cross (decode sub (N.child t 0ul)) (decode sub (N.child t 1ul))
  | 6ul -> Join (decode_condition sub (N.child t 0ul))
                (decode sub (N.child t 1ul)) (decode sub (N.child t 2ul))
  | 7ul -> CountRows (decode sub (N.child t 0ul))
  | 8ul -> CountOne (decode sub (N.child t 0ul))
  | 9ul -> CountValue (N.identifier (N.child t 0ul)) (decode sub (N.child t 1ul))
  | 10ul -> CountWhen (decode_condition sub (N.child t 0ul)) (decode sub (N.child t 1ul))
  | 11ul -> AddCounts (decode sub (N.child t 0ul)) (decode sub (N.child t 1ul))
  | _ -> Base (N.identifier t)

let rec encode_mapping (f:mapping) : Tot N.term =
  match f with
  | Identity -> N.make0 20ul
  | Mapping a -> N.lookup a
  | Compose f g -> N.make2 22ul (encode_mapping f) (encode_mapping g)
let rec encode_condition (p:condition) : Tot N.term =
  match p with
  | Always -> N.make0 30ul
  | Never -> N.make0 31ul
  | Predicate a -> N.lookup a
  | Both p q -> N.make2 33ul (encode_condition p) (encode_condition q)
  | Preimage p f -> N.make2 34ul (encode_condition p) (encode_mapping f)
  | NotNull a -> N.make1 35ul (N.lookup a)
let rec encode (q:plan) : Tot N.term =
  match q with
  | Base a -> N.lookup a
  | Empty -> N.make0 1ul
  | Filter p a -> N.make2 2ul (encode_condition p) (encode a)
  | Project f a -> N.make2 3ul (encode_mapping f) (encode a)
  | UnionAll a b -> N.make2 4ul (encode a) (encode b)
  | Cross a b -> N.make2 5ul (encode a) (encode b)
  | Join p a b -> N.make3 6ul (encode_condition p) (encode a) (encode b)
  | CountRows a -> N.make1 7ul (encode a)
  | CountOne a -> N.make1 8ul (encode a)
  | CountValue e a -> N.make2 9ul (N.lookup e) (encode a)
  | CountWhen p a -> N.make2 10ul (encode_condition p) (encode a)
  | AddCounts a b -> N.make2 11ul (encode a) (encode b)

let rewrite_native (t:N.term) : N.term =
  match rewrite (decode 32 t) with
  | None -> t
  | Some q -> encode q
