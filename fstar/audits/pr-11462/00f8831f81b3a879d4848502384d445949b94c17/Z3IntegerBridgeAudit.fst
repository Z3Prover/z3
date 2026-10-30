module Z3IntegerBridgeAudit
open FStar.List.Tot

let rec sum (xs:list int) : Tot int (decreases xs) =
  match xs with [] -> 0 | x :: rest -> x + sum rest
let rec product (xs:list int) : Tot int (decreases xs) =
  match xs with [] -> 1 | x :: rest -> x * product rest
let subtract (xs:list int) : int =
  match xs with [] -> 0 | [x] -> -x | x :: rest -> x - sum rest

(* left-nested SMT-LIB semantics of (- a b c ...) *)
let rec foldsub (acc:int) (ys:list int) : Tot int (decreases ys) =
  match ys with [] -> acc | y :: r -> foldsub (acc - y) r

let rec lem_foldsub (acc:int) (ys:list int)
  : Lemma (ensures foldsub acc ys == acc - sum ys) (decreases ys) =
  match ys with [] -> () | _ :: r -> lem_foldsub (acc - List.Tot.hd ys) r

(* O1: nonempty subtraction equals left-nested subtraction, incl. unary negation *)
let o1 (x:int) (rest:list int)
  : Lemma (subtract (x :: rest) == (match rest with [] -> 0 - x | _ -> foldsub x rest)) =
  lem_foldsub x rest

(* O2: sum/product agree with append (n-ary flattening is sound) *)
let rec o2s (a b:list int) : Lemma (ensures sum (a @ b) == sum a + sum b) (decreases a) =
  match a with [] -> () | _ :: r -> o2s r b
let rec o2p (a b:list int)
  : Lemma (ensures product (a @ b) == product a * product b) (decreases a) =
  match a with
  | [] -> ()
  | x :: r -> o2p r b; FStar.Math.Lemmas.paren_mul_right x (product r) (product b)

(* O3: unbounded integers: no overflow edge; witness that Sub is not commutative/ not Add-of-negation-free *)
let o3 () : Lemma (subtract [1;2] == -1 /\ subtract [2;1] == 1 /\ subtract [5] == -5) = ()
