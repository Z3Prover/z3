module Z3MbqiDivGuard
(* Abstract model of partial_arith_guard_cfg (src/smt/smt_model_checker.cpp, PR 11692
   head 8d187acd).  d0 = model interpretation of div0 at a zero divisor.
   c  = the value the auxiliary context may freely choose for (div a 0) when the
        divisor is symbolic (the evaluator leaves such terms unevaluated). *)

type exp =
  | Num : int -> exp
  | Var : nat -> exp
  | Add : exp -> exp -> exp
  | Div : exp -> exp -> exp          (* div a b *)
  | D0  : exp -> exp -> exp          (* fi->get_interp() instantiated with args *)
  | Ite0 : exp -> exp -> exp -> exp  (* ite (= s 0) z nz *)

let ediv_nz (a b: int{b <> 0}) : int =
  let q = a / b in let r = a - b * q in
  if r >= 0 then q else if b > 0 then q - 1 else q + 1

(* Model semantics (what the model evaluator would compute): zero -> d0 *)
let rec sem_model (d0: int -> int -> int) (env: nat -> int) (e: exp) : Tot int (decreases e) =
  match e with
  | Num n -> n
  | Var i -> env i
  | Add a b -> sem_model d0 env a + sem_model d0 env b
  | Div a b -> let x = sem_model d0 env a in let y = sem_model d0 env b in
               if y = 0 then d0 x y else ediv_nz x y
  | D0 a b -> d0 (sem_model d0 env a) (sem_model d0 env b)
  | Ite0 s z nz -> if sem_model d0 env s = 0 then sem_model d0 env z else sem_model d0 env nz

(* Auxiliary-context semantics after evaluation: symbolic divisor at zero -> arbitrary c;
   numeral divisor is evaluated by the model evaluator (d0). *)
let rec sem_aux (d0 c: int -> int -> int) (env: nat -> int) (e: exp) : Tot int (decreases e) =
  match e with
  | Num n -> n
  | Var i -> env i
  | Add a b -> sem_aux d0 c env a + sem_aux d0 c env b
  | Div a (Num n) -> let x = sem_aux d0 c env a in
               if n = 0 then d0 x 0 else ediv_nz x n
  | Div a b -> let x = sem_aux d0 c env a in let y = sem_aux d0 c env b in
               if y = 0 then c x y else ediv_nz x y
  | D0 a b -> d0 (sem_aux d0 c env a) (sem_aux d0 c env b)
  | Ite0 s z nz -> if sem_aux d0 c env s = 0 then sem_aux d0 c env z else sem_aux d0 c env nz

(* One bottom-up pass; Div result is BR_DONE (not revisited). Numeral divisors skipped. *)
let rec guard (e: exp) : Tot exp (decreases e) =
  match e with
  | Num _ | Var _ -> e
  | Add a b -> Add (guard a) (guard b)
  | D0 a b -> D0 (guard a) (guard b)
  | Ite0 s z nz -> Ite0 (guard s) (guard z) (guard nz)
  | Div a b ->
    let a' = guard a in let b' = guard b in
    (match b' with
     | Num _ -> Div a' b'
     | _ -> Ite0 b' (D0 a' b') (Div a' b'))

(* Obligation 1 (counterexample witness for the unguarded base): c differs from d0 *)
let d0_zero (_ _: int) : int = 0
let c_one (_ _: int) : int = 1
let env0 (_: nat) : int = 0
let witness : exp = Div (Num 0) (Var 0)   (* (div 0 x) at x = 0 *)
let base_diverges () : Lemma (sem_aux d0_zero c_one env0 witness <> sem_model d0_zero env0 witness) = ()

(* Obligation 2: guard makes the auxiliary semantics agree with the model for ALL c *)
let rec guard_sound (d0 c: int -> int -> int) (env: nat -> int) (e: exp)
  : Lemma (ensures sem_aux d0 c env (guard e) == sem_model d0 env e) (decreases e) =
  match e with
  | Num _ | Var _ -> ()
  | Add a b -> guard_sound d0 c env a; guard_sound d0 c env b
  | D0 a b -> guard_sound d0 c env a; guard_sound d0 c env b
  | Ite0 s z nz -> guard_sound d0 c env s; guard_sound d0 c env z; guard_sound d0 c env nz
  | Div a b -> guard_sound d0 c env a; guard_sound d0 c env b

(* Obligation 3: the model's value is unchanged when no choice is needed, i.e. the guard
   is the identity on terms without Div (so pass is a no-op where it should be) *)
let rec no_div (e: exp) : bool = match e with
  | Num _ | Var _ -> true
  | Add a b | D0 a b -> no_div a && no_div b
  | Ite0 s z nz -> no_div s && no_div z && no_div nz
  | Div _ _ -> false
let rec guard_id (e: exp) : Lemma (requires no_div e) (ensures guard e == e) (decreases e) =
  match e with
  | Num _ | Var _ -> ()
  | Add a b | D0 a b -> guard_id a; guard_id b
  | Ite0 s z nz -> guard_id s; guard_id z; guard_id nz
