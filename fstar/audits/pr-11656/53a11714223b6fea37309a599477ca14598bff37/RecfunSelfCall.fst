module RecfunSelfCall
(* Model of the PR #11656 guard in recfun_rewriter::mk_app_core (unary function, single bound var).
   Rewrite result: Some r = BR_REWRITE_FULL r ; None = BR_FAILED. *)

type term =
  | Var : term
  | Num : int -> term
  | Gt  : term -> term -> term
  | Ite : term -> term -> term -> term
  | App : nat -> term -> term

let rec subst (t:term) (a:term) : term =
  match t with
  | Var -> a
  | Num _ -> t
  | Gt x y -> Gt (subst x a) (subst y a)
  | Ite c x y -> Ite (subst c a) (subst x a) (subst y a)
  | App f x -> App f (subst x a)

let rec occurs (s:term) (t:term) : bool =
  t = s ||
  (match t with
   | Var | Num _ -> false
   | Gt x y -> occurs s x || occurs s y
   | Ite c x y -> occurs s c || occurs s x || occurs s y
   | App _ x -> occurs s x)

(* interp maps function symbols and an argument value to an integer; booleans encoded as 0/1 *)
type interp = nat -> int -> int

let rec eval (i:interp) (v:int) (t:term) : int =
  match t with
  | Var -> v
  | Num n -> n
  | Gt x y -> if eval i v x > eval i v y then 1 else 0
  | Ite c x y -> if eval i v c <> 0 then eval i v x else eval i v y
  | App f x -> i f (eval i v x)

(* PR head behaviour of the substitution branch *)
let step (f:nat) (body:term) (arg:term) : option term =
  let r = subst body arg in
  if occurs (App f arg) r then None else Some r

(* O1: the new guard — a returned rewrite never contains the original call *)
let o1 (f:nat) (body arg:term)
  : Lemma (match step f body arg with
           | Some r -> not (occurs (App f arg) r) /\ r == subst body arg
           | None -> occurs (App f arg) (subst body arg))
  = ()

(* O2: soundness: Some r preserves meaning under the defining equation of f;
   None leaves the term unchanged (trivially sound). *)
let rec subst_correct (i:interp) (v:int) (t:term) (a:term)
  : Lemma (ensures eval i v (subst t a) == eval i (eval i v a) t) (decreases t)
  = match t with
    | Var | Num _ -> ()
    | Gt x y -> subst_correct i v x a; subst_correct i v y a
    | Ite c x y -> subst_correct i v c a; subst_correct i v x a; subst_correct i v y a
    | App _ x -> subst_correct i v x a

let o2 (i:interp) (f:nat) (body arg:term) (v:int)
  : Lemma (requires forall (n:int). i f n == eval i n body)
          (ensures (match step f body arg with
                    | Some r -> eval i v r == eval i v (App f arg)
                    | None -> True))
  = subst_correct i v body arg

(* O3: reachable witness for the disclosed incompleteness trade-off (not a soundness bug):
   g(x) = ite (x>0) (g x) 7 on 0 — guard fires although the self-call branch is dead. *)
let g_body : term = Ite (Gt Var (Num 0)) (App 0 Var) (Num 7)

let o3 () : Lemma (step 0 g_body (Num 0) == None /\
                (forall (i:interp). eval i 0 g_body == 7))
  = assert_norm (step 0 g_body (Num 0) == None)

(* Guard does not fire for decreasing recursion such as fact-like g(x)=ite(x>0, g(x-1)..): here modelled
   with a distinct-argument call App 0 (Num 1) in body on arg Num 0 *)
let o3b () : Lemma (Some? (step 0 (Ite (Gt Var (Num 0)) (App 0 (Num 1)) (Num 1)) (Num 0)) == true)
  = assert_norm (Some? (step 0 (Ite (Gt Var (Num 0)) (App 0 (Num 1)) (Num 1)) (Num 0)) == true)
