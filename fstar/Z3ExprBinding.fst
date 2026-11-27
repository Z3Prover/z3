module Z3ExprBinding

open Z3AstTheory
open FStar.List.Tot
module L = FStar.List.Tot

let rec lift (amount cutoff:nat) (e:expr) : Tot expr (decreases e) =
  match e with
  | Var n s -> Var (if n < cutoff then n else n + amount) s
  | App f args -> App f (lift_args amount cutoff args)
  | Quantifier k bs s body ->
    Quantifier k bs s (lift amount (cutoff + L.length bs) body)

and lift_args (amount cutoff:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> lift amount cutoff a :: lift_args amount cutoff rest

let lift_environments (#value:Type) (amount cutoff:nat) (rho sigma:env value) : prop =
  forall (n:nat). sigma (if n < cutoff then n else n + amount) == rho n

let rec lemma_lift (#value:Type) (i:interpretation value) (e:expr) (amount cutoff:nat)
                   (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ lift_environments amount cutoff rho sigma)
          (ensures eval i (lift amount cutoff e) sigma == eval i e rho)
          (decreases %[e])
  = match e with
    | Var _ _ -> ()
    | App _ args -> lemma_lift_args i args amount cutoff rho sigma
    | Quantifier _ bs _ body ->
      let bodies (vs:list value{L.length vs = L.length bs})
        : Lemma (eval i (lift amount (cutoff + L.length bs) body) (shift vs sigma) ==
                 eval i body (shift vs rho))
        = let indices (n:nat)
            : Lemma (shift vs sigma (if n < cutoff + L.length bs then n else n + amount) ==
                     shift vs rho n)
            = if n < L.length vs then ()
              else assert (sigma (if n - L.length vs < cutoff
                                  then n - L.length vs else n - L.length vs + amount) ==
                           rho (n - L.length vs)) in
          FStar.Classical.forall_intro indices;
          lemma_lift i body amount (cutoff + L.length bs) (shift vs rho) (shift vs sigma) in
      FStar.Classical.forall_intro bodies

and lemma_lift_args (#value:Type) (i:interpretation value) (args:list expr) (amount cutoff:nat)
                    (rho sigma:env value)
  : Lemma (requires quant_extensional i /\ lift_environments amount cutoff rho sigma)
          (ensures eval_args i (lift_args amount cutoff args) sigma == eval_args i args rho)
          (decreases %[args])
  = match args with
    | [] -> ()
    | e :: rest ->
      lemma_lift i e amount cutoff rho sigma;
      lemma_lift_args i rest amount cutoff rho sigma

let lemma_lift_under (#value:Type) (i:interpretation value) (e:expr)
                     (rho:env value) (vs:list value)
  : Lemma (requires quant_extensional i)
          (ensures eval i (lift (L.length vs) 0 e) (shift vs rho) == eval i e rho)
  = let indices (n:nat)
      : Lemma (shift vs rho (n + L.length vs) == rho n) = () in
    FStar.Classical.forall_intro indices;
    lemma_lift i e (L.length vs) 0 rho (shift vs rho)
