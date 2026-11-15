module Z3GroundScope

open Z3AstTheory
module D = Z3ExprScope
module L = FStar.List.Tot

let rec listed (table:list expr) (e:expr) : Tot bool (decreases e) =
  L.mem e table &&
  (match e with
   | App _ args -> listed_args table args
   | _ -> true)

and listed_args (table:list expr) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | e :: rest -> listed table e && listed_args table rest

let application_table (table:list expr) : prop =
  forall (e:expr). L.mem e table ==>
    (App? e /\ sorts_match (App?.args e) (App?.decl e).domain)

let rec lemma_scoped (table:list expr) (e:expr)
  : Lemma (requires application_table table /\ listed table e)
          (ensures D.scoped [] e)
          (decreases e) =
  match e with
  | App _ args -> lemma_scoped_args table args
  | _ -> ()

and lemma_scoped_args (table:list expr) (args:list expr)
  : Lemma (requires application_table table /\ listed_args table args)
          (ensures D.scoped_args [] args)
          (decreases args) =
  match args with
  | [] -> ()
  | e :: rest ->
    lemma_scoped table e;
    lemma_scoped_args table rest
