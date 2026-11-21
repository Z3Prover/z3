module Z3DocumentScope

open Z3AstTheory
module D = Z3ExprScope
module G = Z3GroundScope
module S = Z3DocumentSyntax
module L = FStar.List.Tot

let rec lemma_ground_member (table:list expr) (e:expr)
  : Lemma (requires S.ground_exprs table /\ L.mem e table)
          (ensures App? e /\ sorts_match (App?.args e) (App?.decl e).domain)
          (decreases table) =
  match table with
  | [] -> ()
  | x :: rest -> if x <> e then lemma_ground_member rest e

let lemma_ground_application_table (table:list expr)
  : Lemma (requires S.ground_exprs table)
          (ensures G.application_table table) =
  let member (e:expr)
    : Lemma (L.mem e table ==>
             App? e /\ sorts_match (App?.args e) (App?.decl e).domain) =
    if L.mem e table then lemma_ground_member table e in
  FStar.Classical.forall_intro member

let lemma_ground_term (table:list expr) (e:expr)
  : Lemma (requires S.ground_exprs table /\ G.listed table e)
          (ensures D.scoped [] e) =
  lemma_ground_application_table table;
  G.lemma_scoped table e
