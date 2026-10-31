module PulseMip.Solver
#lang-pulse

open Pulse.Lib.Pervasives
open PulseMip.Model
module C = PulseMip.Certificate
module S = PulseMip.Search

fn rec visit (depth row_limit:nat) (p:problem) (rows:list polynomial)
             (remaining:ref nat) (best:ref (option point))
  requires pts_to remaining 'n ** pts_to best 'b
  returns r:S.outcome
  ensures exists* n' b'. pts_to remaining n' ** pts_to best b' ** pure (n' <= 'n)
  decreases depth
{
  let available = !remaining;
  if (depth = 0 || available = 0) {
    S.Open C.NodeLimit
  } else {
    assert (pure (available > 0 && depth > 0));
    remaining := available - 1;
    let incumbent = !best;
    let next = S.plan row_limit p rows incumbent;
    match next {
      S.Close t -> { S.Closed t }
      S.Offer x t -> {
        best := S.improve p x incumbent;
        S.Closed t
      }
      S.Escape x d -> { S.Infinite x d }
      S.Stop reason -> { S.Open reason }
      S.Fail message -> { S.Broken message }
      S.Fork v k -> {
        let left = visit (depth - 1) row_limit p (lower_branch v k :: rows) remaining best;
        match left {
          S.Infinite _ _ -> { left }
          S.Broken _ -> { left }
          _ -> {
            let right = visit (depth - 1) row_limit p (upper_branch v k :: rows) remaining best;
            S.join v k left right
          }
        }
      }
    }
  }
}

fn solve (p:problem) (node_limit row_limit:nat)
  requires emp
  returns r:C.result
  ensures emp ** pure (C.accepts p r \/ C.Error? r)
{
  if (not (valid p)) {
    C.Error "invalid problem: variable indices or polynomial denominators"
  } else {
    let mut remaining = node_limit;
    let mut best = None #point;
    let outcome = visit node_limit row_limit p p.constraints remaining best;
    let incumbent = !best;
    let raw = S.finish outcome incumbent;
    C.certify p raw
  }
}
