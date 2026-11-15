module Z3ModusPonensSyntax

open Z3AstTheory
open Z3UnifiedProofSyntax
module C = Z3CanonicalOps

let step (kind:rule) (concl:judgment) (facts:list judgment) : bool =
  match proposition concl with
  | None -> false
  | Some target ->
    if kind = ObservationalMP then
      (match facts with
       | [j; Observational a b] -> proposition j = Some a && target = b
       | _ -> false)
    else if kind = ModusPonens then
      (match propositions facts with
       | Some [a; App f [s; t]] ->
         (C.canonical_implies f || C.canonical_eq f) && a = s && target = t
       | _ -> false)
    else false
