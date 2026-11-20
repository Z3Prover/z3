module Z3IndependentIntegerLatticeSyntax

open Z3AstTheory
open Z3ProofIndex
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module C = Z3LpCertificate
module G = Z3LpGomorySyntax
module L = FStar.List.Tot

type partial = {
  split: expr;
  offset: G.rational;
  below: list G.rational;
  above: list G.rational;
}

let rec columns (context:C.certificate) (s:C.step) (pivot:nat)
                (seen:list nat) (row:C.polynomial) (p:partial)
  : Tot (option partial) (decreases row) =
  match row with
  | [] -> if L.mem pivot seen then Some p else None
  | (coefficient,j) :: rest ->
    if L.mem j seen then None else
    let seen = j :: seen in
    if j = pivot then
      if G.equal coefficient (G.neg G.one) then columns context s pivot seen rest p
      else None
    else if G.equal coefficient G.zero then columns context s pivot seen rest p
    else
      C.lookup context.variables j >>= (fun variable ->
      G.find_bounds j None s.bounds >>= (fun bounds ->
      let lower, upper = match bounds with
        | Some b -> b.lower, b.upper | None -> None, None in
      match lower, upper with
      | Some lo, Some hi ->
        G.bound_fact context s lo true >>= (fun l ->
        G.bound_fact context s hi false >>= (fun h ->
        if not (G.equal l.rhs h.rhs) || l.relation = C.Gt || h.relation = C.Lt
        then None else
        let positive = fst coefficient >= 0 in
        let magnitude = if positive then coefficient else G.neg coefficient in
        G.add_bound context s (not positive) (if positive then hi else lo) magnitude p.below >>= (fun below ->
        G.add_bound context s positive (if positive then lo else hi) magnitude p.above >>= (fun above ->
        columns context s pivot seen rest
          { p with offset = G.plus p.offset (G.times coefficient l.rhs);
                   below = below; above = above }))))
      | _, _ ->
        G.divide coefficient s.divisor >>= (fun c ->
        let n, d = c in
        if not variable.integer || get_sort variable.term <> A.int_s || n % d <> 0
        then None else
        columns context s pivot seen rest
          { p with split = G.add p.split (G.multiply (G.floor c) variable.term) })))

let candidate (context:C.certificate) (index:nat) : option G.certificate =
  C.lookup context.steps index >>= (fun s ->
  s.pivot >>= (fun pivot ->
  C.lookup context.variables pivot >>= (fun v ->
  if s.rule <> C.IntegerLattice || not v.integer || get_sort v.term <> A.int_s ||
     not (G.positive s.divisor) || s.equation.relation <> C.Eq ||
     s.equation.contradiction || not (G.equal s.equation.rhs G.zero) ||
     not (G.equal s.equation.epsilon G.zero) || s.conclusion.contradiction ||
     (s.conclusion.relation <> C.Le && s.conclusion.relation <> C.Ge)
  then None else
  G.find_bounds pivot None s.bounds >>= (fun bounds ->
  (match bounds with
   | None -> None
   | Some b ->
     let lower = s.conclusion.relation = C.Ge in
     (if lower then b.lower else b.upper) >>= (fun source ->
     G.bound_fact context s source lower >>= (fun bound ->
     let initial = { split = G.integer 0; offset = G.zero;
                     below = L.map (fun _ -> G.zero) s.premises;
                     above = L.map (fun _ -> G.zero) s.premises } in
     columns context s pivot [] s.equation.lhs initial >>= (fun p ->
     G.divide (G.minus bound.rhs p.offset) s.divisor >>= (fun quotient ->
     let ceiling = 0 - G.floor (G.neg quotient) in
     let threshold =
       if lower then
         if bound.relation = C.Gt then G.floor quotient else ceiling - 1
       else if bound.relation = C.Lt then ceiling - 1 else G.floor quotient in
     G.add_bound context s lower source G.one (if lower then p.below else p.above) >>= (fun source_weights ->
     G.fact_scale context.variables s.conclusion >>= (fun scale ->
     let target = G.times G.one (1, scale) in
     let below = if lower then source_weights else p.below in
     let above = if lower then p.above else source_weights in
     Some { G.split = p.split; threshold = threshold;
            below = G.zero :: (below @ [s.divisor; if lower then G.zero else target]);
            above = G.zero :: (above @ [s.divisor; if lower then target else G.zero]) })))))))))))
