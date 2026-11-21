module Z3SortedBinding

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module D = Z3ExprScope
module B = Z3ExprBinding
module Sub = Z3Substitution
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let lift_index (amount cutoff n:nat) : nat =
  if n < cutoff then n else n + amount

let lift_scopes (amount cutoff:nat) (left right:list sort) : prop =
  forall (n:nat{n < L.length left}).
    D.scoped right (Var (lift_index amount cutoff n) (L.index left n))

let rec lemma_lift_scope_extend (amount cutoff:nat) (left right bound:list sort)
                               (n:nat{n < L.length (bound @ left)})
  : Lemma (requires lift_scopes amount cutoff left right)
          (ensures D.scoped (bound @ right)
                     (Var (lift_index amount (cutoff + L.length bound) n)
                          (L.index (bound @ left) n)))
          (decreases bound) =
  LP.append_length bound left;
  LP.append_length bound right;
  match bound with
  | [] -> ()
  | _ :: rest ->
    if n > 0 then lemma_lift_scope_extend amount cutoff left right rest (n - 1)

let rec lemma_lift_scope (amount cutoff:nat) (left right:list sort) (e:expr)
  : Lemma (requires D.scoped left e /\ lift_scopes amount cutoff left right)
          (ensures D.scoped right (B.lift amount cutoff e) /\
                   get_sort (B.lift amount cutoff e) == get_sort e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args -> lemma_lift_args_scope amount cutoff left right args f.domain
  | Quantifier _ bound _ body ->
    LP.rev_length bound;
    let indices (n:nat{n < L.length (L.rev bound @ left)})
      : Lemma (D.scoped (L.rev bound @ right)
                 (Var (lift_index amount (cutoff + L.length bound) n)
                      (L.index (L.rev bound @ left) n))) =
      lemma_lift_scope_extend amount cutoff left right (L.rev bound) n in
    FStar.Classical.forall_intro indices;
    lemma_lift_scope amount (cutoff + L.length bound) (L.rev bound @ left)
      (L.rev bound @ right) body

and lemma_lift_args_scope (amount cutoff:nat) (left right:list sort) (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args left args /\ sorts_match args ss /\
                    lift_scopes amount cutoff left right)
          (ensures D.scoped_args right (B.lift_args amount cutoff args) /\
                   sorts_match (B.lift_args amount cutoff args) ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_lift_scope amount cutoff left right e;
    lemma_lift_args_scope amount cutoff left right rest tail
  | _, _ -> ()

let rec lemma_extend_scope (bound scope:list sort) (n:nat{n < L.length scope})
  : Lemma (ensures D.scoped (bound @ scope)
                     (Var (n + L.length bound) (L.index scope n)))
          (decreases bound) =
  LP.append_length bound scope;
  match bound with [] -> () | _ :: rest -> lemma_extend_scope rest scope n

let lemma_lift_under_scope (bound scope:list sort) (e:expr)
  : Lemma (requires D.scoped scope e)
          (ensures D.scoped (bound @ scope) (B.lift (L.length bound) 0 e) /\
                   get_sort (B.lift (L.length bound) 0 e) == get_sort e) =
  let indices (n:nat{n < L.length scope})
    : Lemma (D.scoped (bound @ scope) (Var (n + L.length bound) (L.index scope n))) =
    lemma_extend_scope bound scope n in
  FStar.Classical.forall_intro indices;
  lemma_lift_scope (L.length bound) 0 scope (bound @ scope) e

let substitution_scopes (theta:Sub.substitution) (left right:list sort) : prop =
  forall (n:nat{n < L.length left}).
    match theta n (L.index left n) with
    | Some e -> D.scoped right e /\ get_sort e == L.index left n
    | None -> True

let rec lemma_scope_index (prefix suffix:list sort) (n:nat{n < L.length (prefix @ suffix)})
  : Lemma (ensures
      (if n < L.length prefix
       then L.index (prefix @ suffix) n == L.index prefix n
       else L.index (prefix @ suffix) n == L.index suffix (n - L.length prefix)))
    (decreases prefix) =
  LP.append_length prefix suffix;
  match prefix with
  | [] -> ()
  | _ :: rest -> if n > 0 then lemma_scope_index rest suffix (n - 1)

let lemma_under_substitution_scopes (theta:Sub.substitution) (bound left right:list sort)
  : Lemma (requires substitution_scopes theta left right)
          (ensures substitution_scopes (Sub.under (L.length bound) theta)
                     (bound @ left) (bound @ right)) =
  LP.append_length bound left;
  LP.append_length bound right;
  let indices (n:nat{n < L.length (bound @ left)})
    : Lemma (
        match Sub.under (L.length bound) theta n (L.index (bound @ left) n) with
        | Some e -> D.scoped (bound @ right) e /\ get_sort e == L.index (bound @ left) n
        | None -> True) =
    lemma_scope_index bound left n;
    if n < L.length bound then
      lemma_scope_index bound right n
    else (
      let j = n - L.length bound in
      match theta j (L.index left j) with
      | Some e ->
        assert (D.scoped right e /\ get_sort e == L.index left j);
        lemma_lift_under_scope bound right e
      | None -> ())
  in
  FStar.Classical.forall_intro indices

let rec lemma_apply_scope (theta:Sub.substitution) (left right:list sort) (e result:expr)
  : Lemma (requires D.scoped left e /\ substitution_scopes theta left right /\
                    Sub.apply theta e == Some result)
          (ensures D.scoped right result /\ get_sort result == get_sort e)
          (decreases e) =
  match e, result with
  | Var _ _, _ -> ()
  | App f args, App _ results ->
    lemma_apply_args_scope theta left right args results f.domain
  | Quantifier _ bound _ body, Quantifier _ _ _ body' ->
    LP.rev_length bound;
    lemma_under_substitution_scopes theta (L.rev bound) left right;
    lemma_apply_scope (Sub.under (L.length bound) theta)
      (L.rev bound @ left) (L.rev bound @ right) body body'
  | _, _ -> ()

and lemma_apply_args_scope (theta:Sub.substitution) (left right:list sort)
                           (args results:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args left args /\ sorts_match args ss /\
                    substitution_scopes theta left right /\
                    Sub.apply_args theta args == Some results)
          (ensures D.scoped_args right results /\ sorts_match results ss)
          (decreases args) =
  match args, results, ss with
  | e :: rest, e' :: rest', _ :: tail ->
    lemma_apply_scope theta left right e e';
    lemma_apply_args_scope theta left right rest rest' tail
  | _, _, _ -> ()

let lift_environments (#base:sort -> Type0) (sigma:V.signature)
                      (amount cutoff:nat) (left right:list sort)
                      (rho:V.environment base sigma left) (eta:V.environment base sigma right) : prop =
  forall (n:nat{n < L.length left}).
    let j = lift_index amount cutoff n in
    if j < L.length right
    then L.index left n == L.index right j /\ rho n == eta j
    else False

let rec lemma_extend_tail_index (#base:sort -> Type0) (sigma:V.signature)
                               (bound scope:list sort) (vs:V.arguments base sigma bound)
                               (rho:V.environment base sigma scope) (n:nat{n < L.length scope})
  : Lemma (ensures
            (let j = n + L.length bound in
             if j < L.length (bound @ scope)
             then D.scoped (bound @ scope) (Var j (L.index scope n)) /\
                  V.extend sigma scope bound vs rho j == rho n
             else False))
          (decreases bound) =
  LP.append_length bound scope;
  match bound, vs with
  | [], [] -> ()
  | _ :: rest, _ :: tail -> lemma_extend_tail_index sigma rest scope tail rho n
  | _, _ -> FStar.Pervasives.false_elim ()

let lemma_lift_under_environments (#base:sort -> Type0) (sigma:V.signature)
                                  (bound scope:list sort) (vs:V.arguments base sigma bound)
                                  (rho:V.environment base sigma scope)
  : Lemma (lift_environments sigma (L.length bound) 0 scope (bound @ scope)
             rho (V.extend sigma scope bound vs rho)) =
  let indices (n:nat{n < L.length scope})
    : Lemma (
        let j = n + L.length bound in
        if j < L.length (bound @ scope)
        then L.index scope n == L.index (bound @ scope) j /\
             rho n == V.extend sigma scope bound vs rho j
        else False) =
    lemma_extend_tail_index sigma bound scope vs rho n in
  FStar.Classical.forall_intro indices

let rec lemma_lift_extend_index (#base:sort -> Type0) (sigma:V.signature)
                               (amount cutoff:nat) (left right bound:list sort)
                               (rho:V.environment base sigma left) (eta:V.environment base sigma right)
                               (vs:V.arguments base sigma bound)
                               (n:nat{n < L.length (bound @ left)})
  : Lemma (requires lift_environments sigma amount cutoff left right rho eta)
          (ensures
            (let j = lift_index amount (cutoff + L.length bound) n in
             if j < L.length (bound @ right)
             then L.index (bound @ left) n == L.index (bound @ right) j /\
                  V.extend sigma left bound vs rho n == V.extend sigma right bound vs eta j
             else False))
          (decreases bound) =
  LP.append_length bound left;
  LP.append_length bound right;
  match bound, vs with
  | [], [] -> ()
  | _ :: rest, _ :: tail ->
    if n > 0 then lemma_lift_extend_index sigma amount cutoff left right rest rho eta tail (n - 1)
  | _, _ -> FStar.Pervasives.false_elim ()

let rec lemma_lift (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                   (amount cutoff:nat) (left right:list sort)
                   (rho:V.environment base sigma left) (eta:V.environment base sigma right)
                   (e:expr)
  : Lemma (requires D.scoped left e /\ D.scoped right (B.lift amount cutoff e) /\
                    lift_environments sigma amount cutoff left right rho eta)
          (ensures V.evaluate sigma i left rho e ==
                   V.evaluate sigma i right eta (B.lift amount cutoff e))
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args -> lemma_lift_args sigma i amount cutoff left right rho eta args f.domain
  | Quantifier k bound _ body ->
    LP.rev_length bound;
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (
          V.evaluate sigma i (L.rev bound @ left)
            (V.extend sigma left (L.rev bound) vs rho) body ==
          V.evaluate sigma i (L.rev bound @ right)
            (V.extend sigma right (L.rev bound) vs eta)
            (B.lift amount (cutoff + L.length bound) body)) =
      let indices (n:nat{n < L.length (L.rev bound @ left)})
        : Lemma (
            let j = lift_index amount (cutoff + L.length bound) n in
            if j < L.length (L.rev bound @ right)
            then L.index (L.rev bound @ left) n == L.index (L.rev bound @ right) j /\
                 V.extend sigma left (L.rev bound) vs rho n ==
                 V.extend sigma right (L.rev bound) vs eta j
            else False) =
        lemma_lift_extend_index sigma amount cutoff left right (L.rev bound) rho eta vs n in
      FStar.Classical.forall_intro indices;
      lemma_lift sigma i amount (cutoff + L.length bound) (L.rev bound @ left) (L.rev bound @ right)
        (V.extend sigma left (L.rev bound) vs rho)
        (V.extend sigma right (L.rev bound) vs eta) body in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i left right rho eta k bound (get_sort body)
      body (B.lift amount (cutoff + L.length bound) body)

and lemma_lift_args (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                    (amount cutoff:nat) (left right:list sort)
                    (rho:V.environment base sigma left) (eta:V.environment base sigma right)
                    (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args left args /\ D.scoped_args right (B.lift_args amount cutoff args) /\
                    sorts_match args ss /\ sorts_match (B.lift_args amount cutoff args) ss /\
                    lift_environments sigma amount cutoff left right rho eta)
          (ensures V.evaluate_args sigma i left rho args ss ==
                   V.evaluate_args sigma i right eta (B.lift_args amount cutoff args) ss)
          (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_lift sigma i amount cutoff left right rho eta e;
    lemma_lift_args sigma i amount cutoff left right rho eta rest tail
  | _, _ -> ()

let lemma_lift_under (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                     (bound scope:list sort) (vs:V.arguments base sigma bound)
                     (rho:V.environment base sigma scope) (e:expr)
  : Lemma (requires D.scoped scope e)
          (ensures D.scoped (bound @ scope) (B.lift (L.length bound) 0 e) /\
                   get_sort (B.lift (L.length bound) 0 e) == get_sort e /\
                   V.evaluate sigma i scope rho e ==
                   V.evaluate sigma i (bound @ scope) (V.extend sigma scope bound vs rho)
                     (B.lift (L.length bound) 0 e)) =
  lemma_lift_under_scope bound scope e;
  lemma_lift_under_environments sigma bound scope vs rho;
  lemma_lift sigma i (L.length bound) 0 scope (bound @ scope)
    rho (V.extend sigma scope bound vs rho) e

let substitution_environments (#base:sort -> Type0) (sigma:V.signature)
                              (i:V.interpretation base sigma) (theta:Sub.substitution)
                              (left right:list sort)
                              (rho:V.environment base sigma left)
                              (eta:V.environment base sigma right) : prop =
  forall (n:nat{n < L.length left}).
    match theta n (L.index left n) with
    | Some e ->
      D.scoped right e /\ get_sort e == L.index left n /\
      rho n == V.evaluate sigma i right eta e
    | None -> True

let rec lemma_extend_prefix_equal (#base:sort -> Type0) (sigma:V.signature)
                                  (bound left right:list sort)
                                  (vs:V.arguments base sigma bound)
                                  (rho:V.environment base sigma left)
                                  (eta:V.environment base sigma right)
                                  (n:nat{n < L.length bound})
  : Lemma (V.extend sigma left bound vs rho n == V.extend sigma right bound vs eta n)
          (decreases bound) =
  LP.append_length bound left;
  LP.append_length bound right;
  match bound, vs with
  | _ :: rest, _ :: tail ->
    if n > 0 then lemma_extend_prefix_equal sigma rest left right tail rho eta (n - 1)
  | _, _ -> FStar.Pervasives.false_elim ()

let lemma_under_substitution_environments (#base:sort -> Type0) (sigma:V.signature)
                                         (i:V.interpretation base sigma)
                                         (theta:Sub.substitution) (bound left right:list sort)
                                         (vs:V.arguments base sigma bound)
                                         (rho:V.environment base sigma left)
                                         (eta:V.environment base sigma right)
  : Lemma (requires substitution_environments sigma i theta left right rho eta)
          (ensures substitution_environments sigma i (Sub.under (L.length bound) theta)
                     (bound @ left) (bound @ right)
                     (V.extend sigma left bound vs rho) (V.extend sigma right bound vs eta)) =
  LP.append_length bound left;
  LP.append_length bound right;
  let indices (n:nat{n < L.length (bound @ left)})
    : Lemma (
        match Sub.under (L.length bound) theta n (L.index (bound @ left) n) with
        | Some e ->
          D.scoped (bound @ right) e /\ get_sort e == L.index (bound @ left) n /\
          V.extend sigma left bound vs rho n ==
            V.evaluate sigma i (bound @ right) (V.extend sigma right bound vs eta) e
        | None -> True) =
    lemma_scope_index bound left n;
    if n < L.length bound then (
      lemma_scope_index bound right n;
      lemma_extend_prefix_equal sigma bound left right vs rho eta n)
    else (
      let j = n - L.length bound in
      lemma_extend_tail_index sigma bound left vs rho j;
      match theta j (L.index left j) with
      | Some e ->
        assert (D.scoped right e /\ get_sort e == L.index left j /\
                rho j == V.evaluate sigma i right eta e);
        lemma_lift_under sigma i bound right vs eta e
      | None -> ())
  in
  FStar.Classical.forall_intro indices

let rec lemma_apply (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                    (theta:Sub.substitution) (left right:list sort)
                    (rho:V.environment base sigma left) (eta:V.environment base sigma right)
                    (e result:expr)
  : Lemma (requires D.scoped left e /\ D.scoped right result /\
                    substitution_environments sigma i theta left right rho eta /\
                    Sub.apply theta e == Some result)
          (ensures get_sort e == get_sort result /\
                   V.evaluate sigma i left rho e == V.evaluate sigma i right eta result)
          (decreases e) =
  match e, result with
  | Var _ _, _ -> ()
  | App f args, App _ results ->
    lemma_apply_args sigma i theta left right rho eta args results f.domain
  | Quantifier k bound _ body, Quantifier _ _ _ body' ->
    LP.rev_length bound;
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (
          V.evaluate sigma i (L.rev bound @ left)
            (V.extend sigma left (L.rev bound) vs rho) body ==
          V.evaluate sigma i (L.rev bound @ right)
            (V.extend sigma right (L.rev bound) vs eta) body') =
      lemma_under_substitution_environments sigma i theta (L.rev bound) left right vs rho eta;
      lemma_apply sigma i (Sub.under (L.length bound) theta)
        (L.rev bound @ left) (L.rev bound @ right)
        (V.extend sigma left (L.rev bound) vs rho)
        (V.extend sigma right (L.rev bound) vs eta) body body' in
    FStar.Classical.forall_intro pointwise;
    V.lemma_quantifier_environments sigma i left right rho eta k bound (get_sort body) body body'
  | _, _ -> ()

and lemma_apply_args (#base:sort -> Type0) (sigma:V.signature) (i:V.interpretation base sigma)
                     (theta:Sub.substitution) (left right:list sort)
                     (rho:V.environment base sigma left) (eta:V.environment base sigma right)
                     (args results:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args left args /\ D.scoped_args right results /\
                    sorts_match args ss /\ sorts_match results ss /\
                    substitution_environments sigma i theta left right rho eta /\
                    Sub.apply_args theta args == Some results)
          (ensures V.evaluate_args sigma i left rho args ss ==
                   V.evaluate_args sigma i right eta results ss)
          (decreases args) =
  match args, results, ss with
  | e :: rest, e' :: rest', _ :: tail ->
    lemma_apply sigma i theta left right rho eta e e';
    lemma_apply_args sigma i theta left right rho eta rest rest' tail
  | _, _, _ -> ()

let rec lemma_argument_lookup (#base:sort -> Type0) (sigma:V.signature)
                              (i:V.interpretation base sigma) (scope:list sort)
                              (rho:V.environment base sigma scope) (args:list expr) (ss:list sort)
                              (n:nat{n < L.length ss})
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss)
          (ensures n < L.length args /\ D.scoped scope (L.index args n) /\
                   get_sort (L.index args n) == L.index ss n /\
                   V.extend sigma scope ss (V.evaluate_args sigma i scope rho args ss) rho n ==
                   V.evaluate sigma i scope rho (L.index args n))
          (decreases args) =
  LP.append_length ss scope;
  match args, ss with
  | e :: rest, s :: tail ->
    if n > 0 then lemma_argument_lookup sigma i scope rho rest tail (n - 1)
    else V.lemma_sort_eq (get_sort e) s
  | _, _ -> ()

let rec lemma_sorts_length (args:list expr) (ss:list sort)
  : Lemma (requires sorts_match args ss) (ensures L.length args == L.length ss)
          (decreases args) =
  match args, ss with
  | _ :: rest, _ :: tail -> lemma_sorts_length rest tail
  | _, _ -> ()

let lemma_arguments_environments (#base:sort -> Type0) (sigma:V.signature)
                                 (i:V.interpretation base sigma) (scope:list sort)
                                 (rho:V.environment base sigma scope) (args:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss)
          (ensures substitution_environments sigma i (Sub.arguments args) (ss @ scope) scope
                     (V.extend sigma scope ss (V.evaluate_args sigma i scope rho args ss) rho) rho) =
  LP.append_length ss scope;
  lemma_sorts_length args ss;
  let indices (n:nat{n < L.length (ss @ scope)})
    : Lemma (
        match Sub.arguments args n (L.index (ss @ scope) n) with
        | Some e ->
          D.scoped scope e /\ get_sort e == L.index (ss @ scope) n /\
          V.extend sigma scope ss (V.evaluate_args sigma i scope rho args ss) rho n ==
            V.evaluate sigma i scope rho e
        | None -> True) =
    lemma_scope_index ss scope n;
    if n < L.length ss then
      lemma_argument_lookup sigma i scope rho args ss n
    else (
      let j = n - L.length ss in
      lemma_extend_tail_index sigma ss scope (V.evaluate_args sigma i scope rho args ss) rho j)
  in
  FStar.Classical.forall_intro indices

let lemma_substitution_scopes_of_environments (#base:sort -> Type0) (sigma:V.signature)
                                              (i:V.interpretation base sigma)
                                              (theta:Sub.substitution) (left right:list sort)
                                              (rho:V.environment base sigma left)
                                              (eta:V.environment base sigma right)
  : Lemma (requires substitution_environments sigma i theta left right rho eta)
          (ensures substitution_scopes theta left right) =
  let indices (n:nat{n < L.length left})
    : Lemma (
        match theta n (L.index left n) with
        | Some e -> D.scoped right e /\ get_sort e == L.index left n
        | None -> True) = () in
  FStar.Classical.forall_intro indices

let lemma_substitute (#base:sort -> Type0) (sigma:V.signature)
                     (i:V.interpretation base sigma) (scope:list sort)
                     (rho:V.environment base sigma scope) (args:list expr) (ss:list sort)
                     (body result:expr)
  : Lemma (requires D.scoped_args scope args /\ sorts_match args ss /\
                    D.scoped (ss @ scope) body /\ Sub.substitute args body == Some result)
          (ensures D.scoped scope result /\ get_sort body == get_sort result /\
                   V.evaluate sigma i (ss @ scope)
                     (V.extend sigma scope ss (V.evaluate_args sigma i scope rho args ss) rho) body ==
                   V.evaluate sigma i scope rho result) =
  let source = V.extend sigma scope ss (V.evaluate_args sigma i scope rho args ss) rho in
  lemma_arguments_environments sigma i scope rho args ss;
  lemma_substitution_scopes_of_environments sigma i (Sub.arguments args) (ss @ scope) scope source rho;
  lemma_apply_scope (Sub.arguments args) (ss @ scope) scope body result;
  lemma_apply sigma i (Sub.arguments args) (ss @ scope) scope source rho body result
