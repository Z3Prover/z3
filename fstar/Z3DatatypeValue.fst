module Z3DatatypeValue

open Z3AstTheory
open FStar.List.Tot
module D = Z3Definitions
module L = FStar.List.Tot
module P = FStar.List.Tot.Properties

type signature = list func_decl

let rec lemma_sort_eq (a b:sort)
  : Lemma (ensures sort_eq a b <==> a == b) (decreases a) =
  match a, b with
  | ArraySort xs x, ArraySort ys y -> lemma_sort_list_eq xs ys; lemma_sort_eq x y
  | _, _ -> ()

and lemma_sort_list_eq (xs ys:list sort)
  : Lemma (ensures sort_list_eq xs ys <==> xs == ys) (decreases xs) =
  match xs, ys with
  | x :: rest, y :: tail -> lemma_sort_eq x y; lemma_sort_list_eq rest tail
  | _, _ -> ()

let rec datatype_sort (sigma:signature) (s:sort) : Tot bool (decreases sigma) =
  match sigma with
  | [] -> false
  | f :: rest -> f.range = s || datatype_sort rest s

let rec contains_datatype (sigma:signature) (s:sort) : Tot bool (decreases s) =
  datatype_sort sigma s ||
  (match s with
   | BaseSort _ -> false
   | ArraySort domains range -> contains_datatype_args sigma domains || contains_datatype sigma range)

and contains_datatype_args (sigma:signature) (ss:list sort) : Tot bool (decreases ss) =
  match ss with
  | [] -> false
  | s :: rest -> contains_datatype sigma s || contains_datatype_args sigma rest

noeq
type tree (base:sort -> Type0) =
  | Scalar : s:sort -> base s -> tree base
  | Constructor : symbol:func_decl -> arguments:list (tree base) -> tree base

let rec has_sort (#base:sort -> Type0) (sigma:signature) (s:sort) (v:tree base)
  : Tot bool (decreases v) =
  match v with
  | Scalar t _ -> s = t && not (datatype_sort sigma s)
  | Constructor f xs -> L.mem f sigma && f.range = s && fields_have_sorts sigma f.domain xs

and fields_have_sorts (#base:sort -> Type0) (sigma:signature)
                     (ss:list sort) (vs:list (tree base))
  : Tot bool (decreases vs) =
  match ss, vs with
  | [], [] -> true
  | s :: rest, v :: tail -> has_sort sigma s v && fields_have_sorts sigma rest tail
  | _, _ -> false

type value (base:sort -> Type0) (sigma:signature) (s:sort) =
  v:tree base{has_sort sigma s v}

type arguments (base:sort -> Type0) (sigma:signature) (ss:list sort) =
  vs:list (tree base){fields_have_sorts sigma ss vs}

let rec map_base (#a #b:sort -> Type0) (convert:(s:sort -> a s -> b s)) (v:tree a)
  : Tot (tree b) (decreases v) =
  match v with
  | Scalar s x -> Scalar s (convert s x)
  | Constructor f xs -> Constructor f (map_base_fields convert xs)

and map_base_fields (#a #b:sort -> Type0) (convert:(s:sort -> a s -> b s))
                    (xs:list (tree a))
  : Tot (list (tree b)) (decreases xs) =
  match xs with
  | [] -> []
  | x :: rest -> map_base convert x :: map_base_fields convert rest

let rec lemma_map_base (#a #b:sort -> Type0) (convert:(s:sort -> a s -> b s))
                       (sigma:signature) (s:sort) (v:tree a)
  : Lemma (has_sort sigma s (map_base convert v) == has_sort sigma s v) (decreases v) =
  match v with
  | Scalar _ _ -> ()
  | Constructor f xs -> lemma_map_base_fields convert sigma f.domain xs

and lemma_map_base_fields (#a #b:sort -> Type0) (convert:(s:sort -> a s -> b s))
                          (sigma:signature) (ss:list sort) (xs:list (tree a))
  : Lemma (fields_have_sorts sigma ss (map_base_fields convert xs) == fields_have_sorts sigma ss xs)
          (decreases xs) =
  match ss, xs with
  | s :: tail, x :: rest -> lemma_map_base convert sigma s x; lemma_map_base_fields convert sigma tail rest
  | _, _ -> ()

let construct (#base:sort -> Type0) (sigma:signature)
              (f:func_decl{L.mem f sigma}) (xs:arguments base sigma f.domain)
  : value base sigma f.range = Constructor f xs

let recognize (#base:sort -> Type0) (f:func_decl) (v:tree base) : bool =
  match v with Constructor g _ -> f = g | _ -> false

let fields (#base:sort -> Type0) (v:tree base) : list (tree base) =
  match v with Constructor _ xs -> xs | _ -> []

let rec lemma_fields_length (#base:sort -> Type0) (sigma:signature)
                            (ss:list sort) (vs:arguments base sigma ss)
  : Lemma (L.length vs == L.length ss) (decreases vs) =
  match ss, vs with
  | _ :: rest, _ :: tail -> lemma_fields_length sigma rest tail
  | _, _ -> ()

let rec lemma_fields_index (#base:sort -> Type0) (sigma:signature)
                           (ss:list sort) (vs:arguments base sigma ss)
                           (n:nat{n < L.length ss})
  : Lemma (ensures n < L.length vs /\ has_sort sigma (L.index ss n) (L.index vs n))
          (decreases vs) =
  match ss, vs with
  | _ :: rest, _ :: tail -> if n = 0 then () else lemma_fields_index sigma rest tail (n - 1)
  | _, _ -> ()

let select (#base:sort -> Type0) (sigma:signature) (f:func_decl{L.mem f sigma})
           (n:nat{n < L.length f.domain})
           (fallback:value base sigma f.range -> value base sigma (L.index f.domain n))
           (v:value base sigma f.range)
  : value base sigma (L.index f.domain n) =
  match v with
  | Constructor g xs ->
    if f = g then (
      lemma_fields_index sigma f.domain xs n;
      L.index xs n)
    else fallback v
  | _ -> fallback v

let lemma_disjoint (#base:sort -> Type0) (f g:func_decl) (xs ys:list (tree base))
  : Lemma (requires f <> g) (ensures Constructor f xs =!= Constructor g ys) = ()

let lemma_injective (#base:sort -> Type0) (f:func_decl) (xs ys:list (tree base))
  : Lemma (Constructor f xs == Constructor f ys <==> xs == ys) = ()

let lemma_select_match (#base:sort -> Type0) (sigma:signature) (f:func_decl{L.mem f sigma})
                       (xs:arguments base sigma f.domain) (n:nat{n < L.length f.domain})
                       (fallback:value base sigma f.range -> value base sigma (L.index f.domain n))
  : Lemma (ensures n < L.length xs /\
                   select sigma f n fallback (construct sigma f xs) == L.index xs n) =
  lemma_fields_index sigma f.domain xs n

let lemma_select_mismatch (#base:sort -> Type0) (sigma:signature) (f:func_decl{L.mem f sigma})
                          (n:nat{n < L.length f.domain})
                          (fallback:value base sigma f.range -> value base sigma (L.index f.domain n))
                          (v:value base sigma f.range)
  : Lemma (requires not (recognize f v))
          (ensures select sigma f n fallback v == fallback v) =
  match v with Constructor _ _ -> () | _ -> ()

let lemma_reconstruct (#base:sort -> Type0) (sigma:signature) (f:func_decl)
                      (v:value base sigma f.range)
  : Lemma (requires recognize f v)
          (ensures Constructor f (fields v) == v /\
                   fields_have_sorts sigma f.domain (fields v))
  = match v with Constructor _ _ -> () | _ -> ()

let lemma_rebuild_from_selectors (#base:sort -> Type0) (sigma:signature)
                                (f:func_decl{L.mem f sigma})
                                (v:value base sigma f.range)
                                (xs:arguments base sigma f.domain{L.length xs = L.length f.domain})
                                (fallback:(n:nat{n < L.length f.domain} ->
                                  value base sigma f.range -> value base sigma (L.index f.domain n)))
  : Lemma (requires recognize f v /\
                    (forall (n:nat). n < L.length f.domain ==>
                      L.index xs n == select sigma f n (fallback n) v))
          (ensures construct sigma f xs == v) =
  lemma_reconstruct sigma f v;
  lemma_fields_length sigma f.domain (fields v);
  let at (n:nat)
    : Lemma (n < L.length xs ==> L.index xs n == L.index (fields v) n) =
    if n < L.length xs then lemma_select_match sigma f (fields v) n (fallback n) in
  FStar.Classical.forall_intro at;
  P.index_extensionality xs (fields v)

let rec constructors_of (sigma:signature) (s:sort) : Tot (list func_decl) (decreases sigma) =
  match sigma with
  | [] -> []
  | f :: rest -> if f.range = s then f :: constructors_of rest s else constructors_of rest s

let rec lemma_constructor_member (sigma:signature) (s:sort) (f:func_decl)
  : Lemma (requires L.mem f sigma /\ f.range == s)
          (ensures L.mem f (constructors_of sigma s))
          (decreases sigma) =
  match sigma with
  | [] -> ()
  | g :: rest -> if f <> g then lemma_constructor_member rest s f

let lemma_exhaustive (#base:sort -> Type0) (sigma:signature) (s:sort)
                     (v:value base sigma s)
  : Lemma (requires datatype_sort sigma s)
          (ensures exists (f:func_decl). L.mem f (constructors_of sigma s) /\ recognize f v) =
  match v with
  | Constructor f _ -> lemma_constructor_member sigma s f
  | _ -> ()

let rec size (#base:sort -> Type0) (v:tree base) : Tot pos (decreases v) =
  match v with Scalar _ _ -> 1 | Constructor _ xs -> 1 + fields_size xs

and fields_size (#base:sort -> Type0) (xs:list (tree base)) : Tot nat (decreases xs) =
  match xs with [] -> 0 | x :: rest -> size x + fields_size rest

let rec lemma_field_size (#base:sort -> Type0) (xs:list (tree base))
                         (n:nat{n < L.length xs})
  : Lemma (size (L.index xs n) <= fields_size xs) (decreases xs) =
  match xs with
  | _ :: rest -> if n = 0 then () else lemma_field_size rest (n - 1)
  | _ -> ()

let lemma_acyclic (#base:sort -> Type0) (f:func_decl) (xs:list (tree base))
                 (n:nat{n < L.length xs})
  : Lemma (ensures size (L.index xs n) < size (Constructor f xs) /\
                   L.index xs n =!= Constructor f xs) =
  lemma_field_size xs n

let rec descendant (#base:sort -> Type0) (path:list nat) (v:tree base)
  : Tot (option (tree base)) (decreases path) =
  match path with
  | [] -> Some v
  | n :: rest ->
    (match v with
     | Constructor _ xs -> if n < L.length xs then descendant rest (L.index xs n) else None
     | _ -> None)

let rec lemma_descendant_size (#base:sort -> Type0) (path:list nat) (v w:tree base)
  : Lemma (requires descendant path v == Some w)
          (ensures size w <= size v /\ (path <> [] ==> size w < size v /\ w =!= v))
          (decreases path) =
  match path with
  | [] -> ()
  | n :: rest ->
    (match v with
     | Constructor _ xs ->
       lemma_field_size xs n;
       lemma_descendant_size rest (L.index xs n) w
     | _ -> ())

let rec inhabit (#base:sort -> Type0) (fuel:nat) (sigma:signature)
                (base_value:(s:sort -> base s)) (s:sort)
  : Tot (option (value base sigma s)) (decreases %[(fuel <: nat); (2 <: nat); (0 <: nat)]) =
  if not (datatype_sort sigma s) then Some (Scalar s (base_value s))
  else if fuel = 0 then None
  else inhabit_constructor fuel sigma base_value sigma s

and inhabit_constructor (#base:sort -> Type0) (fuel:pos) (sigma:signature)
                        (base_value:(s:sort -> base s)) (candidates:list func_decl)
                        (s:sort)
  : Tot (option (value base sigma s))
        (decreases %[(fuel <: nat); (1 <: nat); L.length candidates]) =
  match candidates with
  | [] -> None
  | f :: rest ->
    if f.range <> s || not (L.mem f sigma) then inhabit_constructor fuel sigma base_value rest s
    else match inhabit_fields fuel sigma base_value f.domain with
      | Some xs -> Some (construct sigma f xs)
      | None -> inhabit_constructor fuel sigma base_value rest s

and inhabit_fields (#base:sort -> Type0) (fuel:pos) (sigma:signature)
                   (base_value:(s:sort -> base s)) (ss:list sort)
  : Tot (option (arguments base sigma ss))
        (decreases %[(fuel <: nat); (0 <: nat); L.length ss]) =
  match ss with
  | [] -> Some []
  | s :: rest ->
    (match inhabit (fuel - 1) sigma base_value s, inhabit_fields fuel sigma base_value rest with
     | Some v, Some vs -> Some (v :: vs)
     | _, _ -> None)

type environment (base:sort -> Type0) (sigma:signature) (scope:list sort) =
  n:nat{n < L.length scope} -> value base sigma (L.index scope n)

let rec extend (#base:sort -> Type0) (sigma:signature) (scope bound:list sort)
               (vs:arguments base sigma bound) (rho:environment base sigma scope)
  : Tot (environment base sigma (bound @ scope)) (decreases bound) =
  match bound, vs with
  | [], [] -> rho
  | _ :: rest, v :: tail ->
    let remaining = extend sigma scope rest tail rho in
    fun n -> if n = 0 then v else remaining (n - 1)
  | _, _ -> FStar.Pervasives.false_elim ()

noeq
type interpretation (base:sort -> Type0) (sigma:signature) = {
  application: f:func_decl -> arguments base sigma f.domain -> value base sigma f.range;
  quantification:
    k:quantifier_kind -> bound:list sort -> body_sort:sort ->
    (arguments base sigma (L.rev bound) -> value base sigma body_sort) ->
    value base sigma (quant_sort k bound body_sort);
}

let typed_body (#base:sort -> Type0) (sigma:signature) (bound:list sort) (t:sort)
               (f:(arguments base sigma (L.rev bound) -> Tot (tree base)){
                 forall (vs:arguments base sigma (L.rev bound)). has_sort sigma t (f vs)})
               (vs:arguments base sigma (L.rev bound))
  : value base sigma t = f vs

noextract
let rec expression_size (e:expr) : Tot pos (decreases e) =
  match e with
  | Var _ _ -> 1
  | App _ args -> 1 + expressions_size args
  | Quantifier _ _ _ body -> 1 + expression_size body

and expressions_size (es:list expr) : Tot nat (decreases es) =
  match es with [] -> 0 | e :: rest -> expression_size e + expressions_size rest

let rec evaluate (#base:sort -> Type0) (sigma:signature) (i:interpretation base sigma)
                 (scope:list sort) (rho:environment base sigma scope)
                 (e:expr{D.scoped scope e})
  : Tot (value base sigma (get_sort e)) (decreases %[(expression_size e <: nat); (0 <: nat)]) =
  match e with
  | Var n _ -> rho n
  | App f args ->
    let vs = evaluate_args sigma i scope rho args f.domain in
    if L.mem f sigma then construct sigma f vs else i.application f vs
  | Quantifier k bound _ body ->
    i.quantification k bound (get_sort body)
      (typed_body sigma bound (get_sort body) (evaluate_body sigma i scope rho bound body))

and evaluate_args (#base:sort -> Type0) (sigma:signature) (i:interpretation base sigma)
                  (scope:list sort) (rho:environment base sigma scope)
                  (es:list expr{D.scoped_args scope es})
                  (ss:list sort{sorts_match es ss})
  : Tot (arguments base sigma ss) (decreases %[(expressions_size es <: nat); (1 <: nat)]) =
  match es, ss with
  | [], [] -> []
  | e :: rest, s :: remaining ->
    lemma_sort_eq (get_sort e) s;
    evaluate sigma i scope rho e :: evaluate_args sigma i scope rho rest remaining
  | _, _ -> FStar.Pervasives.false_elim ()

and evaluate_body (#base:sort -> Type0) (sigma:signature) (i:interpretation base sigma)
                  (scope:list sort) (rho:environment base sigma scope) (bound:list sort)
                  (body:expr{D.scoped (L.rev bound @ scope) body})
  : Tot (f:FStar.FunctionalExtensionality.restricted_t (arguments base sigma (L.rev bound))
             (fun _ -> tree base){
           forall (vs:arguments base sigma (L.rev bound)).
             has_sort sigma (get_sort body) (f vs)})
        (decreases %[(expression_size body <: nat); (1 <: nat)]) =
  (* Canonicalize the refined argument domain for quantifier congruence. *)
  FStar.FunctionalExtensionality.on_dom (arguments base sigma (L.rev bound)) (fun vs ->
    (evaluate sigma i (L.rev bound @ scope) (extend sigma scope (L.rev bound) vs rho) body <: tree base))

let lemma_quantifier_congruence (#base:sort -> Type0) (sigma:signature)
                                (i:interpretation base sigma)
                                (scope:list sort) (rho:environment base sigma scope)
                                (k:quantifier_kind) (bound:list sort) (t:sort) (a b:expr)
  : Lemma (requires D.scoped (L.rev bound @ scope) a /\ D.scoped (L.rev bound @ scope) b /\
                    get_sort a == t /\ get_sort b == t /\ (k == Lambda_k \/ t == bool_sort) /\
                    (forall (vs:arguments base sigma (L.rev bound)).
                      evaluate sigma i (L.rev bound @ scope)
                        (extend sigma scope (L.rev bound) vs rho) a ==
                      evaluate sigma i (L.rev bound @ scope)
                        (extend sigma scope (L.rev bound) vs rho) b))
          (ensures evaluate sigma i scope rho (Quantifier k bound (quant_sort k bound t) a) ==
                   evaluate sigma i scope rho (Quantifier k bound (quant_sort k bound t) b)) =
  let left = evaluate_body sigma i scope rho bound a in
  let right = evaluate_body sigma i scope rho bound b in
  let pointwise (vs:arguments base sigma (L.rev bound))
    : Lemma (left vs == right vs) = () in
  FStar.Classical.forall_intro pointwise;
  assert (FStar.FunctionalExtensionality.feq left right);
  FStar.FunctionalExtensionality.extensionality
    (arguments base sigma (L.rev bound)) (fun _ -> tree base) left right;
  assert (left == right);
  assert (evaluate sigma i scope rho (Quantifier k bound (quant_sort k bound t) a) ==
          i.quantification k bound t (typed_body sigma bound t left));
  assert (evaluate sigma i scope rho (Quantifier k bound (quant_sort k bound t) b) ==
          i.quantification k bound t (typed_body sigma bound t right))
