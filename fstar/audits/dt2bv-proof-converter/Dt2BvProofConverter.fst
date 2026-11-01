module Dt2BvProofConverter

module L = FStar.List.Tot
module Tac = FStar.Tactics.V2

(* Enumeration values are constructor indices; BV values are unsigned residues. *)
let rec capacity (width:nat) : Tot pos (decreases width) =
  if width = 0 then 1 else 2 * capacity (width - 1)

let rec encode_from (count:pos) (index:nat{index < count}) (value:nat)
  : Tot nat (decreases (count - index)) =
  if index + 1 = count then index
  else if value = index then index
  else encode_from count (index + 1) value

let rec lemma_encode_from (count:pos) (index:nat{index < count})
                          (value:nat{index <= value /\ value < count})
  : Lemma (encode_from count index value == value)
          (decreases (count - index)) =
  if index + 1 = count || value = index then ()
  else lemma_encode_from count (index + 1) value

let encode (count:pos) (width:nat) (value:nat) : nat =
  encode_from count 0 value % capacity width

let lemma_encode (count:pos) (width:nat{count <= capacity width})
                 (value:nat{value < count})
  : Lemma (encode count width value == value) =
  lemma_encode_from count 0 value

let lemma_range (count:pos) (width:nat{count <= capacity width})
                (value:nat{value < count})
  : Lemma (encode count width value < count) =
  lemma_encode count width value

let lemma_equality (count:pos) (width:nat{count <= capacity width})
                   (left:nat{left < count}) (right:nat{right < count})
  : Lemma ((encode count width left = encode count width right) == (left = right)) =
  lemma_encode count width left;
  lemma_encode count width right

let singleton () : Lemma (encode 1 1 0 == 0 /\ capacity 1 == 2) = ()

(* Denotational model of the proof operations, not a model of the SMT solver.
   An entails witness stands for a sound input proof or checked certificate. *)
type formula (state:Type0) = state -> bool

let rec holds (#state:Type0) (premises:list (formula state)) (model:state)
  : Tot bool (decreases premises) =
  match premises with
  | [] -> true
  | head :: tail -> head model && holds tail model

type entails (#state:Type0) (premises:list (formula state)) (fact:formula state) =
  forall (model:state). holds premises model ==> fact model

let false_formula (#state:Type0) : formula state = fun _ -> false

(* prove: refute one hypothesis, then discharge it with PR_LEMMA. *)
let discharge (#state:Type0) (fact:formula state)
  : Lemma (requires entails [fun model -> not (fact model)] false_formula)
          (ensures entails [] fact) = ()

(* insert: modus ponens uses a proved equivalence AFTER substitution. *)
let rewrite (#state:Type0) (premises:list (formula state)) (before after:formula state)
  : Lemma (requires entails premises before /\
                    entails [] (fun model -> before model = after model))
          (ensures entails premises after) = ()

let bound (#state:Type0) (premises:list (formula state)) (fact:formula state)
  : Lemma (requires entails [] fact) (ensures entails premises fact) = ()

(* Each nested lemma includes the negation of the ambient hypothesis;
   unit resolution then recovers the old conclusion in that hypothesis. *)
let close_ambient (#state:Type0) (fact clause:formula state)
  : Lemma (requires entails [fun model -> not (fact model)] clause)
          (ensures entails [] (fun model -> fact model || clause model)) = ()

let restore_ambient (#state:Type0) (fact clause:formula state)
  : Lemma (requires entails [] (fun model -> fact model || clause model))
          (ensures entails [fun model -> not (fact model)] clause) = ()

let complete_lemma (#state:Type0) (hypotheses remaining:list (formula state))
                   (clause:formula state)
  : Lemma (requires entails hypotheses false_formula /\
                    (forall model. not (clause model) /\ holds remaining model ==>
                                   holds hypotheses model))
          (ensures entails [] (fun model -> not (holds remaining model) || clause model)) = ()

let restore_context (#state:Type0) (hypotheses:list (formula state)) (clause:formula state)
  : Lemma (requires entails [] (fun model -> not (holds hypotheses model) || clause model))
          (ensures entails hypotheses clause) = ()

(* A negated disjunction may be a single quoted hypothesis. Retaining both
   its clause literals and the quoted clause only duplicates its denotation. *)
let absorb_quoted_clause (#state:Type0) (clause:formula state)
  : Lemma (forall model. (clause model || clause model) == clause model) = ()

let pullback (#state:Type0) (substitution:state -> state) (fact:formula state)
  : formula state = fun model -> fact (substitution model)

let rec substitute (#state:Type0) (substitution:state -> state)
                   (facts:list (formula state))
  : Tot (list (formula state)) (decreases facts) =
  match facts with
  | [] -> []
  | head :: tail -> pullback substitution head :: substitute substitution tail

let rec lemma_substitute (#state:Type0) (substitution:state -> state)
                         (facts:list (formula state)) (model:state)
  : Lemma (holds (substitute substitution facts) model ==
           holds facts (substitution model)) (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: tail -> lemma_substitute substitution tail model

noeq type certificates (#state:Type0) (premises:list (formula state))
  : list (formula state) -> Type0 =
  | Empty : certificates premises []
  | Next : head:formula state -> tail:list (formula state) ->
           certificate:squash (entails premises head) ->
           rest:certificates premises tail ->
           certificates premises (head :: tail)

let rec lemma_certificates (#state:Type0) (premises:list (formula state))
                           (facts:list (formula state))
                           (checked:certificates premises facts) (model:state)
  : Lemma (requires holds premises model) (ensures holds facts model)
          (decreases checked) =
  match checked with
  | Empty -> ()
  | Next head tail _certificate rest ->
    assert (head model);
    lemma_certificates premises tail rest model

(* operator(): substitute the refutation, then replace every asserted target
   premise with its prepared proof. Both assertions AND bounds need witnesses. *)
let refutation_transport (#state:Type0) (original target:list (formula state))
                         (substitution:state -> state)
                         (checked:certificates original (substitute substitution target))
  : Lemma (requires entails target false_formula)
          (ensures entails original false_formula) =
  let at_model (model:state) : Lemma (holds original model ==> false_formula model) =
    if holds original model then (
      lemma_certificates original (substitute substitution target) checked model;
      lemma_substitute substitution target model)
  in
  FStar.Classical.forall_intro at_model

(* Ordinary converter composition: the later transformation is converted first. *)
let compose_transport (#state:Type0) (original middle target:list (formula state))
  : Lemma (requires (entails middle false_formula ==> entails original false_formula) /\
                    (entails target false_formula ==> entails middle false_formula))
          (ensures entails target false_formula ==> entails original false_formula) = ()

let rec disjunction (#state:Type0) (branches:list (formula state)) (model:state)
  : Tot bool (decreases branches) =
  match branches with
  | [] -> false
  | head :: tail -> head model || disjunction tail model

noeq type branch_refutations (#state:Type0) (premises:list (formula state))
  : list (formula state) -> Type0 =
  | NoBranches : branch_refutations premises []
  | RefutedBranch : head:formula state -> tail:list (formula state) ->
                    certificate:squash (entails (head :: premises) false_formula) ->
                    rest:branch_refutations premises tail ->
                    branch_refutations premises (head :: tail)

let rec lemma_refuted_branches (#state:Type0) (premises branches:list (formula state))
                              (checked:branch_refutations premises branches) (model:state)
  : Lemma (requires holds premises model)
          (ensures not (disjunction branches model)) (decreases checked) =
  match checked with
  | NoBranches -> ()
  | RefutedBranch head tail _certificate rest ->
    assert (not (head model));
    lemma_refuted_branches premises tail rest model

(* Branch-local conversion precedes discharge; parent conversion follows it. *)
let split_refutation (#state:Type0) (premises branches:list (formula state))
                     (checked:branch_refutations premises branches)
  : Lemma (requires entails premises (fun model -> disjunction branches model))
          (ensures entails premises false_formula) =
  let at_model (model:state) : Lemma (holds premises model ==> false_formula model) =
    if holds premises model then lemma_refuted_branches premises branches checked model
  in
  FStar.Classical.forall_intro at_model

(* AST-valued proof parameters, including quant-inst bindings, are substituted
   together with proof conclusions. Leaving their denotations unchanged is not
   a correct substitution of a proof payload. *)
let rec fields (#state #value:Type0) (parameters:list (state -> value)) (model:state)
  : Tot (list value) (decreases parameters) =
  match parameters with
  | [] -> []
  | head :: tail -> head model :: fields tail model

let rec substitute_parameters (#state #value:Type0) (substitution:state -> state)
                              (parameters:list (state -> value))
  : Tot (list (state -> value)) (decreases parameters) =
  match parameters with
  | [] -> []
  | head :: tail ->
    (fun model -> head (substitution model)) :: substitute_parameters substitution tail

let rec lemma_parameters (#state #value:Type0) (substitution:state -> state)
                         (parameters:list (state -> value)) (model:state)
  : Lemma (fields (substitute_parameters substitution parameters) model ==
           fields parameters (substitution model)) (decreases parameters) =
  match parameters with
  | [] ->
    assert (fields (substitute_parameters substitution parameters) model ==
            fields parameters (substitution model)) by
      (Tac.norm [delta_only ["Dt2BvProofConverter.fields";
                            "Dt2BvProofConverter.substitute_parameters"]; iota; zeta]; Tac.smt ())
  | _ :: tail ->
    lemma_parameters substitution tail model;
    assert (fields (substitute_parameters substitution parameters) model ==
            fields parameters (substitution model)) by
      (Tac.norm [delta_only ["Dt2BvProofConverter.fields";
                            "Dt2BvProofConverter.substitute_parameters"]; iota; zeta]; Tac.smt ())

(* Refute the old unconditional bridge, even when both codes are in range. *)
let old_bridge_is_not_valid () : Lemma
  (encode 3 2 0 == 0 /\ 1 < 3 /\ not ((0 = 0) = (1 = 0))) = ()
