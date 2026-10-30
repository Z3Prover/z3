module AuditCanonicalOps
open Z3AstTheory
open Z3ValueTheory
open Z3CanonicalOps

let ult_tag : decl_kind = 114
let accessor_tag : decl_kind = 202

(* O1: a declaration named "=" carrying the BV unsigned-less-than tag is not canonical. *)
let clash_eq : func_decl =
  { decl_name = "="; domain = [bool_sort; bool_sort]; range = bool_sort;
    interp = Some ult_tag; int_params = [] }
let o1 () : Lemma (not (canonical_eq clash_eq) /\ not (canonical_connective clash_eq)) = ()

(* O2: a datatype accessor named "and" is not a canonical connective, for any domain. *)
let o2 (dom:list sort) (r:sort)
  : Lemma (not (canonical_connective
      { decl_name = "and"; domain = dom; range = r; interp = Some accessor_tag; int_params = [] })) = ()

(* O3: any canonical connective has a Boolean tag and so cannot carry a BV/datatype tag. *)
let o3 (f:func_decl)
  : Lemma (requires canonical_connective f)
          (ensures f.interp <> Some ult_tag /\ f.interp <> Some accessor_tag) = ()
