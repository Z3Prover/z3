module Z3BvFreshScope

open Z3AstTheory
module D = Z3ExprScope
module Def = Z3DefinitionRecognition
module BF = Z3BvFreshSyntax
module BW = Z3BvSyntax
module BV = Z3BvSyntax
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

include Z3DefinitionRecognitionScope

let lemma_projection_constructed (width:pos) (original f:func_decl) (bit:nat)
  : Lemma (requires original.domain == [] /\ original.range == BV.bv_sort width /\
                    f.interp == None /\ f.int_params == [] /\ f.domain == [] /\
                    f.range == bool_sort)
          (ensures constructed {
            Def.symbol = f; Def.variables = [];
            Def.body = BW.projection width (App original []) bit }) =
  let body = BW.projection width (App original []) bit in
  assert (D.scoped [] body /\ get_sort body == bool_sort);
  let d = { Def.symbol = f; Def.variables = []; Def.body = body } in
  assert (Def.make_definition [] (App f []) body == Some d);
  lemma_make_constructed [] (App f []) body d

let rec lemma_bits_constructed (width:pos) (original:func_decl) (start:nat)
                               (symbols:list func_decl)
  : Lemma (requires original.domain == [] /\ original.range == BV.bv_sort width /\
                    BF.valid_symbols symbols)
          (ensures constructed_definitions
            (BF.bit_definitions width (App original []) start symbols))
          (decreases symbols) =
  match symbols with
  | [] -> ()
  | f :: rest ->
    lemma_projection_constructed width original f start;
    lemma_bits_constructed width original (start + 1) rest;
    let at (d:Def.definition)
      : Lemma (L.mem d (BF.bit_definitions width (App original []) start symbols) ==>
               constructed d) = () in
    FStar.Classical.forall_intro at

let rec lemma_projections_constructed (rs:list BF.reconstruction)
  : Lemma (requires BF.valid_context rs)
          (ensures constructed_definitions (BF.projection_definitions rs))
          (decreases rs) =
  match rs with
  | [] -> ()
  | r :: rest ->
    lemma_bits_constructed r.BF.width r.BF.original 0 r.BF.symbols;
    lemma_projections_constructed rest;
    let at (d:Def.definition)
      : Lemma (L.mem d (BF.projection_definitions rs) ==> constructed d) =
      LP.append_mem (BF.bit_definitions r.BF.width (BF.source r) 0 r.BF.symbols)
                    (BF.projection_definitions rest) d in
    FStar.Classical.forall_intro at

