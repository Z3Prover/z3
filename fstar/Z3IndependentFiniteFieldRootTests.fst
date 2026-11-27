module Z3IndependentFiniteFieldRootTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module FF = Z3SortedFiniteField
module FR = Z3IndependentFiniteFieldRoot

let numeral : func_decl =
  { decl_name = "ff"; domain = []; range = FF.ff_sort 5;
    interp = Some FF.op_ff_num; int_params = [5; 4] }

let free_symbol : func_decl =
  { decl_name = "x"; domain = []; range = FF.ff_sort 5;
    interp = None; int_params = [] }

let numeral_in_root (u:TR.uninterpreted)
                    (sch:S.checked_schema{not (V.datatype_sort (S.signature sch) (FF.ff_sort 5))})
                    (uf:TR.symbols u sch)
  : Lemma (
    let root = TR.standard u sch (FR.field_symbols u sch 5 uf) in
    let m = FR.model u sch 5 root in
    TR.root_model u sch root /\ m.FF.project (root.V.application numeral []) == 4) =
  let root = TR.standard u sch (FR.field_symbols u sch 5 uf) in
  let m = FR.model u sch 5 root in
  assert_norm (FF.numeral (App numeral []) == Some (5, 4));
  FR.lemma_root_inhabited u sch 5 uf;
  m.FF.numeral_law numeral 4;
  FR.lemma_override_application u sch 5 uf numeral []

let free_symbol_in_root (u:TR.uninterpreted)
                        (sch:S.checked_schema{not (V.datatype_sort (S.signature sch) (FF.ff_sort 5))})
                        (uf:TR.symbols u sch)
  : Lemma ((FR.field_symbols u sch 5 uf).TR.apply free_symbol [] ==
           (TR.standard u sch uf).V.application free_symbol []) =
  assert_norm (FF.numeral (App free_symbol []) == None);
  assert_norm (FF.operation_of free_symbol == None);
  FR.lemma_preserves_other u sch 5 uf free_symbol []
