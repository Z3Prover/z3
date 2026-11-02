(* Red/green tests for checked sort identities (`Z3CheckedSorts`), computed by
   normalization with the validator itself.

   * Accepted: base sorts, a one-index and a two-index array, sorts with
     different untrusted ids and the same structure (equal ids), a domain
     order swap, a range or kind change and names that differ in one digit of
     the native-id prefix (distinct ids), long Unicode names, two names whose
     buckets collide, an empty domain with arity 0, a 16-deep shared chain
     whose unfolded tree has 3^16 nodes, and repeated identical definitions.
   * Refused: dangling, forward (cyclic) and self references; one untrusted
     id defining two names, two arrays or a base and an array; ids and
     references outside [0, 2^32); arities that are negative, huge, or that
     do not match the references.
   * Budgets: the exact preparation and storage units of a fixture succeed
     with nothing left and fail one unit short, by phase; repeated
     definitions are charged again; exhaustion is reported before a later
     structural error; a 4096-character name fails with preparation 0, 1 and
     one short of its exact units.

   `units` is a specification counter: it counts the whole name before
   comparing with the limit, so these tests check results, not that a
   counter scans at most the limit. *)
module Z3CheckedSortsTests

open Z3AstTheory
open Z3CheckedSorts
module L = FStar.List.Tot

let units : name_counter = fun s limit ->
  let n = FStar.String.strlen s in if n <= limit then Some n else None

let budget (p s:nat) : sort_budget = { preparation = p; storage = s }

let ample : sort_budget = budget 100000000 100000000

let rejection (raw:list raw_sort) : option sort_graph_error =
  match validate_sort_graph units raw ample with InvalidSortGraph err -> Some err | _ -> None

let exhaustion (raw:list raw_sort) (b:sort_budget) : option budget_phase =
  match validate_sort_graph units raw b with Exhausted p -> Some p | _ -> None

let used (raw:list raw_sort) (b:sort_budget) : option (int & int) =
  match validate_sort_graph units raw b with
  | Prepared _ _ l -> Some (b.preparation - l.preparation, b.storage - l.storage)
  | _ -> None

let same (raw:list raw_sort) (x y:int) : option bool =
  match validate_sort_graph units raw ample with
  | Prepared g m _ ->
    (match resolve_id g m x, resolve_id g m y with
     | Some i, Some j -> Some (id_equal g i j)
     | _, _ -> None)
  | _ -> None

noextract
let meaning (raw:list raw_sort) (x:int) : option sort =
  match validate_sort_graph units raw ample with
  | Prepared g m _ -> (match resolve_id g m x with Some i -> Some (interpret_sort g i) | None -> None)
  | _ -> None

let int_s : raw_sort = RawBase 1 "Int"
let bool_s : raw_sort = RawBase 2 "Bool"
let int_bool : raw_sort = RawArray 3 1 [1] 2
let basic : list raw_sort = [int_s; bool_s; int_bool]

let int_t : sort = BaseSort "Int"
let bool_t : sort = BaseSort "Bool"

(* --- Accepted ------------------------------------------------------------------------- *)

let pair : list raw_sort = L.append basic [RawArray 4 2 [3; 1] 3; RawArray 5 1 [1] 2; RawBase 9 "Int"]

let structure ()
  : Lemma (meaning pair 1 == Some int_t /\
           meaning pair 3 == Some (ArraySort [int_t] bool_t) /\
           meaning pair 4 == Some (ArraySort [ArraySort [int_t] bool_t; int_t] (ArraySort [int_t] bool_t)) /\
           same pair 3 5 == Some true /\ same pair 1 9 == Some true /\
           same pair 3 4 == Some false /\ same pair 1 2 == Some false)
  = assert_norm (meaning pair 1 == Some int_t);
    assert_norm (meaning pair 3 == Some (ArraySort [int_t] bool_t));
    assert_norm (meaning pair 4 == Some (ArraySort [ArraySort [int_t] bool_t; int_t] (ArraySort [int_t] bool_t)));
    assert_norm (same pair 3 5 == Some true /\ same pair 1 9 == Some true);
    assert_norm (same pair 3 4 == Some false /\ same pair 1 2 == Some false)

let ordered : list raw_sort =
  [int_s; bool_s; RawArray 6 2 [1; 2] 1; RawArray 7 2 [2; 1] 1; RawArray 8 1 [1] 1; int_bool; RawBase 10 "Array"]

let order_range_kind ()
  : Lemma (meaning ordered 6 == Some (ArraySort [int_t; bool_t] int_t) /\
           meaning ordered 7 == Some (ArraySort [bool_t; int_t] int_t) /\
           same ordered 6 7 == Some false /\ same ordered 8 3 == Some false /\ same ordered 10 3 == Some false)
  = assert_norm (meaning ordered 6 == Some (ArraySort [int_t; bool_t] int_t));
    assert_norm (meaning ordered 7 == Some (ArraySort [bool_t; int_t] int_t));
    assert_norm (same ordered 6 7 == Some false /\ same ordered 8 3 == Some false /\ same ordered 10 3 == Some false)

let native : list raw_sort =
  [RawBase 11 "sort!2147483829:Term"; RawBase 12 "sort!2147483830:Term"; RawBase 13 "Term";
   RawBase 14 "sort!2147483829:Term"]

let full_names ()
  : Lemma (meaning native 11 == Some (BaseSort "sort!2147483829:Term") /\
           same native 11 12 == Some false /\ same native 11 13 == Some false /\ same native 11 14 == Some true)
  = assert_norm (meaning native 11 == Some (BaseSort "sort!2147483829:Term"));
    assert_norm (same native 11 12 == Some false /\ same native 11 13 == Some false /\ same native 11 14 == Some true)

let greek : string = "αβγδεζηθικλμνξοπρστυφχψω𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℤ"
let greek' : string = "αβγδεζηθικλμνξοπρστυφχψω𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℨ"

let unicode : list raw_sort = [RawBase 20 greek; RawBase 21 greek; RawBase 22 greek'; RawBase 23 "x퟿"; RawBase 24 "x�"]

let unicode_names ()
  : Lemma (meaning unicode 20 == Some (BaseSort greek) /\
           same unicode 20 21 == Some true /\ same unicode 20 22 == Some false /\
           node_key (NodeBase "x퟿") == node_key (NodeBase "x�") /\ same unicode 23 24 == Some false /\
           node_key (NodeBase "sort!2147483829:Term") == node_key (NodeBase "sort!2147483830:Term"))
  = assert_norm (meaning unicode 20 == Some (BaseSort greek));
    assert_norm (same unicode 20 21 == Some true /\ same unicode 20 22 == Some false);
    assert_norm (node_key (NodeBase "x퟿") == node_key (NodeBase "x�"));
    assert_norm (same unicode 23 24 == Some false);
    assert_norm (node_key (NodeBase "sort!2147483829:Term") == node_key (NodeBase "sort!2147483830:Term"))

let nullary : list raw_sort = [int_s; RawArray 30 0 [] 1]

let empty_domain () : Lemma (meaning nullary 30 == Some (ArraySort [] int_t)) =
  assert_norm (meaning nullary 30 == Some (ArraySort [] int_t))

(* Entry `base + k` is (Array e e e) with e the entry `base + k - 1`. *)
let rec chain (base:int) (depth:nat) : Tot (list raw_sort) (decreases depth) =
  if depth = 0 then [RawBase base "Int"]
  else L.append (chain base (depth - 1)) [RawArray (base + depth) 2 [base + depth - 1; base + depth - 1] (base + depth - 1)]

let chains : list raw_sort = L.append (chain 100 16) (chain 200 16)

let both_same (raw:list raw_sort) (x y x' y':int) : option (bool & bool) =
  match validate_sort_graph units raw ample with
  | Prepared g m _ ->
    (match resolve_id g m x, resolve_id g m y, resolve_id g m x', resolve_id g m y' with
     | Some i, Some j, Some i', Some j' -> Some (id_equal g i j, id_equal g i' j')
     | _, _, _, _ -> None)
  | _ -> None

let shared_depth () : Lemma (both_same chains 116 216 115 216 == Some (true, false)) =
  assert_norm (both_same chains 116 216 115 216 == Some (true, false))

let repeated : list raw_sort = [int_s; int_s; bool_s; int_bool; int_bool]

let duplicates () : Lemma (same repeated 3 3 == Some true /\ same repeated 1 3 == Some false) =
  assert_norm (same repeated 3 3 == Some true /\ same repeated 1 3 == Some false)

(* The theorem, not normalization: every entry of `basic` denotes its content. *)
let basic_reflected ()
  : Lemma (match validate_sort_graph units basic ample with
           | Prepared g m _ -> entry_reflected g m int_s /\ entry_reflected g m int_bool
           | _ -> True)
  = assert_norm (L.mem int_s basic /\ L.mem int_bool basic);
    lemma_validated units basic ample

(* --- Refused ----------------------------------------------------------------------------- *)

let references ()
  : Lemma (rejection [int_s; RawArray 3 1 [99] 1] == Some (DanglingReference 99) /\
           rejection [int_s; RawArray 3 1 [1] 98] == Some (DanglingReference 98) /\
           rejection [RawArray 20 1 [21] 21; RawArray 21 1 [20] 20] == Some (DanglingReference 21) /\
           rejection [int_s; RawArray 22 1 [22] 1] == Some (DanglingReference 22))
  = assert_norm (rejection [int_s; RawArray 3 1 [99] 1] == Some (DanglingReference 99));
    assert_norm (rejection [int_s; RawArray 3 1 [1] 98] == Some (DanglingReference 98));
    assert_norm (rejection [RawArray 20 1 [21] 21; RawArray 21 1 [20] 20] == Some (DanglingReference 21));
    assert_norm (rejection [int_s; RawArray 22 1 [22] 1] == Some (DanglingReference 22))

let conflicts ()
  : Lemma (rejection [RawBase 1 "Int"; RawBase 1 "Bool"] == Some (ConflictingDefinition 1) /\
           rejection [RawBase 7 "sort!2147483829:Term"; RawBase 7 "sort!2147483830:Term"] ==
             Some (ConflictingDefinition 7) /\
           rejection [int_s; bool_s; RawArray 1 1 [1] 2] == Some (ConflictingDefinition 1) /\
           rejection [int_s; bool_s; RawArray 6 2 [1; 2] 1; RawArray 6 2 [2; 1] 1] == Some (ConflictingDefinition 6))
  = assert_norm (rejection [RawBase 1 "Int"; RawBase 1 "Bool"] == Some (ConflictingDefinition 1));
    assert_norm (rejection [RawBase 7 "sort!2147483829:Term"; RawBase 7 "sort!2147483830:Term"] ==
                 Some (ConflictingDefinition 7));
    assert_norm (rejection [int_s; bool_s; RawArray 1 1 [1] 2] == Some (ConflictingDefinition 1));
    assert_norm (rejection [int_s; bool_s; RawArray 6 2 [1; 2] 1; RawArray 6 2 [2; 1] 1] ==
                 Some (ConflictingDefinition 6))

let huge : int = 1267650600228229401496703205376

let malformed_ids ()
  : Lemma (rejection [RawBase (-1) "Int"] == Some (MalformedId (-1)) /\
           rejection [RawBase 4294967296 "Int"] == Some (MalformedId 4294967296) /\
           rejection [RawBase 4294967295 "Int"] == None /\
           rejection [RawBase huge "Int"] == Some (MalformedId huge) /\
           rejection [int_s; RawArray 3 1 [(-5)] 1] == Some (MalformedId (-5)) /\
           rejection [int_s; RawArray 3 1 [1] huge] == Some (MalformedId huge))
  = assert_norm (rejection [RawBase (-1) "Int"] == Some (MalformedId (-1)));
    assert_norm (rejection [RawBase 4294967296 "Int"] == Some (MalformedId 4294967296));
    assert_norm (rejection [RawBase 4294967295 "Int"] == None);
    assert_norm (rejection [RawBase huge "Int"] == Some (MalformedId huge));
    assert_norm (rejection [int_s; RawArray 3 1 [(-5)] 1] == Some (MalformedId (-5)));
    assert_norm (rejection [int_s; RawArray 3 1 [1] huge] == Some (MalformedId huge))

let arities ()
  : Lemma (rejection [int_s; bool_s; RawArray 3 2 [1] 2] == Some (WrongArity 3) /\
           rejection [int_s; bool_s; RawArray 3 0 [1] 2] == Some (WrongArity 3) /\
           rejection [int_s; bool_s; RawArray 3 (-1) [] 2] == Some (WrongArity 3) /\
           rejection [int_s; bool_s; RawArray 3 huge [1] 2] == Some (WrongArity 3))
  = assert_norm (rejection [int_s; bool_s; RawArray 3 2 [1] 2] == Some (WrongArity 3));
    assert_norm (rejection [int_s; bool_s; RawArray 3 0 [1] 2] == Some (WrongArity 3));
    assert_norm (rejection [int_s; bool_s; RawArray 3 (-1) [] 2] == Some (WrongArity 3));
    assert_norm (rejection [int_s; bool_s; RawArray 3 huge [1] 2] == Some (WrongArity 3))

(* --- Budgets ------------------------------------------------------------------------------ *)

(* Preparation. Int: 1 + 3 characters, 33 bucket lookup, 66 node and bucket
   update, 33 + 33 id lookup and update (169). Bool: 1 + 4 + 33 + 66 + 66 (170).
   Array Int Bool: 1, 1 + 33 per reference, 33 + 66 + 66 (234).
   Storage. Each name: 1 state, 2 + 66 node, 33 id binding (102); the array:
   also 2 for its one reference (104). *)
let basic_units : nat = 573
let basic_cells : nat = 308

let exact_budgets ()
  : Lemma (used basic ample == Some (basic_units, basic_cells) /\
           used basic (budget basic_units basic_cells) == Some (basic_units, basic_cells) /\
           exhaustion basic (budget (basic_units - 1) basic_cells) == Some Preparation /\
           exhaustion basic (budget basic_units (basic_cells - 1)) == Some Storage)
  = assert_norm (used basic ample == Some (basic_units, basic_cells));
    assert_norm (used basic (budget basic_units basic_cells) == Some (basic_units, basic_cells));
    assert_norm (exhaustion basic (budget (basic_units - 1) basic_cells) == Some Preparation);
    assert_norm (exhaustion basic (budget basic_units (basic_cells - 1)) == Some Storage)

(* A repeated Int costs 1 + 3, 33 + (1 + 3) to find it and 33 to see its id
   bound, and one storage unit for its state. *)
let charged_duplicates () : Lemma (used [int_s; int_s; int_s] ample == Some (169 + 2 * 74, 102 + 2)) =
  assert_norm (used [int_s; int_s; int_s] ample == Some (169 + 2 * 74, 102 + 2))

let exhausted_first ()
  : Lemma (exhaustion [int_s; RawArray 3 1 [99] 1] (budget 168 ample.storage) == Some Preparation /\
           exhaustion [RawBase 20 greek] (budget 50 ample.storage) == Some Preparation)
  = assert_norm (exhaustion [int_s; RawArray 3 1 [99] 1] (budget 168 ample.storage) == Some Preparation);
    assert_norm (exhaustion [RawBase 20 greek] (budget 50 ample.storage) == Some Preparation)

let rec repeat (n:nat) (c:FStar.Char.char) : Tot (list FStar.Char.char) (decreases n) =
  if n = 0 then [] else c :: repeat (n - 1) c

let giant : string = FStar.String.string_of_list (repeat 4096 'g')

(* 1 + 4096 characters + 33 + 66 + 33 + 33; storage 102. *)
let giant_units : nat = 4262

let giant_name ()
  : Lemma (exhaustion [RawBase 1 giant] (budget 0 ample.storage) == Some Preparation /\
           exhaustion [RawBase 1 giant] (budget 1 ample.storage) == Some Preparation /\
           exhaustion [RawBase 1 giant] (budget 4097 ample.storage) == Some Preparation /\
           exhaustion [RawBase 1 giant] (budget (giant_units - 1) ample.storage) == Some Preparation /\
           used [RawBase 1 giant] (budget giant_units 102) == Some (giant_units, 102))
  = assert_norm (exhaustion [RawBase 1 giant] (budget 0 ample.storage) == Some Preparation);
    assert_norm (exhaustion [RawBase 1 giant] (budget 1 ample.storage) == Some Preparation);
    assert_norm (exhaustion [RawBase 1 giant] (budget 4097 ample.storage) == Some Preparation);
    assert_norm (exhaustion [RawBase 1 giant] (budget (giant_units - 1) ample.storage) == Some Preparation);
    assert_norm (used [RawBase 1 giant] (budget giant_units 102) == Some (giant_units, 102))
