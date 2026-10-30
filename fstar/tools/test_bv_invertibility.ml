module T = Z3BvTheory
module I = Z3BvInvertibility
module C = Z3BvInvertibilityConditions
module K = Z3BvInvertibilityConcat
module B = Z3.BitVector

let operators =
  [C.Negate; C.Complement; C.Conjoin; C.Disjoin; C.ShiftLeftValue;
   C.ShiftLeftAmount; C.ShiftRightValue; C.ShiftRightAmount;
   C.ArithmeticRightValue; C.ArithmeticRightAmount; C.Add; C.Multiply;
   C.Dividend; C.Divisor; C.RemainderValue; C.RemainderDivisor]

let relations =
  [I.Eq; I.Ne; I.Ult; I.Ugt; I.Ule; I.Uge; I.Slt; I.Sgt; I.Sle; I.Sge]

let native ctx op s x =
  match op with
  | C.Negate -> B.mk_neg ctx x
  | C.Complement -> B.mk_not ctx x
  | C.Conjoin -> B.mk_and ctx x s
  | C.Disjoin -> B.mk_or ctx x s
  | C.ShiftLeftValue -> B.mk_shl ctx x s
  | C.ShiftLeftAmount -> B.mk_shl ctx s x
  | C.ShiftRightValue -> B.mk_lshr ctx x s
  | C.ShiftRightAmount -> B.mk_lshr ctx s x
  | C.ArithmeticRightValue -> B.mk_ashr ctx x s
  | C.ArithmeticRightAmount -> B.mk_ashr ctx s x
  | C.Add -> B.mk_add ctx x s
  | C.Multiply -> B.mk_mul ctx x s
  | C.Dividend -> B.mk_udiv ctx x s
  | C.Divisor -> B.mk_udiv ctx s x
  | C.RemainderValue -> B.mk_urem ctx x s
  | C.RemainderDivisor -> B.mk_urem ctx s x

let value expr =
  Z.of_string (B.numeral_to_string (Z3.Expr.simplify expr None))

let check_operator ctx n op s x =
  let actual = C.apply (Z.of_int n) op s x in
  let expected =
    value (native ctx op (B.mk_numeral ctx (Z.to_string s) n)
      (B.mk_numeral ctx (Z.to_string x) n))
  in
  if not (Z.equal actual expected) then
    failwith (Printf.sprintf "operator mismatch: width=%d s=%s x=%s"
      n (Z.to_string s) (Z.to_string x));
  expected

let signed n v =
  if v >= 1 lsl (n - 1) then v - (1 lsl n) else v

let exhaustive ctx max_width =
  let checked = ref 0 in
  for n = 1 to max_width do
    let size = 1 lsl n in
    let width = Z.of_int n in
    List.iteri (fun op_index op ->
      for s = 0 to size - 1 do
        let parameter = Z.of_int s in
        let reachable = Array.make size false in
        for x = 0 to size - 1 do
          let argument = Z.of_int x in
          let y =
            if n <= 4 then check_operator ctx n op parameter argument
            else C.apply width op parameter argument
          in
          reachable.(Z.to_int y) <- true
        done;
        let count = ref 0 in
        let umin = ref size and umax = ref (-1) in
        let smin = ref size and smax = ref (-size) in
        Array.iteri (fun y present ->
          if present then (
            incr count;
            umin := min !umin y;
            umax := max !umax y;
            smin := min !smin (signed n y);
            smax := max !smax (signed n y)
          )) reachable;
        for t = 0 to size - 1 do
          List.iteri (fun relation_index relation ->
            let expected =
              match relation with
              | I.Eq -> reachable.(t)
              | I.Ne -> !count > 1 || not reachable.(t)
              | I.Ult -> !umin < t
              | I.Ugt -> !umax > t
              | I.Ule -> !umin <= t
              | I.Uge -> !umax >= t
              | I.Slt -> !smin < signed n t
              | I.Sgt -> !smax > signed n t
              | I.Sle -> !smin <= signed n t
              | I.Sge -> !smax >= signed n t
            in
            let actual = C.condition width op relation parameter (Z.of_int t) in
            if actual <> expected then
              failwith (Printf.sprintf
                "condition mismatch: width=%d op=%d relation=%d s=%d t=%d actual=%b expected=%b"
                n op_index relation_index s t actual expected);
            incr checked
          ) relations
        done
      done
    ) operators;
    Printf.printf "All 160 conditions pass exhaustively at width %d\n%!" n
  done;
  !checked

let boundaries ctx =
  List.iter (fun n ->
    let width = Z.of_int n in
    let half = Z.shift_left Z.one (n - 1) in
    let all = Z.pred (Z.shift_left Z.one n) in
    let values =
      [Z.zero; Z.one; Z.pred half; half; all;
       Z.of_int (n - 1); width; Z.of_int (n + 1)]
      |> List.filter (fun v -> Z.geq v Z.zero && Z.leq v all)
      |> List.sort_uniq Z.compare
    in
    List.iter (fun op ->
      List.iter (fun s ->
        List.iter (fun x -> ignore (check_operator ctx n op s x)) values
      ) values
    ) operators;
    List.iter (fun a ->
      List.iter (fun k ->
        let actual = T.bv_sign_extend width (Z.of_int k) a in
        let expected = value (B.mk_sign_ext ctx k
          (B.mk_numeral ctx (Z.to_string a) n)) in
        if not (Z.equal actual expected) then
          failwith (Printf.sprintf "sign extension mismatch: width=%d extension=%d" n k)
      ) [0; 1; n]
    ) values
  ) [1; 2; 17; 32; 64; 65; 257]

let native_concat ctx p s x =
  match p with
  | K.High -> B.mk_concat ctx x s
  | K.Low -> B.mk_concat ctx s x

let word ctx n x = B.mk_numeral ctx (Z.to_string x) n

let check_concat ctx n m p s x =
  let actual = K.apply (Z.of_int n) (Z.of_int m) p s x in
  let expected = value (native_concat ctx p (word ctx m s) (word ctx n x)) in
  if not (Z.equal actual expected) then
    failwith (Printf.sprintf "concatenation mismatch: widths=%d,%d" n m);
  expected

let check_target_parts n m p t tx ts =
  let n = Z.of_int n and m = Z.of_int m in
  if not (Z.equal (K.variable_part n m p t) tx &&
          Z.equal (K.fixed_part n m p t) ts) then
    failwith "concatenation target decomposition mismatch"

let holds n r a b =
  match r with
  | I.Eq -> a = b
  | I.Ne -> a <> b
  | I.Ult -> a < b
  | I.Ugt -> a > b
  | I.Ule -> a <= b
  | I.Uge -> a >= b
  | I.Slt -> signed n a < signed n b
  | I.Sgt -> signed n a > signed n b
  | I.Sle -> signed n a <= signed n b
  | I.Sge -> signed n a >= signed n b

let exhaustive_concat ctx max_width =
  let checked = ref 0 in
  for n = 1 to min 4 max_width do
    for m = 1 to min 4 max_width do
      let wn = Z.of_int n and wm = Z.of_int m in
      List.iteri (fun position p ->
        for s = 0 to (1 lsl m) - 1 do
          let parameter = Z.of_int s in
          let outputs = Array.init (1 lsl n) (fun x ->
            Z.to_int (check_concat ctx n m p parameter (Z.of_int x))) in
          for t = 0 to (1 lsl (n + m)) - 1 do
            let tx, ts =
              match p with
              | K.High -> t lsr m, t land ((1 lsl m) - 1)
              | K.Low -> t land ((1 lsl n) - 1), t lsr n
            in
            let target = Z.of_int t in
            let tx = Z.of_int tx and ts = Z.of_int ts in
            check_target_parts n m p target tx ts;
            List.iteri (fun relation r ->
              let expected = Array.exists (fun y -> holds (n + m) r y t) outputs in
              let actual = K.condition wn wm p r parameter tx ts in
              let witness = K.witness wn p r tx in
              let attained = holds (n + m) r outputs.(Z.to_int witness) t in
              if actual <> expected || actual <> attained ||
                 actual <> K.condition_value wn wm p r parameter target then
                failwith (Printf.sprintf
                  "concat condition mismatch: widths=%d,%d position=%d relation=%d s=%d t=%d"
                  n m position relation s t);
              incr checked
            ) relations
          done
        done
      ) [K.High; K.Low]
    done
  done;
  Printf.printf "%d exhaustive mixed-width condition and witness instances passed\n%!"
    !checked

let native_holds ctx r a b =
  let predicate =
    match r with
    | I.Eq -> Z3.Boolean.mk_eq ctx a b
    | I.Ne -> Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx a b)
    | I.Ult -> B.mk_ult ctx a b
    | I.Ugt -> B.mk_ugt ctx a b
    | I.Ule -> B.mk_ule ctx a b
    | I.Uge -> B.mk_uge ctx a b
    | I.Slt -> B.mk_slt ctx a b
    | I.Sgt -> B.mk_sgt ctx a b
    | I.Sle -> B.mk_sle ctx a b
    | I.Sge -> B.mk_sge ctx a b
  in
  Z3.Boolean.is_true (Z3.Expr.simplify predicate None)

let concat_boundaries ctx =
  let values n =
    let half = Z.shift_left Z.one (n - 1) in
    [Z.zero; Z.one; Z.pred half; half; Z.pred (Z.shift_left Z.one n)]
    |> List.sort_uniq Z.compare
  in
  List.iter (fun (n, m) ->
    let wn = Z.of_int n and wm = Z.of_int m in
    List.iter (fun p ->
      List.iter (fun s ->
        List.iter (fun tx ->
          ignore (check_concat ctx n m p s tx);
          List.iter (fun ts ->
            let target = native_concat ctx p (word ctx m ts) (word ctx n tx) in
            let t = value target in
            check_target_parts n m p t tx ts;
            List.iter (fun r ->
              let x = K.witness wn p r tx in
              let result = native_concat ctx p (word ctx m s) (word ctx n x) in
              let actual = K.condition wn wm p r s tx ts in
              if actual <> native_holds ctx r result target ||
                 actual <> K.condition_value wn wm p r s t then
                failwith (Printf.sprintf
                  "native concat condition/witness mismatch: widths=%d,%d" n m)
            ) relations
          ) (values m)
        ) (values n)
      ) (values m)
    ) [K.High; K.Low]
  ) [1, 1; 1, 65; 65, 1; 17, 32; 32, 17; 64, 65; 65, 64;
     1, 257; 257, 1; 257, 257];
  Printf.printf "Mixed-width native Z3 boundary and signed-order checks passed\n%!"

let () =
  let max_width = if Array.length Sys.argv = 2 then int_of_string Sys.argv.(1) else 8 in
  if max_width < 1 || max_width > 8 then invalid_arg "width must be between 1 and 8";
  Printf.printf "Native Z3 oracle: %s\n%!" Z3.Version.full_version;
  let ctx = Z3.mk_context [] in
  boundaries ctx;
  concat_boundaries ctx;
  exhaustive_concat ctx max_width;
  let checked = exhaustive ctx max_width in
  Printf.printf "%d exhaustive condition instances passed; native Z3 semantic checks passed\n%!"
    checked
