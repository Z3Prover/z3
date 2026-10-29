module Z3BvInvertibilityConditions

open Z3BvTheory
module U = FStar.UInt
module I = Z3BvInvertibility

(* Same-width inventory from the CAV/LPAR artifacts; see BV_INVERTIBILITY.md. *)
type operator =
  | Negate | Complement | Conjoin | Disjoin | ShiftLeftValue | ShiftLeftAmount | ShiftRightValue | ShiftRightAmount | ArithmeticRightValue | ArithmeticRightAmount | Add | Multiply | Dividend | Divisor | RemainderValue | RemainderDivisor

let signed_min (n:pos) : bv n = U.pow2_n #n (n - 1)
let signed_max (n:pos) : bv n = signed_min n - 1

let apply (#n:pos) (op:operator) (s x:bv n) : bv n =
  match op with
  | Negate -> bvneg x
  | Complement -> bvnot x
  | Conjoin -> bvand x s
  | Disjoin -> bvor x s
  | ShiftLeftValue -> bvshl x s
  | ShiftLeftAmount -> bvshl s x
  | ShiftRightValue -> bvlshr x s
  | ShiftRightAmount -> bvlshr s x
  | ArithmeticRightValue -> bvashr x s
  | ArithmeticRightAmount -> bvashr s x
  | Add -> bvadd x s
  | Multiply -> bvmul x s
  | Dividend -> bvudiv x s
  | Divisor -> bvudiv s x
  | RemainderValue -> bvurem x s
  | RemainderDivisor -> bvurem s x

let rec shift_disjunction (#n:pos) (op:operator) (r:I.relation)
  (s t:bv n) (i:nat) : Tot bool (decreases i) =
  I.holds r (apply op s (bv_of_int #n i)) t ||
  (if i = 0 then false else shift_disjunction op r s t (i - 1))

let condition_bvneg (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> true
  | I.Ne -> true
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (t <> (bvnot (bv_of_int #n 0)))
  | I.Ule -> true
  | I.Uge -> true
  | I.Slt -> (t <> (signed_min n))
  | I.Sgt -> (t <> (signed_max n))
  | I.Sle -> true
  | I.Sge -> true

let condition_bvnot (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> true
  | I.Ne -> true
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (t <> (bvnot (bv_of_int #n 0)))
  | I.Ule -> true
  | I.Uge -> true
  | I.Slt -> (t <> (signed_min n))
  | I.Sgt -> (t <> (signed_max n))
  | I.Sle -> true
  | I.Sge -> true

let condition_bvand (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvand t s) = t)
  | I.Ne -> ((s <> (bv_of_int #n 0)) || (t <> (bv_of_int #n 0)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t s)
  | I.Ule -> true
  | I.Uge -> (not (I.holds I.Ult s t))
  | I.Slt -> (I.holds I.Slt (bvand (bvnot (bvneg t)) s) t)
  | I.Sgt -> (I.holds I.Slt t (bvand s (signed_max n)))
  | I.Sle -> (I.holds I.Uge s (bvand t (signed_min n)))
  | I.Sge -> (((bvand s t) = t) || (I.holds I.Slt t (bvand (bvsub t s) s)))

let condition_bvor (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvor t s) = t)
  | I.Ne -> ((s <> (bvnot (bv_of_int #n 0))) || (t <> (bvnot (bv_of_int #n 0))))
  | I.Ult -> (I.holds I.Ult s t)
  | I.Ugt -> (I.holds I.Ult t (bvnot (bv_of_int #n 0)))
  | I.Ule -> (I.holds I.Uge t s)
  | I.Uge -> true
  | I.Slt -> (I.holds I.Slt (bvor (bvnot (bvsub s t)) s) t)
  | I.Sgt -> (I.holds I.Slt t (bvor s (signed_max n)))
  | I.Sle -> (I.holds I.Sge t (bvor s (signed_min n)))
  | I.Sge -> (not (I.holds I.Slt s (bvand s t)))

let condition_bvshl0 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvshl (bvlshr t s) s) = t)
  | I.Ne -> ((t <> (bv_of_int #n 0)) || (I.holds I.Ult s (bv_of_int #n n)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t (bvshl (bvnot (bv_of_int #n 0)) s))
  | I.Ule -> true
  | I.Uge -> (I.holds I.Uge (bvshl (bvnot (bv_of_int #n 0)) s) t)
  | I.Slt -> (I.holds I.Slt (bvshl (bvlshr (signed_min n) s) s) t)
  | I.Sgt -> (I.holds I.Slt t (bvand (bvshl (signed_max n) s) (signed_max n)))
  | I.Sle -> (I.holds I.Ult (bvlshr t (bvlshr t s)) (signed_min n))
  | I.Sge -> (I.holds I.Sge (bvand (bvshl (signed_max n) s) (signed_max n)) t)

let condition_bvshl1 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> shift_disjunction ShiftLeftAmount I.Eq s t n
  | I.Ne -> ((s <> (bv_of_int #n 0)) || (t <> (bv_of_int #n 0)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> shift_disjunction ShiftLeftAmount I.Ugt s t n
  | I.Ule -> true
  | I.Uge -> shift_disjunction ShiftLeftAmount I.Uge s t n
  | I.Slt -> (I.holds I.Ult (bvshl (signed_min n) s) (bvadd t (signed_min n)))
  | I.Sgt -> shift_disjunction ShiftLeftAmount I.Sgt s t n
  | I.Sle -> (I.holds I.Ult (bvlshr t s) (signed_min n))
  | I.Sge -> shift_disjunction ShiftLeftAmount I.Sge s t n

let condition_bvlshr0 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvlshr (bvshl t s) s) = t)
  | I.Ne -> ((t <> (bv_of_int #n 0)) || (I.holds I.Ult s (bv_of_int #n n)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t (bvlshr (bvnot s) s))
  | I.Ule -> true
  | I.Uge -> ((bvlshr (bvshl t s) s) = t)
  | I.Slt -> (I.holds I.Slt (bvlshr (bvnot (bvneg t)) s) t)
  | I.Sgt -> (I.holds I.Slt t (bvlshr (bvshl (signed_max n) s) s))
  | I.Sle -> (I.holds I.Sge t (bvlshr t s))
  | I.Sge -> ((not (not (s = (bv_of_int #n 0)))) || (I.holds I.Sge (bvlshr (bvnot (bv_of_int #n 0)) s) t))

let condition_bvlshr1 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> shift_disjunction ShiftRightAmount I.Eq s t n
  | I.Ne -> ((s <> (bv_of_int #n 0)) || (t <> (bv_of_int #n 0)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t s)
  | I.Ule -> true
  | I.Uge -> (I.holds I.Uge s t)
  | I.Slt -> ((I.holds I.Slt s t) || (I.holds I.Slt (bv_of_int #n 0) t))
  | I.Sgt -> (((not (I.holds I.Slt s (bv_of_int #n 0))) || (I.holds I.Sgt (bvlshr s (bv_of_int #n 1)) t)) && ((not (I.holds I.Sge s (bv_of_int #n 0))) || (I.holds I.Sgt s t)))
  | I.Sle -> ((I.holds I.Ult t (signed_min n)) || (I.holds I.Sge t s))
  | I.Sge -> (((not (I.holds I.Slt s (bv_of_int #n 0))) || (I.holds I.Sge (bvlshr s (bv_of_int #n 1)) t)) && ((not (I.holds I.Sge s (bv_of_int #n 0))) || (I.holds I.Sge s t)))

let condition_bvashr0 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> (((not (I.holds I.Ult s (bv_of_int #n n))) || ((bvashr (bvshl t s) s) = t)) && ((not (I.holds I.Uge s (bv_of_int #n n))) || ((t = (bvnot (bv_of_int #n 0))) || (t = (bv_of_int #n 0)))))
  | I.Ne -> true
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t (bvnot (bv_of_int #n 0)))
  | I.Ule -> true
  | I.Uge -> true
  | I.Slt -> (I.holds I.Slt (bvashr (signed_min n) s) t)
  | I.Sgt -> (I.holds I.Slt t (bvlshr (signed_max n) s))
  | I.Sle -> (I.holds I.Sge t (bvnot (bvlshr (signed_max n) s)))
  | I.Sge -> (I.holds I.Sge (bvlshr (signed_max n) s) t)

let condition_bvashr1 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> shift_disjunction ArithmeticRightAmount I.Eq s t n
  | I.Ne -> (((not (t = (bv_of_int #n 0))) || (not (s = (bv_of_int #n 0)))) && ((not (t = (bvnot (bv_of_int #n 0)))) || (not (s = (bvnot (bv_of_int #n 0))))))
  | I.Ult -> ((not ((not (I.holds I.Ult s t)) && (I.holds I.Slt s (bv_of_int #n 0)))) && (not (t = (bv_of_int #n 0))))
  | I.Ugt -> ((I.holds I.Slt s (bvlshr s (bvnot t))) || (I.holds I.Ult t s))
  | I.Ule -> ((I.holds I.Ult s (signed_min n)) || (I.holds I.Uge t s))
  | I.Uge -> (not ((I.holds I.Ult s (bvnot s)) && (I.holds I.Ult s t)))
  | I.Slt -> ((I.holds I.Slt s t) || (I.holds I.Slt (bv_of_int #n 0) t))
  | I.Sgt -> ((I.holds I.Slt t (bvand s (signed_max n))) && (I.holds I.Slt t (bvor s (signed_max n))))
  | I.Sle -> ((I.holds I.Sge t (bv_of_int #n 0)) || (I.holds I.Sge t s))
  | I.Sge -> (not ((I.holds I.Ult t (bvnot t)) && (I.holds I.Slt s t)))

let condition_bvadd (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> true
  | I.Ne -> true
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (t <> (bvnot (bv_of_int #n 0)))
  | I.Ule -> true
  | I.Uge -> true
  | I.Slt -> (t <> (signed_min n))
  | I.Sgt -> (t <> (signed_max n))
  | I.Sle -> true
  | I.Sge -> true

let condition_bvmul (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvand (bvor (bvneg s) s) t) = t)
  | I.Ne -> ((t <> (bv_of_int #n 0)) || (s <> (bv_of_int #n 0)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t (bvor (bvneg s) s))
  | I.Ule -> true
  | I.Uge -> (not (I.holds I.Ult (bvor (bvneg s) s) t))
  | I.Slt -> (I.holds I.Slt (bvand (bvnot (bvneg t)) (bvor (bvneg s) s)) t)
  | I.Sgt -> (I.holds I.Slt t (bvsub t (bvor (bvor s t) (bvneg s))))
  | I.Sle -> (not ((s = (bv_of_int #n 0)) && (I.holds I.Slt t s)))
  | I.Sge -> (I.holds I.Sge (bvand (bvor (bvneg s) s) (signed_max n)) t)

let condition_bvudiv0 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvudiv (bvmul s t) s) = t)
  | I.Ne -> ((s <> (bv_of_int #n 0)) || (t <> (bvnot (bv_of_int #n 0))))
  | I.Ult -> ((I.holds I.Ult (bv_of_int #n 0) s) && (I.holds I.Ult (bv_of_int #n 0) t))
  | I.Ugt -> (I.holds I.Ugt (bvudiv (bvnot (bv_of_int #n 0)) s) t)
  | I.Ule -> (not (I.holds I.Ult (bvor s t) (bvnot (bvneg s))))
  | I.Uge -> ((bvand (bvudiv (bvmul s t) t) s) = s)
  | I.Slt -> ((not (I.holds I.Sle t (bv_of_int #n 0))) || (I.holds I.Slt (bvudiv (signed_min n) s) t))
  | I.Sgt -> ((I.holds I.Sgt (bvudiv (bvnot (bv_of_int #n 0)) s) t) || (I.holds I.Sgt (bvudiv (signed_max n) s) t))
  | I.Sle -> (((bvudiv (bvmul s t) s) = t) || ((not (I.holds I.Sle t (bv_of_int #n 0))) || (I.holds I.Slt (bvudiv (signed_min n) s) t)))
  | I.Sge -> ((I.holds I.Sge (bvudiv (bvnot (bv_of_int #n 0)) s) t) || (I.holds I.Sge (bvudiv (signed_max n) s) t))

let condition_bvudiv1 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> ((bvudiv s (bvudiv s t)) = t)
  | I.Ne -> (if n = 1 then bvand s t = 0 else true)
  | I.Ult -> ((I.holds I.Ult (bv_of_int #n 0) (bvnot (bvand (bvneg t) s))) && (I.holds I.Ult (bv_of_int #n 0) t))
  | I.Ugt -> (I.holds I.Ult t (bvnot (bv_of_int #n 0)))
  | I.Ule -> (I.holds I.Ult (bv_of_int #n 0) (bvor (bvnot s) t))
  | I.Uge -> true
  | I.Slt -> ((I.holds I.Slt s t) || (I.holds I.Sge t (bv_of_int #n 0)))
  | I.Sgt -> (if n = 1 then I.holds I.Sgt s t else (((not (I.holds I.Sge s (bv_of_int #n 0))) || (I.holds I.Sgt s t)) && ((not (I.holds I.Slt s (bv_of_int #n 0))) || (I.holds I.Sgt (bvlshr s (bv_of_int #n 1)) t))))
  | I.Sle -> ((I.holds I.Sge t (bvnot (bv_of_int #n 0))) || (I.holds I.Sge t s))
  | I.Sge -> (if n = 1 then I.holds I.Sge s t else (((not (I.holds I.Sge s (bv_of_int #n 0))) || (I.holds I.Sge s t)) && ((not (I.holds I.Slt s (bv_of_int #n 0))) || (I.holds I.Sge (bvlshr s (bv_of_int #n 1)) t))))

let condition_bvurem0 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> (not (I.holds I.Ult (bvnot (bvneg s)) t))
  | I.Ne -> ((s <> (bv_of_int #n 1)) || (t <> (bv_of_int #n 0)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t (bvnot (bvneg s)))
  | I.Ule -> true
  | I.Uge -> (I.holds I.Uge (bvnot (bvneg s)) t)
  | I.Slt -> (I.holds I.Slt (bvnot t) (bvor (bvneg s) (bvneg t)))
  | I.Sgt -> ((((not (I.holds I.Sgt s (bv_of_int #n 0))) || (I.holds I.Slt t (bvnot (bvneg s)))) && ((not (I.holds I.Sle s (bv_of_int #n 0))) || (t <> (signed_max n)))) && ((t <> (bv_of_int #n 0)) || (s <> (bv_of_int #n 1))))
  | I.Sle -> (I.holds I.Slt (bvnot (bv_of_int #n 0)) (bvand (bvneg s) t))
  | I.Sge -> ((I.holds I.Slt t s) || (I.holds I.Sge (bv_of_int #n 0) s))

let condition_bvurem1 (#n:pos) (r:I.relation) (s t:bv n) : bool =
  match r with
  | I.Eq -> (I.holds I.Uge (bvand (bvsub (bvadd t t) s) s) t)
  | I.Ne -> ((s <> (bv_of_int #n 0)) || (t <> (bv_of_int #n 0)))
  | I.Ult -> (t <> (bv_of_int #n 0))
  | I.Ugt -> (I.holds I.Ult t s)
  | I.Ule -> true
  | I.Uge -> ((I.holds I.Uge (bvand (bvsub (bvadd t t) s) s) t) || (I.holds I.Ult t s))
  | I.Slt -> ((I.holds I.Slt s t) || (I.holds I.Slt (bv_of_int #n 0) t))
  | I.Sgt -> (((not (I.holds I.Sge s (bv_of_int #n 0))) || (I.holds I.Sgt s t)) && ((not (I.holds I.Slt s (bv_of_int #n 0))) || (I.holds I.Sgt (bvlshr (bvsub s (bv_of_int #n 1)) (bv_of_int #n 1)) t)))
  | I.Sle -> ((I.holds I.Ult t (signed_min n)) || (I.holds I.Sge t s))
  | I.Sge -> (((not (I.holds I.Sge s (bv_of_int #n 0))) || (I.holds I.Sge s t)) && ((not ((I.holds I.Slt s (bv_of_int #n 0)) && (I.holds I.Sge t (bv_of_int #n 0)))) || (I.holds I.Ugt (bvsub s t) t)))

let condition (#n:pos) (op:operator) (r:I.relation) (s t:bv n) : bool =
  match op with
  | Negate -> condition_bvneg r s t
  | Complement -> condition_bvnot r s t
  | Conjoin -> condition_bvand r s t
  | Disjoin -> condition_bvor r s t
  | ShiftLeftValue -> condition_bvshl0 r s t
  | ShiftLeftAmount -> condition_bvshl1 r s t
  | ShiftRightValue -> condition_bvlshr0 r s t
  | ShiftRightAmount -> condition_bvlshr1 r s t
  | ArithmeticRightValue -> condition_bvashr0 r s t
  | ArithmeticRightAmount -> condition_bvashr1 r s t
  | Add -> condition_bvadd r s t
  | Multiply -> condition_bvmul r s t
  | Dividend -> condition_bvudiv0 r s t
  | Divisor -> condition_bvudiv1 r s t
  | RemainderValue -> condition_bvurem0 r s t
  | RemainderDivisor -> condition_bvurem1 r s t
