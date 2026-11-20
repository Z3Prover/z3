module MaxSmtNegBounds
(* Model of maxsmt::get_lower/get_upper (raw m_lower/m_upper, then
   m_c.adjust = adjust_value::operator()(rational)) and of
   context::get_lower_value/get_upper_value for O_MAXSMT, base vs PR head.
   Integers model rationals; infinities/epsilons are not modelled. *)

let adjust (off:int) (neg:bool) (x:int) : int = (if neg then 0 - x else x) + off

(* maxsmt::get_lower / get_upper : adjusted raw bounds *)
let ms_lower (lo off:int) (neg:bool) = adjust off neg lo
let ms_upper (hi off:int) (neg:bool) = adjust off neg hi

(* base *)
let base_lower (lo hi off:int) (neg:bool) = ms_lower lo off neg
let base_upper (lo hi off:int) (neg:bool) = ms_upper hi off neg

(* PR head *)
let pr_lower (lo hi off:int) (neg:bool) = if neg then ms_upper hi off neg else ms_lower lo off neg
let pr_upper (lo hi off:int) (neg:bool) = if neg then ms_lower lo off neg else ms_upper hi off neg

(* Obligation 1: interval well-formed *)
let ob1 (lo hi off:int) (neg:bool)
  : Lemma (requires lo <= hi) (ensures pr_lower lo hi off neg <= pr_upper lo hi off neg) = ()

(* Obligation 2: encloses adjusted value of every raw value in [lo,hi] *)
let ob2 (lo hi v off:int) (neg:bool)
  : Lemma (requires lo <= v /\ v <= hi)
          (ensures pr_lower lo hi off neg <= adjust off neg v /\ adjust off neg v <= pr_upper lo hi off neg) = ()

(* Obligation 3: non-negated behaviour unchanged *)
let ob3 (lo hi off:int)
  : Lemma (pr_lower lo hi off false == base_lower lo hi off false /\
           pr_upper lo hi off false == base_upper lo hi off false) = ()

(* Counterexample for base: concrete witness lo=0,hi=1,off=0,neg=true *)
let base_cex ()
  : Lemma (0 <= 1 /\ base_lower 0 1 0 true > base_upper 0 1 0 true
           /\ pr_lower 0 1 0 true <= pr_upper 0 1 0 true) = ()
