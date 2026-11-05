(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_copy.spl:29:4-20:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun Axiom_20$0 () Bool)
(declare-fun Axiom_21$0 () Bool)
(declare-fun Axiom_22$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_2$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun b_2$0 () Loc)
(declare-fun b_init$0 () Loc)
(declare-fun c_3$0 () Loc)
(declare-fun c_init$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun d_3$0 () Loc)
(declare-fun d_4$0 () Loc)
(declare-fun d_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_5$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun old_d_2$0 () Loc)
(declare-fun old_d_4$0 () Loc)
(declare-fun old_d_init$0 () Loc)
(declare-fun prev$0 () FldLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun tmp_2$0 () Loc)
(declare-fun tmp_3$0 () Loc)
(declare-fun tmp_init$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y)
            (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 tmp_3$0 ?y ?y)) (= tmp_3$0 ?y)
            (Btwn$0 next$0 tmp_3$0 (read$0 next$0 tmp_3$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_d_4$0 ?y ?y)) (= old_d_4$0 ?y)
            (Btwn$0 next$0 old_d_4$0 (read$0 next$0 old_d_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y)
            (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 b_init$0) b_init$0))
            (not (Btwn$0 next$0 b_init$0 ?y ?y)) (= b_init$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 tmp_3$0) tmp_3$0))
            (not (Btwn$0 next$0 tmp_3$0 ?y ?y)) (= tmp_3$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_d_4$0) old_d_4$0))
            (not (Btwn$0 next$0 old_d_4$0 ?y ?y)) (= old_d_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 old_curr_4$0) old_curr_4$0))
            (not (Btwn$0 next$0 old_curr_4$0 ?y ?y)) (= old_curr_4$0 ?y))))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next$0 b_init$0 (read$0 next$0 b_init$0) (read$0 next$0 b_init$0)))

(assert (Btwn$0 next$0 tmp_3$0 (read$0 next$0 tmp_3$0) (read$0 next$0 tmp_3$0)))

(assert (Btwn$0 next$0 old_d_4$0 (read$0 next$0 old_d_4$0) (read$0 next$0 old_d_4$0)))

(assert (Btwn$0 next$0 old_curr_4$0 (read$0 next$0 old_curr_4$0)
  (read$0 next$0 old_curr_4$0)))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) null$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0)) (not (in$0 null$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_28$0))
        (not (in$0 a_2$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) a_2$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0)) (not (in$0 a_2$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_28$0))
        (not (in$0 c_3$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) c_3$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0)) (not (in$0 c_3$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_28$0)) (not (in$0 curr_init$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_28$0)) (not (in$0 curr_init$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) curr_init$0))
        (not (in$0 tmp_3$0 sk_?X_28$0)) (not (in$0 curr_init$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_28$0))
        (not (in$0 curr_init$0 sk_?X_28$0)))))

(assert (or (not Axiom_22$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_28$0))
        (not (in$0 curr_init$0 sk_?X_28$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) null$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0)) (not (in$0 null$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_29$0))
        (not (in$0 a_2$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) a_2$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0)) (not (in$0 a_2$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_29$0))
        (not (in$0 c_3$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) c_3$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0)) (not (in$0 c_3$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_29$0)) (not (in$0 curr_init$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_29$0)) (not (in$0 curr_init$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) curr_init$0))
        (not (in$0 tmp_3$0 sk_?X_29$0)) (not (in$0 curr_init$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_29$0))
        (not (in$0 curr_init$0 sk_?X_29$0)))))

(assert (or (not Axiom_20$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_29$0))
        (not (in$0 curr_init$0 sk_?X_29$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) null$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) null$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) null$0))
        (not (in$0 old_d_4$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 null$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) null$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0)) (not (in$0 null$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) null$0)
        (not (= (read$0 next$0 null$0) a_2$0)) (not (in$0 null$0 sk_?X_26$0))
        (not (in$0 a_2$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) a_2$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) a_2$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) a_2$0))
        (not (in$0 old_d_4$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 a_2$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) a_2$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0)) (not (in$0 a_2$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) null$0)
        (not (= (read$0 next$0 null$0) c_3$0)) (not (in$0 null$0 sk_?X_26$0))
        (not (in$0 c_3$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) c_3$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) c_3$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) c_3$0))
        (not (in$0 old_d_4$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 c_3$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) c_3$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0)) (not (in$0 c_3$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_26$0)) (not (in$0 curr_init$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) b_init$0)
        (not (= (read$0 next$0 b_init$0) curr_init$0))
        (not (in$0 b_init$0 sk_?X_26$0)) (not (in$0 curr_init$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) tmp_3$0)
        (not (= (read$0 next$0 tmp_3$0) curr_init$0))
        (not (in$0 tmp_3$0 sk_?X_26$0)) (not (in$0 curr_init$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) old_d_4$0)
        (not (= (read$0 next$0 old_d_4$0) curr_init$0))
        (not (in$0 old_d_4$0 sk_?X_26$0))
        (not (in$0 curr_init$0 sk_?X_26$0)))))

(assert (or (not Axiom_21$0)
    (or (= (read$0 prev$0 curr_init$0) old_curr_4$0)
        (not (= (read$0 next$0 old_curr_4$0) curr_init$0))
        (not (in$0 old_curr_4$0 sk_?X_26$0))
        (not (in$0 curr_init$0 sk_?X_26$0)))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 Alloc$0 (setenum$0 tmp_3$0)))
                 (or (in$0 x Alloc$0) (in$0 x (setenum$0 tmp_3$0))))
            (and (not (in$0 x Alloc$0)) (not (in$0 x (setenum$0 tmp_3$0)))
                 (not (in$0 x (union$0 Alloc$0 (setenum$0 tmp_3$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_27$0 sk_?X_26$0))
                 (or (in$0 x sk_?X_27$0) (in$0 x sk_?X_26$0)))
            (and (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_26$0))
                 (not (in$0 x (union$0 sk_?X_27$0 sk_?X_26$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 (setenum$0 tmp_3$0)))
                 (or (in$0 x FP$0) (in$0 x (setenum$0 tmp_3$0))))
            (and (not (in$0 x FP$0)) (not (in$0 x (setenum$0 tmp_3$0)))
                 (not (in$0 x (union$0 FP$0 (setenum$0 tmp_3$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_29$0 sk_?X_28$0))
                 (or (in$0 x sk_?X_29$0) (in$0 x sk_?X_28$0)))
            (and (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_28$0))
                 (not (in$0 x (union$0 sk_?X_29$0 sk_?X_28$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_29$0) (in$0 x sk_?X_28$0)
                 (in$0 x (intersection$0 sk_?X_29$0 sk_?X_28$0)))
            (and (or (not (in$0 x sk_?X_29$0)) (not (in$0 x sk_?X_28$0)))
                 (not (in$0 x (intersection$0 sk_?X_29$0 sk_?X_28$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_27$0) (in$0 x sk_?X_26$0)
                 (in$0 x (intersection$0 sk_?X_27$0 sk_?X_26$0)))
            (and (or (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_26$0)))
                 (not (in$0 x (intersection$0 sk_?X_27$0 sk_?X_26$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 (write$0 next$0 tmp_3$0 null$0) tmp_3$0) null$0))

(assert (or (= null$0 tmp_3$0)
    (= (read$0 next$0 null$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) null$0))))

(assert (or (= b_init$0 tmp_3$0)
    (= (read$0 next$0 b_init$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) b_init$0))))

(assert (or (= tmp_3$0 tmp_3$0)
    (= (read$0 next$0 tmp_3$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) tmp_3$0))))

(assert (or (= old_d_4$0 tmp_3$0)
    (= (read$0 next$0 old_d_4$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) old_d_4$0))))

(assert (or (= old_curr_4$0 tmp_3$0)
    (= (read$0 next$0 old_curr_4$0)
      (read$0 (write$0 next$0 tmp_3$0 null$0) old_curr_4$0))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_2$0 null$0) null$0))

(assert (= (read$0 prev$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or
    (and (Btwn$0 next$0 a_init$0 curr_init$0 curr_init$0)
         (or (and (= null$0 old_curr_init$0) (= a_init$0 curr_init$0))
             (and (= (read$0 next$0 old_curr_init$0) curr_init$0)
                  (= (read$0 prev$0 a_init$0) null$0)
                  (in$0 old_curr_init$0 sk_?X_29$0)))
         Axiom_20$0)
    (not
         (dlseg_struct$0 sk_?X_29$0 next$0 prev$0 a_init$0 null$0 curr_init$0
           old_curr_init$0))))

(assert (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) old_curr_init$0)
                  (in$0 b_init$0 sk_?X_28$0))
             (and (= curr_init$0 null$0) (= old_curr_init$0 b_init$0)))
         Axiom_22$0)
    (not
         (dlseg_struct$0 sk_?X_28$0 next$0 prev$0 curr_init$0 old_curr_init$0
           null$0 b_init$0))))

(assert (= FP_3$0 (union$0 FP$0 (setenum$0 tmp_3$0))))

(assert (= a_2$0 a_init$0))

(assert (= c_3$0 c_init$0))

(assert (= d_3$0 d_init$0))

(assert (= next_2$0 (write$0 next$0 d_4$0 null$0)))

(assert (= old_curr_5$0 curr_4$0))

(assert (= old_d_4$0 d_3$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_29$0 sk_?X_28$0)))

(assert (= sk_?X_25$0 FP$0))

(assert (= sk_?X_27$0 (union$0 sk_?X_29$0 sk_?X_28$0)))

(assert (= sk_?X_29$0
  (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0 old_curr_init$0)))

(assert (dlseg_struct$0 sk_?X_26$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0))

(assert (dlseg_struct$0 sk_?X_29$0 next$0 prev$0 a_init$0 null$0 curr_init$0
  old_curr_init$0))

(assert (not (= tmp_3$0 null$0)))

(assert (not (in$0 d_4$0 FP_3$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_init$0 l1 curr_init$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0
                     old_curr_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 a_init$0 l1 curr_init$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a_init$0 null$0
                          curr_init$0 old_curr_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0
                     null$0 b_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0
                          old_curr_init$0 null$0 b_init$0)))))))

(assert (or
    (and (Btwn$0 next$0 c_init$0 null$0 null$0)
         (or (and (= null$0 d_init$0) (= c_init$0 null$0))
             (and (= (read$0 next$0 d_init$0) null$0)
                  (= (read$0 prev$0 c_init$0) null$0)
                  (in$0 d_init$0 sk_?X_26$0)))
         Axiom_21$0)
    (not
         (dlseg_struct$0 sk_?X_26$0 next$0 prev$0 c_init$0 null$0 null$0
           d_init$0))))

(assert (= Alloc_2$0 (union$0 Alloc$0 (setenum$0 tmp_3$0))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= b_2$0 b_init$0))

(assert (= curr_4$0 curr_init$0))

(assert (= d_4$0 tmp_3$0))

(assert (= old_curr_4$0 old_curr_init$0))

(assert (= old_d_2$0 old_d_init$0))

(assert (= tmp_2$0 tmp_init$0))

(assert (= emptyset$0 (intersection$0 sk_?X_27$0 sk_?X_26$0)))

(assert (= sk_?X_25$0 (union$0 sk_?X_27$0 sk_?X_26$0)))

(assert (= sk_?X_26$0 (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0)))

(assert (= sk_?X_28$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0 b_init$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (dlseg_struct$0 sk_?X_28$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0
  b_init$0))

(assert (not (= curr_4$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 tmp_3$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0
                     d_init$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 c_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0
                          d_init$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 d_4$0 null$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v d_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not (Btwn$0 next$0 ?z d_4$0 d_4$0)))))
                          (and (not (= d_4$0 ?v))
                               (or (Btwn$0 next$0 ?z d_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u d_4$0)
                               (or (Btwn$0 next$0 null$0 ?v d_4$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 d_4$0
                                               d_4$0)))))
                          (and (not (= d_4$0 ?v))
                               (or (Btwn$0 next$0 ?z d_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 null$0 ?u ?v)
                               (or (Btwn$0 next$0 null$0 ?v d_4$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 d_4$0
                                               d_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v d_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z d_4$0 d_4$0)))))
                 (and (not (= d_4$0 ?v))
                      (or (Btwn$0 next$0 ?z d_4$0 ?v)
                          (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u d_4$0)
                      (or (Btwn$0 next$0 null$0 ?v d_4$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 d_4$0 d_4$0)))))
                 (and (not (= d_4$0 ?v))
                      (or (Btwn$0 next$0 ?z d_4$0 ?v)
                          (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 null$0 ?u ?v)
                      (or (Btwn$0 next$0 null$0 ?v d_4$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 d_4$0 d_4$0)))))
                 (not (Btwn$0 (write$0 next$0 d_4$0 null$0) ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
