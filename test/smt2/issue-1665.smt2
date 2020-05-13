; Copyright (c) 2018 Microsoft Corporation
; GitHub issue

(declare-sort sko_ty_0_1793)
(declare-fun s1_1796 () (Array sko_ty_0_1793 Bool))
(declare-fun s2_1797 () (Array sko_ty_0_1793 Bool))
(declare-fun x_1795 () sko_ty_0_1793)
(assert (not (default s1_1796)))
(assert (not (default s2_1797)))
(assert (select ((_ map (and (Bool Bool) Bool))
          s1_1796
          ((_ map (not (Bool) Bool)) s2_1797))
        x_1795))
(assert (not (select s1_1796 x_1795)))
(check-sat)
(reset)

(declare-fun s1_1796 () (Array Int Bool))
(declare-fun s2_1797 () (Array Int Bool))
(declare-fun x_1795 () Int)
(assert (not (default s1_1796)))
(assert (not (default s2_1797)))
(assert (select ((_ map (and (Bool Bool) Bool))
          s1_1796
          ((_ map (not (Bool) Bool)) s2_1797))
        x_1795))
(assert (not (select s1_1796 x_1795)))
(check-sat)
(reset)

(declare-fun s1_1796 () (Array Int Bool))
(declare-fun s2_1797 () (Array Int Bool))
(declare-fun x_1795 () Int)
(assert (not (default s1_1796)))
(assert (not (default s2_1797)))
(assert (select ((_ map (and (Bool Bool) Bool))
          s1_1796
          ((_ map (not (Bool) Bool)) s2_1797))
        x_1795))
(assert (not (select s1_1796 x_1795)))
(check-sat)
