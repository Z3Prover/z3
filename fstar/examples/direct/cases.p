% Native direct proof; the last input assertion is discharged, not an axiom.
cnf(a0,axiom,((p) | (q))).
cnf(a1,axiom,(~(p) | (r))).
cnf(a2,axiom,(~(q) | (r))).
cnf(p5,plain,(~(r) | (r)),inference(tautology,[status(thm)],[])).
cnf(p23,plain,((r)),inference(forward_rewriting,[status(thm)],[a0,a1,a2])).
cnf(goal_1,theorem,((r)),inference(reiteration,[status(thm)],[p23])).
