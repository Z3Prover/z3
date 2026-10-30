% Native direct proof; the last input assertion is discharged, not an axiom.
cnf(a0,axiom,((p) | (q))).
cnf(a1,axiom,(~(p) | (q) | (r))).
cnf(a2,axiom,((p) | ~(q) | (r))).
cnf(a3,axiom,(~(p) | ~(q) | (r))).
cnf(p5,plain,(~(r) | (r)),inference(tautology,[status(thm)],[])).
cnf(p28,plain,(~(p) | (p)),inference(tautology,[status(thm)],[])).
cnf(p29_r0,plain,((q) | (p)),inference(resolution,[status(thm)],[a0,p28])).
cnf(p30_r0,plain,((p) | (r)),inference(resolution,[status(thm)],[a2,p29_r0])).
cnf(p30_r1,plain,((r) | (p)),inference(resolution,[status(thm)],[p30_r0,p28])).
cnf(p32_r0,plain,((q) | (r)),inference(resolution,[status(thm)],[a1,p30_r1])).
cnf(p33_r0,plain,(~(p) | (r)),inference(resolution,[status(thm)],[a3,p32_r0])).
cnf(p33_r1,plain,((r)),inference(resolution,[status(thm)],[p33_r0,p30_r1])).
cnf(goal_1,theorem,((r)),inference(reiteration,[status(thm)],[p33_r1])).
