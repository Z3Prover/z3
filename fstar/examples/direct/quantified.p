% Native direct proof; the last input assertion is discharged, not an axiom.
tff(ts0,type,'U':$tType).
tff(td5,type,a:'U').
tff(td7,type,q:('U') > $o).
tff(td8,type,p:('U') > $o).
tff(a0,axiom,(![X0:'U']:((p(X0)) | (q(X0))))).
tff(a1,axiom,(~(p(a)))).
tff(p16_inst,plain,((p(a)) | (q(a))),inference(instantiate,[status(thm)],[a0])).
tff(p16_r0,plain,((q(a))),inference(resolution,[status(thm)],[p16_inst,a1])).
tff(p13,plain,(~(q(a)) | (q(a))),inference(tautology,[status(thm)],[])).
tff(p16_r1,plain,((q(a))),inference(resolution,[status(thm)],[p16_r0,p13])).
tff(goal_1,theorem,((q(a))),inference(reiteration,[status(thm)],[p16_r1])).
