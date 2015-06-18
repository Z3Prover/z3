
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using Microsoft.SolverFoundation.Services;
using System;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    public class Z3MILPParams : Z3BaseParams
    {
        // Need these constructors for reflection done by plugin model

        public Z3MILPParams() : base() { }

        public Z3MILPParams(Directive directive) : base(directive) { }

        public Z3MILPParams(Func<bool> queryAbortFunction) : base(queryAbortFunction) { }

        public Z3MILPParams(Z3BaseParams z3Parameters) : base (z3Parameters) { }
    }

}