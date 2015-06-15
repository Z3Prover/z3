using Microsoft.SolverFoundation.Services;
using System;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    public class Z3TermParams : Z3BaseParams
    {
        public Z3TermParams() : base() { }

        public Z3TermParams(Directive directive) : base(directive) { }

        public Z3TermParams(Func<bool> queryAbortFunction) : base(queryAbortFunction) { }

        public Z3TermParams(Z3BaseParams z3Parameters) : base(z3Parameters) { }
    }

}