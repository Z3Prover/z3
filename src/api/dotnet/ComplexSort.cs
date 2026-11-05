/* Copyright (c) 2026 Microsoft Corporation */
using System;

namespace Microsoft.Z3
{
    /// <summary>A Complex sort, representing pairs of Reals.</summary>
    public class ComplexSort : ArithSort
    {
        internal ComplexSort(Context ctx, IntPtr obj) : base(ctx, obj) { }

        internal ComplexSort(Context ctx)
            : base(ctx, Native.Z3_mk_complex_sort(ctx.nCtx)) { }
    }
}
