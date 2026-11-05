/* Copyright (c) 2026 Microsoft Corporation */
using System;

namespace Microsoft.Z3
{
    /// <summary>A Complex expression. Complex numbers have no ordering.</summary>
    public class ComplexExpr : ArithExpr
    {
        internal ComplexExpr(Context ctx, IntPtr obj) : base(ctx, obj) { }

        /// <summary>The Real-valued real component.</summary>
        public RealExpr RealPart { get { return Context.MkRealPart(this); } }

        /// <summary>The Real-valued imaginary component.</summary>
        public RealExpr ImagPart { get { return Context.MkImagPart(this); } }
    }
}
