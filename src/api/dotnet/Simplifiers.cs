/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Simplifiers.cs

Abstract:

    Z3 Managed API: Simplifiers

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

--*/

using System;
using System.Diagnostics;

namespace Microsoft.Z3
{
    /// <summary>
    /// Simplifiers are the basic building block for creating custom solvers with incremental pre-processing.
    /// The complete list of simplifiers may be obtained using <c>Context.NumSimplifiers</c> 
    /// and <c>Context.SimplifierNames</c>.
    /// It may also be obtained using the command <c>(help-simplifier)</c> in the SMT 2.0 front-end.
    /// </summary>
    public class Simplifier : Z3Object
    {
        /// <summary>
        /// A string containing a description of parameters accepted by the tactic.
        /// </summary>
        public string Help
        {
            get
            {

                return Native.Z3_simplifier_get_help(Context.nCtx, NativeObject);
            }
        }

        /// <summary>
        /// Retrieves parameter descriptions for Simplifiers.
        /// </summary>
        public ParamDescrs ParameterDescriptions
        {
            get { return new ParamDescrs(Context, Native.Z3_simplifier_get_param_descrs(Context.nCtx, NativeObject)); }
        }

        #region Internal
        internal Simplifier(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal Simplifier(Context ctx, string name)
            : base(ctx, Native.Z3_mk_simplifier(ctx.nCtx, name))
        {
            Debug.Assert(ctx != null);
        }

        internal override void IncRef(IntPtr o)
        {
            Native.Z3_simplifier_inc_ref(Context.nCtx, o);
        }

        internal override void DecRef(IntPtr o)
        {
            lock (Context)
            {
                if (Context.nCtx != IntPtr.Zero)
                    Native.Z3_simplifier_dec_ref(Context.nCtx, o);
            }
        }
        #endregion
    }
}
