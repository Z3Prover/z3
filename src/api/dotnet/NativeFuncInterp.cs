/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    NativeFuncInterp.cs

Abstract:

    Z3 Managed API: Function Interpretations

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{

    using Z3_context = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_app = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_model = System.IntPtr;
    using Z3_func_interp = System.IntPtr;
    using Z3_func_entry = System.IntPtr;

    /// <summary>
    ///  A function interpretation is represented as a finite map and an 'else' value.
    ///  Each entry in the finite map represents the value of a function given a set of arguments.  
    /// </summary>
    public class NativeFuncInterp 
    {

        /// <summary>
        /// Evaluation entry of a function
        /// </summary>
        public class Entry
        {
            /// <summary>
            /// Argument values that define entry
            /// </summary>
            public Z3_ast[] Arguments;

            /// <summary>
            /// Result of applying function to Arguments in the interpretation
            /// </summary>
            public Z3_ast Result;
        }

        /// <summary>
        /// Function that is interpreted
        /// </summary>
        public Z3_func_decl Declaration;

        /// <summary>
        /// Set of non-default entries defining the function graph
        /// </summary>
        public Entry[] Entries;

        /// <summary>
        /// Default cause of the function interpretation
        /// </summary>
        public Z3_ast Else;

        #region Internal
        internal NativeFuncInterp(NativeContext ctx, NativeModel mdl, Z3_func_decl decl, Z3_func_interp fi)
        {
            Debug.Assert(ctx != null);
            Z3_context nCtx = ctx.nCtx;
            Native.Z3_func_interp_inc_ref(nCtx, fi);

            Declaration = decl;
            Else = Native.Z3_func_interp_get_else(nCtx, fi);
            uint numEntries = Native.Z3_func_interp_get_num_entries(nCtx, fi);
            uint numArgs = Native.Z3_func_interp_get_arity(nCtx, fi);
            Entries = new Entry[numEntries];

            for (uint j = 0; j < numEntries; ++j)
            {
                var ntvEntry = Native.Z3_func_interp_get_entry(nCtx, fi, j);
                Entries[j] = new Entry();
                Native.Z3_func_entry_inc_ref(nCtx, ntvEntry);
                Entries[j].Arguments = new Z3_ast[numArgs];
                for (uint i = 0; i < numArgs; ++i)
                    Entries[j].Arguments[i] = Native.Z3_func_entry_get_arg(nCtx, ntvEntry, i);
                Entries[j].Result = Native.Z3_func_entry_get_value(nCtx, ntvEntry);
                Native.Z3_func_entry_dec_ref(nCtx, ntvEntry);
            }

            Native.Z3_func_interp_dec_ref(nCtx, fi);
        }


        #endregion
    }
}
