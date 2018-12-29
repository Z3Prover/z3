/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    FuncInterp.cs

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
    /// <summary>
    ///  A function interpretation is represented as a finite map and an 'else' value.
    ///  Each entry in the finite map represents the value of a function given a set of arguments.  
    /// </summary>
    public class FuncInterp : Z3Object
    {
        /// <summary>
        /// An Entry object represents an element in the finite map used to encode
        /// a function interpretation.
        /// </summary>
        public class Entry : Z3Object
        {
            /// <summary>
            /// Return the (symbolic) value of this entry.
            /// </summary>
            public Expr Value
            {
                get
                {
                    return Expr.Create(Context, Native.Z3_func_entry_get_value(Context.nCtx, NativeObject));
                }
            }

            /// <summary>
            /// The number of arguments of the entry.
            /// </summary>
            public uint NumArgs
            {
                get { return Native.Z3_func_entry_get_num_args(Context.nCtx, NativeObject); }
            }

            /// <summary>
            /// The arguments of the function entry.
            /// </summary>
            public Expr[] Args
            {
                get
                {

                    uint n = NumArgs;
                    Expr[] res = new Expr[n];
                    for (uint i = 0; i < n; i++)
                        res[i] = Expr.Create(Context, Native.Z3_func_entry_get_arg(Context.nCtx, NativeObject, i));
                    return res;
                }
            }

            /// <summary>
            /// A string representation of the function entry.
            /// </summary>
            public override string ToString()
            {
                uint n = NumArgs;
                string res = "[";
                Expr[] args = Args;
                for (uint i = 0; i < n; i++)
                    res += args[i] + ", ";
                return res + Value + "]";
            }

            #region Internal
            internal Entry(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }

            internal class DecRefQueue : IDecRefQueue
            {
                public DecRefQueue() : base() { }
                public DecRefQueue(uint move_limit) : base(move_limit) { }
                internal override void IncRef(Context ctx, IntPtr obj)
                {
                    Native.Z3_func_entry_inc_ref(ctx.nCtx, obj);
                }

                internal override void DecRef(Context ctx, IntPtr obj)
                {
                    Native.Z3_func_entry_dec_ref(ctx.nCtx, obj);
                }
            };

            internal override void IncRef(IntPtr o)
            {
                Context.FuncEntry_DRQ.IncAndClear(Context, o);
                base.IncRef(o);
            }

            internal override void DecRef(IntPtr o)
            {
                Context.FuncEntry_DRQ.Add(o);
                base.DecRef(o);
            }
            #endregion
        };

        /// <summary>
        /// The number of entries in the function interpretation.
        /// </summary>
        public uint NumEntries
        {
            get { return Native.Z3_func_interp_get_num_entries(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The entries in the function interpretation
        /// </summary>
        public Entry[] Entries
        {
            get
            {

                uint n = NumEntries;
                Entry[] res = new Entry[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new Entry(Context, Native.Z3_func_interp_get_entry(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The (symbolic) `else' value of the function interpretation.
        /// </summary>
        public Expr Else
        {
            get
            {

                return Expr.Create(Context, Native.Z3_func_interp_get_else(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// The arity of the function interpretation
        /// </summary>
        public uint Arity
        {
            get { return Native.Z3_func_interp_get_arity(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// A string representation of the function interpretation.
        /// </summary>    
        public override string ToString()
        {
            string res = "";
            res += "[";
            foreach (Entry e in Entries)
            {
                uint n = e.NumArgs;
                if (n > 1) res += "[";
                Expr[] args = e.Args;
                for (uint i = 0; i < n; i++)
                {
                    if (i != 0) res += ", ";
                    res += args[i];
                }
                if (n > 1) res += "]";
                res += " -> " + e.Value + ", ";
            }
            res += "else -> " + Else;
            res += "]";
            return res;
        }

        #region Internal
        internal FuncInterp(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_func_interp_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_func_interp_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.FuncInterp_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.FuncInterp_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
