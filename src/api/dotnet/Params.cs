/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Parameter.cs

Abstract:

    Z3 Managed API: Parameters

Author:

    Christoph Wintersteiger (cwinter) 2012-03-20

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// A Params objects represents a configuration in the form of Symbol/value pairs.
    /// </summary>
    [ContractVerification(true)]
    public class Params : Z3Object
    {
        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, bool value)
        {
            Contract.Requires(name != null);

            Native.Z3_params_set_bool(Context.nCtx, NativeObject, name.NativeObject, (byte)(value ? 1 : 0));
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, uint value)
        {
            Contract.Requires(name != null);

            Native.Z3_params_set_uint(Context.nCtx, NativeObject, name.NativeObject, value);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, double value)
        {
            Contract.Requires(name != null);            

            Native.Z3_params_set_double(Context.nCtx, NativeObject, name.NativeObject, value);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, string value)
        {
            Contract.Requires(value != null);

            Native.Z3_params_set_symbol(Context.nCtx, NativeObject, name.NativeObject, Context.MkSymbol(value).NativeObject);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, Symbol value)
        {
            Contract.Requires(name != null);
            Contract.Requires(value != null);

            Native.Z3_params_set_symbol(Context.nCtx, NativeObject, name.NativeObject, value.NativeObject);
            return this;
        }


        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(string name, bool value)
        {
            Native.Z3_params_set_bool(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, (byte)(value ? 1 : 0));
	    return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(string name, uint value)
        {
            Native.Z3_params_set_uint(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value);
	    return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(string name, double value)
        {
            Native.Z3_params_set_double(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(string name, Symbol value)
        {
            Contract.Requires(value != null);

            Native.Z3_params_set_symbol(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value.NativeObject);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(string name, string value)
        {
            Contract.Requires(name != null);
            Contract.Requires(value != null);

            Native.Z3_params_set_symbol(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, Context.MkSymbol(value).NativeObject);
            return this;
        }

        /// <summary>
        /// A string representation of the parameter set.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_params_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal Params(Context ctx)
            : base(ctx, Native.Z3_mk_params(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_params_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_params_dec_ref(ctx.nCtx, obj);
            }
        };        

        internal override void IncRef(IntPtr o)
        {
            Context.Params_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Params_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
