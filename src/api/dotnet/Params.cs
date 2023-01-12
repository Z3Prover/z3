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

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// A Params objects represents a configuration in the form of Symbol/value pairs.
    /// </summary>
    public class Params : Z3Object
    {
        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, bool value)
        {
            Debug.Assert(name != null);

            Native.Z3_params_set_bool(Context.nCtx, NativeObject, name.NativeObject, (byte)(value ? 1 : 0));
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, uint value)
        {
            Debug.Assert(name != null);

            Native.Z3_params_set_uint(Context.nCtx, NativeObject, name.NativeObject, value);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, double value)
        {
            Debug.Assert(name != null);            

            Native.Z3_params_set_double(Context.nCtx, NativeObject, name.NativeObject, value);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, string value)
        {
            Debug.Assert(value != null);

            Native.Z3_params_set_symbol(Context.nCtx, NativeObject, name.NativeObject, Context.MkSymbol(value).NativeObject);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(Symbol name, Symbol value)
        {
            Debug.Assert(name != null);
            Debug.Assert(value != null);

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
            Debug.Assert(value != null);

            Native.Z3_params_set_symbol(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value.NativeObject);
            return this;
        }

        /// <summary>
        /// Adds a parameter setting.
        /// </summary>
        public Params Add(string name, string value)
        {
            Debug.Assert(name != null);
            Debug.Assert(value != null);

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
            Debug.Assert(ctx != null);
        }      

        internal override void IncRef(IntPtr o)
        {
            Native.Z3_params_inc_ref(Context.nCtx, o);
        }

        internal override void DecRef(IntPtr o)
        {
            lock (Context)
            {
                if (Context.nCtx != IntPtr.Zero)
                    Native.Z3_params_dec_ref(Context.nCtx, o);
            }
        }
        #endregion
    }
}
