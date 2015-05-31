/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Parameter.cs

Abstract:

    Z3 Managed API: Parameter Descriptions

Author:

    Christoph Wintersteiger (cwinter) 2012-03-20

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// A ParamDescrs describes a set of parameters.
    /// </summary>
    [ContractVerification(true)]
    public class ParamDescrs : Z3Object
    {
        /// <summary>
        /// validate a set of parameters.
        /// </summary>
        public void Validate(Params p)
        {
            Contract.Requires(p != null);
            Native.Z3_params_validate(Context.nCtx, p.NativeObject, NativeObject);
        }

        /// <summary>
        /// Retrieve kind of parameter.
        /// </summary>
        public Z3_param_kind GetKind(Symbol name)
        {
            Contract.Requires(name != null);
            return (Z3_param_kind)Native.Z3_param_descrs_get_kind(Context.nCtx, NativeObject, name.NativeObject);
        }

        /// <summary>
        /// Retrieve all names of parameters.
        /// </summary>
        public Symbol[] Names 
        {
            get 
            {
                  uint sz = Native.Z3_param_descrs_size(Context.nCtx, NativeObject);
                  Symbol[] names = new Symbol[sz];
                  for (uint i = 0; i < sz; ++i) {
                      names[i] = Symbol.Create(Context, Native.Z3_param_descrs_get_name(Context.nCtx, NativeObject, i));
                  }
                  return names;
            }
        }

        /// <summary>
        /// The size of the ParamDescrs.
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_param_descrs_size(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Retrieves a string representation of the ParamDescrs. 
        /// </summary>    
        public override string ToString()
        {
            return Native.Z3_param_descrs_to_string(Context.nCtx, NativeObject); 
        }

        #region Internal
        internal ParamDescrs(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_param_descrs_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_param_descrs_dec_ref(ctx.nCtx, obj);
            }
        };        

        internal override void IncRef(IntPtr o)
        {
            Context.ParamDescrs_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.ParamDescrs_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
