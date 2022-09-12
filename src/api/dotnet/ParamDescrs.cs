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

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// A ParamDescrs describes a set of parameters.
    /// </summary>
    public class ParamDescrs : Z3Object
    {
        /// <summary>
        /// validate a set of parameters.
        /// </summary>
        public void Validate(Params p)
        {
            Debug.Assert(p != null);
            Native.Z3_params_validate(Context.nCtx, p.NativeObject, NativeObject);
        }

        /// <summary>
        /// Retrieve kind of parameter.
        /// </summary>
        public Z3_param_kind GetKind(Symbol name)
        {
            Debug.Assert(name != null);
            return (Z3_param_kind)Native.Z3_param_descrs_get_kind(Context.nCtx, NativeObject, name.NativeObject);
        }

        /// <summary>
        /// Retrieve documentation of parameter.
        /// </summary>
        public string GetDocumentation(Symbol name)
        {
            Debug.Assert(name != null);
            return Native.Z3_param_descrs_get_documentation(Context.nCtx, NativeObject, name.NativeObject);
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
            Debug.Assert(ctx != null);
        }       

        internal override void IncRef(IntPtr o)
        {
            Native.Z3_param_descrs_inc_ref(Context.nCtx, o);
        }

        internal override void DecRef(IntPtr o)
        {
            lock (Context)
            {
                if (Context.nCtx != IntPtr.Zero)
                    Native.Z3_param_descrs_dec_ref(Context.nCtx, o);
            }
        }
        #endregion
    }
}
