/**
 * This file was automatically generated from ParamDescrs.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * A ParamDescrs describes a set of parameters.
     **/
    public class ParamDescrs extends Z3Object
    {
        /**
         * validate a set of parameters.
         **/
        public void Validate(Params p)
        {
            
            Native.paramsValidate(Context.nCtx, p.NativeObject, NativeObject);
        }

        /**
         * Retrieve kind of parameter.
         **/
        public Z3ParamKind GetKind(Symbol name)
        {
            
            return (Z3ParamKind)Native.paramDescrsGetKind(Context.nCtx, NativeObject, name.NativeObject);
        }

        /**
         * Retrieve all names of parameters.
         **/
        public Symbol[] Names() 
            {
                  Integer sz = Native.paramDescrsSize(Context.nCtx, NativeObject);
                  Symbol[] names = new Symbol[sz];
                  for (Integer i = 0; i < sz; ++i) {
                      names[i] = Symbol.Create(Context, Native.paramDescrsGetName(Context.nCtx, NativeObject, i));
                  return names;
            }
        }

        /**
         * The size of the ParamDescrs.
         **/
        public Integer Size()  { return Native.paramDescrsSize(Context.nCtx, NativeObject); }

        /**
         * Retrieves a string representation of the ParamDescrs. 
         **/
        public String toString()
        {
            return Native.paramDescrstoString(Context.nCtx, NativeObject); 
        }

        ParamDescrs(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.paramDescrsIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.paramDescrsDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.ParamDescrsDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.ParamDescrsDRQ.Add(o);
            super.DecRef(o);
        }
    }
