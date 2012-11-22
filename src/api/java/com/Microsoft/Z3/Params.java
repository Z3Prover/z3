/**
 * This file was automatically generated from Params.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * A ParameterSet represents a configuration in the form of Symbol/value pairs.
     **/
    public class Params extends Z3Object
    {
        /**
         * Adds a parameter setting.
         **/
        public void Add(Symbol name, boolean value)
        {
            

            Native.paramsSetBoolean(Context.nCtx, NativeObject, name.NativeObject, (value) ? 1 : 0);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(Symbol name, Integer value)
        {
            

            Native.paramsSetInteger(Context.nCtx, NativeObject, name.NativeObject, value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(Symbol name, double value)
        {
            
            
            Native.paramsSetDouble(Context.nCtx, NativeObject, name.NativeObject, value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(Symbol name, Symbol value)
        {
            
            

            Native.paramsSetSymbol(Context.nCtx, NativeObject, name.NativeObject, value.NativeObject);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, boolean value)
        {
            Native.paramsSetBoolean(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, (value) ? 1 : 0);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, Integer value)
        {
            Native.paramsSetInteger(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, double value)
        {
            Native.paramsSetDouble(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, Symbol value)
        {
            

            Native.paramsSetSymbol(Context.nCtx, NativeObject, Context.MkSymbol(name).NativeObject, value.NativeObject);
        }

        /**
         * A string representation of the parameter set.
         **/
        public String toString()
        {
            return Native.paramstoString(Context.nCtx, NativeObject);
        }

        Params(Context ctx)
            { super(ctx, Native.mkParams(ctx.nCtx));
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.paramsIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.paramsDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.ParamsDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.ParamsDRQ.Add(o);
            super.DecRef(o);
        }
    }
