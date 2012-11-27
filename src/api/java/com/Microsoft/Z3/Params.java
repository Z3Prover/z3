/**
 * This file was automatically generated from Params.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

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
            

            Native.paramsSetBool(Context().nCtx(), NativeObject(), name.NativeObject(), (value) ? true : false);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(Symbol name, double value)
        {
            
            
            Native.paramsSetDouble(Context().nCtx(), NativeObject(), name.NativeObject(), value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(Symbol name, Symbol value)
        {
            
            

            Native.paramsSetSymbol(Context().nCtx(), NativeObject(), name.NativeObject(), value.NativeObject());
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, boolean value)
        {
            Native.paramsSetBool(Context().nCtx(), NativeObject(), Context().MkSymbol(name).NativeObject(), (value) ? true : false);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, int value)
        {
            Native.paramsSetUint(Context().nCtx(), NativeObject(), Context().MkSymbol(name).NativeObject(), value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, double value)
        {
            Native.paramsSetDouble(Context().nCtx(), NativeObject(), Context().MkSymbol(name).NativeObject(), value);
        }

        /**
         * Adds a parameter setting.
         **/
        public void Add(String name, Symbol value)
        {
            

            Native.paramsSetSymbol(Context().nCtx(), NativeObject(), Context().MkSymbol(name).NativeObject(), value.NativeObject());
        }

        /**
         * A string representation of the parameter set.
         **/
        public String toString()
        {
            return Native.paramsToString(Context().nCtx(), NativeObject());
        }

        Params(Context ctx)
        { super(ctx, Native.mkParams(ctx.nCtx()));
            
        }

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.paramsIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.paramsDecRef(ctx.nCtx(), obj);
            }
        };        

        void IncRef(long o)
        {
            Context().Params_DRQ().IncAndClear(Context(), o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context().Params_DRQ().Add(o);
            super.DecRef(o);
        }
    }
