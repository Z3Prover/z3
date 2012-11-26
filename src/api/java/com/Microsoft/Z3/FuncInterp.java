/**
 * This file was automatically generated from FuncInterp.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     *  A function interpretation is represented as a finite map and an 'else' value.
     *  Each entry in the finite map represents the value of a function given a set of arguments.  
     **/
    public class FuncInterp extends Z3Object
    {
        /**
         * An Entry object represents an element in the finite map used to encode
         * a function interpretation.
         **/
        public class Entry extends Z3Object
        {
            /**
             * Return the (symbolic) value of this entry.
             **/
            public Expr Value() 
                {
                    
                    return Expr.Create(Context(), Native.funcEntryGetValue(Context().nCtx(), NativeObject()));
                }

            /**
             * The number of arguments of the entry.
             **/
            public int NumArgs()  { return Native.funcEntryGetNumArgs(Context().nCtx(), NativeObject()); }

            /**
             * The arguments of the function entry.
             **/
            public Expr[] Args() 
                {
                    
                    

                    int n = NumArgs();
                    Expr[] res = new Expr[n];
                    for (int i = 0; i < n; i++)
                        res[i] = Expr.Create(Context(), Native.funcEntryGetArg(Context().nCtx(), NativeObject(), i));
                    return res;
                }

            /**
             * A string representation of the function entry.
             **/
            public String toString()
            {
                int n = NumArgs();
                String res = "[";
                Expr[] args = Args;
                for (int i = 0; i < n; i++)
                    res += args[i] + ", ";
                return res + Value + "]";
            }

        Entry(Context ctx, long obj) { super(ctx, obj); {  }}

            class DecRefQueue extends IDecRefQueue
            {
                public void IncRef(Context ctx, long obj)
                {
                    Native.funcEntryIncRef(ctx.nCtx(), obj);
                }

                public void DecRef(Context ctx, long obj)
                {
                    Native.funcEntryDecRef(ctx.nCtx(), obj);
                }
            };

            void IncRef(long o)
            {
                Context().FuncEntry_DRQ().IncAndClear(Context(), o);
                super.IncRef(o);
            }

            void DecRef(long o)
            {
                Context().FuncEntry_DRQ().Add(o);
                super.DecRef(o);
            }
        };

        /**
         * The number of entries in the function interpretation.
         **/
        public int NumEntries()  { return Native.funcInterpGetNumEntries(Context().nCtx(), NativeObject()); }

        /**
         * The entries in the function interpretation
         **/
        public Entry[] Entries() 
            {
                
                

                int n = NumEntries();
                Entry[] res = new Entry[n];
                for (int i = 0; i < n; i++)
                    res[i] = new Entry(Context(), Native.funcInterpGetEntry(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The (symbolic) `else' value of the function interpretation.
         **/
        public Expr Else() 
            {
                

                return Expr.Create(Context(), Native.funcInterpGetElse(Context().nCtx(), NativeObject()));
            }

        /**
         * The arity of the function interpretation
         **/
        public int Arity()  { return Native.funcInterpGetArity(Context().nCtx(), NativeObject()); }

        /**
         * A string representation of the function interpretation.
         **/
        public String toString()
        {
            String res = "";
            res += "[";
            for (Entry e: Entries)
            {
                int n = e.NumArgs;
                if (n > 1) res += "[";
                Expr[] args = e.Args;
                for (int i = 0; i < n; i++)
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

        FuncInterp(Context ctx, long obj)
        { super(ctx, obj);
            
        }

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.funcInterpIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.funcInterpDecRef(ctx.nCtx(), obj);
            }
        };

        void IncRef(long o)
        {
            Context().FuncInterp_DRQ().IncAndClear(Context(), o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context().FuncInterp_DRQ().Add(o);
            super.DecRef(o);
        }
    }
