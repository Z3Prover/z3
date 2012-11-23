/**
 * This file was automatically generated from FuncInterp.cs 
 **/

package com.Microsoft.Z3;

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
            public Expr Value()  {
                    
                    return Expr.Create(Context, Native.funcEntryGetValue(Context.nCtx, NativeObject)); }
            }

            /**
             * The number of arguments of the entry.
             **/
            public long NumArgs()  { return Native.funcEntryGetNumArgs(Context.nCtx, NativeObject); }

            /**
             * The arguments of the function entry.
             **/
            public Expr[] Args() 
                {
                    
                    

                    long n = NumArgs;
                    Expr[] res = new Expr[n];
                    for (long i = 0; i < n; i++)
                        res[i] = Expr.Create(Context, Native.funcEntryGetArg(Context.nCtx, NativeObject, i));
                    return res;
                }

            /**
             * A string representation of the function entry.
             **/
            public String toString()
            {
                long n = NumArgs;
                String res = "[";
                Expr[] args = Args;
                for (long i = 0; i < n; i++)
                    res += args[i] + ", ";
                return res + Value + "]";
            }

            Entry(Context ctx, IntPtr obj) { super(ctx, obj);  }

            class DecRefQueue extends Z3.DecRefQueue
            {
                public void IncRef(Context ctx, IntPtr obj)
                {
                    Native.funcEntryIncRef(ctx.nCtx, obj);
                }

                public void DecRef(Context ctx, IntPtr obj)
                {
                    Native.funcEntryDecRef(ctx.nCtx, obj);
                }
            };

            void IncRef(IntPtr o)
            {
                Context.FuncEntry_DRQ.IncAndClear(Context, o);
                super.IncRef(o);
            }

            void DecRef(IntPtr o)
            {
                Context.FuncEntry_DRQ.Add(o);
                super.DecRef(o);
            }
        };

        /**
         * The number of entries in the function interpretation.
         **/
        public long NumEntries()  { return Native.funcInterpGetNumEntries(Context.nCtx, NativeObject); }

        /**
         * The entries in the function interpretation
         **/
        public Entry[] Entries() 
            {
                
                Contract.Ensures(Contract.ForAll(0, Contract.Result<Entry[]>().Length, 
                    j => Contract.Result<Entry[]>()[j] != null));

                long n = NumEntries;
                Entry[] res = new Entry[n];
                for (long i = 0; i < n; i++)
                    res[i] = new Entry(Context, Native.funcInterpGetEntry(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The (symbolic) `else' value of the function interpretation.
         **/
        public Expr Else()  {
                

                return Expr.Create(Context, Native.funcInterpGetElse(Context.nCtx, NativeObject)); }
        }

        /**
         * The arity of the function interpretation
         **/
        public long Arity()  { return Native.funcInterpGetArity(Context.nCtx, NativeObject); }

        /**
         * A string representation of the function interpretation.
         **/
        public String toString()
        {
            String res = "";
            res += "[";
            for (Entry.Iterator e = Entries.iterator(); e.hasNext(); )
            {
                long n = e.NumArgs;                
                if (n > 1) res += "[";
                Expr[] args = e.Args;
                for (long i = 0; i < n; i++)
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

        FuncInterp(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.funcInterpIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.funcInterpDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.FuncInterp_DRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.FuncInterp_DRQ.Add(o);
            super.DecRef(o);
        }
    }
