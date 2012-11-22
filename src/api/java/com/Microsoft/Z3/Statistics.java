/**
 * This file was automatically generated from Statistics.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Objects of this class track statistical information about solvers. 
     **/
    public class Statistics extends Z3Object
    {
        /**
         * Statistical data is organized into pairs of [Key, Entry], where every
         * Entry is either a <code>DoubleEntry</code> or a <code>UIntEntry</code>
         **/
        public class Entry
        {
            /**
             * The key of the entry.
             **/
            /**
             * The uint-value of the entry.
             **/
            public Integer UIntValue() { return mInteger; } 
            /**
             * The double-value of the entry.
             **/
            public double DoubleValue() { return mDouble; } 
            /**
             * True if the entry is uint-valued.
             **/
            public boolean IsUInt() { return mIsInteger; } 
            /**
             * True if the entry is double-valued.
             **/
            public boolean IsDouble() { return mIsDouble; } 

            /**
             * The string representation of the the entry's value.
             **/
            public String Value() 
                {
                    

                    if (IsUInt)
                        return mInteger.toString();
                    else if (IsDouble)
                        return mDouble.toString();
                    else
                        throw new Z3Exception("Unknown statistical entry type");
            }

            /**
             * The string representation of the Entry.
             **/
            public String toString()
            {
                return Key + ": " + Value;
            }

            private boolean mIsInteger = false;
            private boolean mIsDouble = false;
            private Integer mInteger = 0;
            private double mDouble = 0.0;
            Entry(String k, Integer v) { Key = k; mIsInteger = true; mInteger = v; }
            Entry(String k, double v) { Key = k; mIsDouble = true; mDouble = v; }
        }

        /**
         * A string representation of the statistical data.
         **/
        public String toString()
        {
            return Native.statstoString(Context.nCtx, NativeObject);
        }

        /**
         * The number of statistical data.
         **/
        public Integer Size()  { return Native.statsSize(Context.nCtx, NativeObject); }

        /**
         * The data entries.
         **/
        public Entry[] Entries() 
            {
                
                
                

                Integer n = Size;
                Entry[] res = new Entry[n];
                for (Integer i = 0; i < n; i++)
                {
                    Entry e;
                    String k = Native.statsGetKey(Context.nCtx, NativeObject, i);
                    if (Native.statsIsInteger(Context.nCtx, NativeObject, i) != 0)
                        e = new Entry(k, Native.statsGetIntegerValue(Context.nCtx, NativeObject, i));
                    else if (Native.statsIsDouble(Context.nCtx, NativeObject, i) != 0)
                        e = new Entry(k, Native.statsGetDoubleValue(Context.nCtx, NativeObject, i));
                    else
                        throw new Z3Exception("Unknown data entry value");
                    res[i] = e;
                return res;
            }
        }

        /**
         * The statistical counters.
         **/
        public String[] Keys() 
            {
                

                Integer n = Size;
                String[] res = new String[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = Native.statsGetKey(Context.nCtx, NativeObject, i);
                return res;
        }

        /**
         * The value of a particular statistical counter.
         * <remarks>Returns null if the key is unknown.</remarks>
         **/
        public Entry this[String key]() 
            {
                Integer n = Size;
                Entry[] es = Entries;
                for (Integer i = 0; i < n; i++)
                    if (es[i].Key == key)
                        return es[i];
                return null;
        }

        Statistics(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.statsIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.statsDecRef(ctx.nCtx, obj);
            }
        };

        void IncRef(IntPtr o)
        {
            Context.StatisticsDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.StatisticsDRQ.Add(o);
            super.DecRef(o);
        }
    }
