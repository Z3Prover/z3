/**
 * This file was automatically generated from Statistics.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

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
            public long UIntValue() { return m_long; } 
            /**
             * The double-value of the entry.
             **/
            public double DoubleValue() { return m_double; } 
            /**
             * True if the entry is uint-valued.
             **/
            public boolean IsUInt() { return m_is_long; } 
            /**
             * True if the entry is double-valued.
             **/
            public boolean IsDouble() { return m_is_double; } 

            /**
             * The string representation of the the entry's value.
             **/
            public String Value() 
                {
                    

                    if (IsUInt)
                        return m_long.ToString();
                    else if (IsDouble)
                        return m_double.ToString();
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

            private boolean m_is_long = false;
            private boolean m_is_double = false;
            private long m_long = 0;
            private double m_double = 0.0;
            Entry(String k, long v)
            {
                Key = k;
                m_is_long = true;
                m_long = v;
            }
            Entry(String k, double v)
            {
                Key = k;
                m_is_double = true;
                m_double = v;
            }
        }

        /**
         * A string representation of the statistical data.
         **/
        public String toString()
        {
            return Native.statsToString(Context().nCtx(), NativeObject());
        }

        /**
         * The number of statistical data.
         **/
        public long Size()  { return Native.statsSize(Context().nCtx(), NativeObject()); }

        /**
         * The data entries.
         **/
        public Entry[] Entries() 
            {
                
                
                

                long n = Size;
                Entry[] res = new Entry[n];
                for (long i; i < n; i++)
                {
                    Entry e;
                    String k = Native.statsGetKey(Context().nCtx(), NativeObject(), i);
                    if (Native.statsIsLong(Context().nCtx(), NativeObject(), i) != 0)
                        e = new Entry(k, Native.statsGetLongValue(Context().nCtx(), NativeObject(), i));
                    else if (Native.statsIsDouble(Context().nCtx(), NativeObject(), i) != 0)
                        e = new Entry(k, Native.statsGetDoubleValue(Context().nCtx(), NativeObject(), i));
                    else
                        throw new Z3Exception("Unknown data entry value");
                    res[i] = e;
                }
                return res;
        }

        /**
         * The statistical counters.
         **/
        public String[] Keys() 
            {
                

                long n = Size;
                String[] res = new String[n];
                for (long i; i < n; i++)
                    res[i] = Native.statsGetKey(Context().nCtx(), NativeObject(), i);
                return res;
            }

        /**
         * The value of a particular statistical counter.
         * <remarks>Returns null if the key is unknown.</remarks>
         **/
        public Entry get(String key) 
            {
                long n = Size;
                Entry[] es = Entries;
                for (long i; i < n; i++)
                    if (es[i].Key == key)
                        return es[i];
                return null;
            }

        Statistics(Context ctx, long obj)
        { super(ctx, obj);
            
        }

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.statsIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.statsDecRef(ctx.nCtx(), obj);
            }
        };

        void IncRef(long o)
        {
            Context.Statistics_DRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context.Statistics_DRQ.Add(o);
            super.DecRef(o);
        }
    }
