/**
 * This file was automatically generated from Statistics.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

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
        public String Key;

        /**
         * The uint-value of the entry.
         **/
        public int UIntValue()
        {
            return m_int;
        }

        /**
         * The double-value of the entry.
         **/
        public double DoubleValue()
        {
            return m_double;
        }

        /**
         * True if the entry is uint-valued.
         **/
        public boolean IsUInt()
        {
            return m_is_int;
        }

        /**
         * True if the entry is double-valued.
         **/
        public boolean IsDouble()
        {
            return m_is_double;
        }

        /**
         * The string representation of the the entry's value.
         * 
         * @throws Z3Exception
         **/
        public String Value() throws Z3Exception
        {
            if (IsUInt())
                return Integer.toString(m_int);
            else if (IsDouble())
                return Double.toString(m_double);
            else
                throw new Z3Exception("Unknown statistical entry type");
        }

        /**
         * The string representation of the Entry.
         **/
        public String toString()
        {
            try
            {
                return Key + ": " + Value();
            } catch (Z3Exception e)
            {
                return new String("Z3Exception: " + e.getMessage());
            }
        }

        private boolean m_is_int = false;
        private boolean m_is_double = false;
        private int m_int = 0;
        private double m_double = 0.0;

        Entry(String k, int v)
        {
            Key = k;
            m_is_int = true;
            m_int = v;
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
        try
        {
            return Native.statsToString(Context().nCtx(), NativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    /**
     * The number of statistical data.
     **/
    public int Size() throws Z3Exception
    {
        return Native.statsSize(Context().nCtx(), NativeObject());
    }

    /**
     * The data entries.
     * 
     * @throws Z3Exception
     **/
    public Entry[] Entries() throws Z3Exception
    {

        int n = Size();
        Entry[] res = new Entry[n];
        for (int i = 0; i < n; i++)
        {
            Entry e;
            String k = Native.statsGetKey(Context().nCtx(), NativeObject(), i);
            if (Native.statsIsUint(Context().nCtx(), NativeObject(), i))
                e = new Entry(k, Native.statsGetUintValue(Context().nCtx(),
                        NativeObject(), i));
            else if (Native.statsIsDouble(Context().nCtx(), NativeObject(), i))
                e = new Entry(k, Native.statsGetDoubleValue(Context().nCtx(),
                        NativeObject(), i));
            else
                throw new Z3Exception("Unknown data entry value");
            res[i] = e;
        }
        return res;
    }

    /**
     * The statistical counters.
     **/
    public String[] Keys() throws Z3Exception
    {
        int n = Size();
        String[] res = new String[n];
        for (int i = 0; i < n; i++)
            res[i] = Native.statsGetKey(Context().nCtx(), NativeObject(), i);
        return res;
    }

    /**
     * The value of a particular statistical counter. <remarks>Returns null if
     * the key is unknown.</remarks>
     * 
     * @throws Z3Exception
     **/
    public Entry get(String key) throws Z3Exception
    {
        int n = Size();
        Entry[] es = Entries();
        for (int i = 0; i < n; i++)
            if (es[i].Key == key)
                return es[i];
        return null;
    }

    Statistics(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void IncRef(long o) throws Z3Exception
    {
        Context().Statistics_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        Context().Statistics_DRQ().Add(o);
        super.DecRef(o);
    }
}
