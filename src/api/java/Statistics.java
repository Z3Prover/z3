/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Statistics.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Objects of this class track statistical information about solvers.
 **/
public class Statistics extends Z3Object {
    /**
     * Statistical data is organized into pairs of [Key, Entry], where every
     * Entry is either a {@code DoubleEntry} or a {@code UIntEntry}
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
        public int getUIntValue()
        {
            return m_int;
        }

        /**
         * The double-value of the entry.
         **/
        public double getDoubleValue()
        {
            return m_double;
        }

        /**
         * True if the entry is uint-valued.
         **/
        public boolean isUInt()
        {
            return m_is_int;
        }

        /**
         * True if the entry is double-valued.
         **/
        public boolean isDouble()
        {
            return m_is_double;
        }

        /**
         * The string representation of the entry's value.
         * 
         * @throws Z3Exception
         **/
        public String getValueString()
        {
            if (isUInt()) {
                return Integer.toString(m_int);
            } else if (isDouble()) {
                return Double.toString(m_double);
            } else {
                throw new Z3Exception("Unknown statistical entry type");
            }
        }

        /**
         * The string representation of the Entry.
         **/
        @Override
        public String toString() {
            return Key + ": " + getValueString();
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
    @Override
    public String toString()
    {
        return Native.statsToString(getContext().nCtx(), getNativeObject());
    }

    /**
     * The number of statistical data.
     **/
    public int size()
    {
        return Native.statsSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * The data entries.
     * 
     * @throws Z3Exception
     **/
    public Entry[] getEntries()
    {

        int n = size();
        Entry[] res = new Entry[n];
        for (int i = 0; i < n; i++)
        {
            Entry e;
            String k = Native.statsGetKey(getContext().nCtx(), getNativeObject(), i);
            if (Native.statsIsUint(getContext().nCtx(), getNativeObject(), i)) {
                e = new Entry(k, Native.statsGetUintValue(getContext().nCtx(),
                    getNativeObject(), i));
            } else if (Native.statsIsDouble(getContext().nCtx(), getNativeObject(), i)) {
                e = new Entry(k, Native.statsGetDoubleValue(getContext().nCtx(),
                    getNativeObject(), i));
            } else {
                throw new Z3Exception("Unknown data entry value");
            }
            res[i] = e;
        }
        return res;
    }

    /**
     * The statistical counters.
     **/
    public String[] getKeys()
    {
        int n = size();
        String[] res = new String[n];
        for (int i = 0; i < n; i++)
            res[i] = Native.statsGetKey(getContext().nCtx(), getNativeObject(), i);
        return res;
    }

    /**
     * The value of a particular statistical counter.
     * Remarks: Returns null if
     * the key is unknown.
     * 
     * @throws Z3Exception
     **/
    public Entry get(String key)
    {
        int n = size();
        Entry[] es = getEntries();
        for (int i = 0; i < n; i++) {
            if (es[i].Key.equals(key)) {
                return es[i];
            }
        }
        return null;
    }

    Statistics(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        getContext().getStatisticsDRQ().storeReference(getContext(), this);
    }

    @Override
    void addToReferenceQueue() {
        Native.statsIncRef(getContext().nCtx(), getNativeObject());
    }
}
