/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Statistics.cs

Abstract:

    Z3 Managed API: Statistics

Author:

    Christoph Wintersteiger (cwinter) 2012-03-22

Notes:
    
--*/

using System;
using System.Diagnostics;
namespace Microsoft.Z3
{

    using Z3_context = System.IntPtr;
    using Z3_stats = System.IntPtr;
    /// <summary>
    /// Objects of this class track statistical information about solvers. 
    /// </summary>
    public class Statistics : Z3Object
    {
        /// <summary>
        /// Statistical data is organized into pairs of [Key, Entry], where every
        /// Entry is either a <c>DoubleEntry</c> or a <c>UIntEntry</c>
        /// </summary>
        public class Entry
        {
            /// <summary>
            /// The key of the entry.
            /// </summary>
            readonly public string Key;
            /// <summary>
            /// The uint-value of the entry.
            /// </summary>
            public uint UIntValue { get { return m_uint; } }
            /// <summary>
            /// The double-value of the entry.
            /// </summary>
            public double DoubleValue { get { return m_double; } }
            /// <summary>
            /// True if the entry is uint-valued.
            /// </summary>
            public bool IsUInt { get { return m_is_uint; } }
            /// <summary>
            /// True if the entry is double-valued.
            /// </summary>
            public bool IsDouble { get { return m_is_double; } }

            /// <summary>
            /// The string representation of the entry's value.
            /// </summary>
            public string Value
            {
                get
                {

                    if (IsUInt)
                        return m_uint.ToString();
                    else if (IsDouble)
                        return m_double.ToString();
                    else
                        throw new Z3Exception("Unknown statistical entry type");
                }
            }

            /// <summary>
            /// The string representation of the Entry.
            /// </summary>
            public override string ToString()
            {
                return Key + ": " + Value;
            }

            #region Internal
            readonly private bool m_is_uint = false;
            readonly private bool m_is_double = false;
            readonly private uint m_uint = 0;
            readonly private double m_double = 0.0;
            internal Entry(string k, uint v)
            {
                Key = k;
                m_is_uint = true;
                m_uint = v;
            }
            internal Entry(string k, double v)
            {
                Key = k;
                m_is_double = true;
                m_double = v;
            }
            #endregion
        }

        /// <summary>
        /// A string representation of the statistical data.
        /// </summary>    
        public override string ToString()
        {
            return Native.Z3_stats_to_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// The number of statistical data.
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_stats_size(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The data entries.
        /// </summary>
        public Entry[] Entries
        {
            get
            {
                return NativeEntries(Context.nCtx, NativeObject);
            }
        }

        internal static Entry[] NativeEntries(Z3_context ctx, Z3_stats stats)
        {
            uint n = Native.Z3_stats_size(ctx, stats);
            Entry[] res = new Entry[n];
            for (uint i = 0; i < n; i++)
            {
                Entry e;
                string k = Native.Z3_stats_get_key(ctx, stats, i);
                if (Native.Z3_stats_is_uint(ctx, stats, i) != 0)
                    e = new Entry(k, Native.Z3_stats_get_uint_value(ctx, stats, i));
                else if (Native.Z3_stats_is_double(ctx, stats, i) != 0)
                    e = new Entry(k, Native.Z3_stats_get_double_value(ctx, stats, i));
                else
                    throw new Z3Exception("Unknown data entry value");
                res[i] = e;
            }
            return res;
        }

        /// <summary>
        /// The statistical counters.
        /// </summary>
        public string[] Keys
        {
            get
            {

                uint n = Size;
                string[] res = new string[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Native.Z3_stats_get_key(Context.nCtx, NativeObject, i);
                return res;
            }
        }

        /// <summary>
        /// The value of a particular statistical counter.
        /// </summary>        
        /// <remarks>Returns null if the key is unknown.</remarks>
        public Entry this[string key]
        {
            get
            {
                uint n = Size;
                Entry[] es = Entries;
                for (uint i = 0; i < n; i++)
                    if (es[i].Key == key)
                        return es[i];
                return null;
            }
        }

        #region Internal
        internal Statistics(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }

        internal override void IncRef(IntPtr o)
        {
            Native.Z3_stats_inc_ref(Context.nCtx, o);
        }

        internal override void DecRef(IntPtr o)
        {
            lock (Context)
            {
                if (Context.nCtx != IntPtr.Zero)
                    Native.Z3_stats_dec_ref(Context.nCtx, o);
            }
        }
        #endregion
    }
}
