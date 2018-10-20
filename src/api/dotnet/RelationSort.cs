/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    RelationSort.cs

Abstract:

    Z3 Managed API: Relation Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Relation sorts.
    /// </summary>
    public class RelationSort : Sort
    {
        /// <summary>
        /// The arity of the relation sort.
        /// </summary>
        public uint Arity
        {
            get { return Native.Z3_get_relation_arity(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The sorts of the columns of the relation sort.
        /// </summary>
        public Sort[] ColumnSorts
        {
            get
            {

                if (m_columnSorts != null)
                    return m_columnSorts;

                uint n = Arity;
                Sort[] res = new Sort[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.Z3_get_relation_column(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        #region Internal
        private Sort[] m_columnSorts = null;

        internal RelationSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
