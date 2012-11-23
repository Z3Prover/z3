/**
 * This file was automatically generated from RelationSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Relation sorts.
     **/
    public class RelationSort extends Sort
    {
        /**
         * The arity of the relation sort.
         **/
        public long Arity()  { return Native.getRelationArity(Context().nCtx(), NativeObject()); }

        /**
         * The sorts of the columns of the relation sort.
         **/
        public Sort[] ColumnSorts() 
            {
                

                if (m_columnSorts != null)
                    return m_columnSorts;

                long n = Arity;
                Sort[] res = new Sort[n];
                for (long i; i < n; i++)
                    res[i] = Sort.Create(Context, Native.getRelationColumn(Context().nCtx(), NativeObject(), i));
                return res;
            }

        private Sort[] m_columnSorts = null;

        RelationSort(Context ctx, long obj)
        { super(ctx, obj);
            
        }
    }
