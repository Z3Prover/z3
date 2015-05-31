/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    RelationSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Relation sorts.
 **/
public class RelationSort extends Sort
{
    /**
     * The arity of the relation sort.
     **/
    public int getArity()
    {
        return Native.getRelationArity(getContext().nCtx(), getNativeObject());
    }

    /**
     * The sorts of the columns of the relation sort.
     * @throws Z3Exception 
     **/
    public Sort[] getColumnSorts()
    {

        if (m_columnSorts != null)
            return m_columnSorts;

        int n = getArity();
        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.create(getContext(), Native.getRelationColumn(getContext()
                    .nCtx(), getNativeObject(), i));
        return res;
    }

    private Sort[] m_columnSorts = null;

    RelationSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
