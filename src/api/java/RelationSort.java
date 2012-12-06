/**
 * This file was automatically generated from RelationSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
    public int Arity() throws Z3Exception
    {
        return Native.getRelationArity(Context().nCtx(), NativeObject());
    }

    /**
     * The sorts of the columns of the relation sort.
     * @throws Z3Exception 
     **/
    public Sort[] ColumnSorts() throws Z3Exception
    {

        if (m_columnSorts != null)
            return m_columnSorts;

        int n = Arity();
        Sort[] res = new Sort[n];
        for (int i = 0; i < n; i++)
            res[i] = Sort.Create(Context(), Native.getRelationColumn(Context()
                    .nCtx(), NativeObject(), i));
        return res;
    }

    private Sort[] m_columnSorts = null;

    RelationSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
