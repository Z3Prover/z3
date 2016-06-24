/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Sort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_ast_kind;
import com.microsoft.z3.enumerations.Z3_sort_kind;

/**
 * The Sort class implements type information for ASTs.
 **/
public class Sort extends AST
{
    /**
     * Equality operator for objects of type Sort. 
     **/
    @Override
    public boolean equals(Object o)
    {
        if (o == this) return true;
        if (!(o instanceof Sort)) return false;
        Sort other = (Sort) o;

	return  (getContext().nCtx() == other.getContext().nCtx()) &&
	    (Native.isEqSort(
            getContext().nCtx(),
            getNativeObject(),
            other.getNativeObject()
        ));
    }

    /**
     * Hash code generation for Sorts
     * 
     * @return A hash code
     **/
    public int hashCode()
    {
        return super.hashCode();
    }

    /**
     * Returns a unique identifier for the sort.
     **/
    public int getId()
    {
        return Native.getSortId(getContext().nCtx(), getNativeObject());
    }

    /**
     * The kind of the sort.
     **/
    public Z3_sort_kind getSortKind()
    {
        return Z3_sort_kind.fromInt(Native.getSortKind(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * The name of the sort
     **/
    public Symbol getName()
    {
        return Symbol.create(getContext(),
                Native.getSortName(getContext().nCtx(), getNativeObject()));
    }

    /**
     * A string representation of the sort.
     **/
    @Override
    public String toString() {
        return Native.sortToString(getContext().nCtx(), getNativeObject());
    }

    /**
     * Sort constructor
     **/
    Sort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void checkNativeObject(long obj)
    {
        if (Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_SORT_AST
                .toInt())
            throw new Z3Exception("Underlying object is not a sort");
        super.checkNativeObject(obj);
    }

    static Sort create(Context ctx, long obj)
    {
        Z3_sort_kind sk = Z3_sort_kind.fromInt(Native.getSortKind(ctx.nCtx(), obj));
        switch (sk)
        {
        case Z3_ARRAY_SORT:
            return new ArraySort(ctx, obj);
        case Z3_BOOL_SORT:
            return new BoolSort(ctx, obj);
        case Z3_BV_SORT:
            return new BitVecSort(ctx, obj);
        case Z3_DATATYPE_SORT:
            return new DatatypeSort(ctx, obj);
        case Z3_INT_SORT:
            return new IntSort(ctx, obj);
        case Z3_REAL_SORT:
            return new RealSort(ctx, obj);
        case Z3_UNINTERPRETED_SORT:
            return new UninterpretedSort(ctx, obj);
        case Z3_FINITE_DOMAIN_SORT:
            return new FiniteDomainSort(ctx, obj);
        case Z3_RELATION_SORT:
            return new RelationSort(ctx, obj);
        case Z3_FLOATING_POINT_SORT:
            return new FPSort(ctx, obj);
        case Z3_ROUNDING_MODE_SORT:
            return new FPRMSort(ctx, obj);
        case Z3_SEQ_SORT:
            return new SeqSort(ctx, obj);
        case Z3_RE_SORT:
            return new ReSort(ctx, obj);
        default:
            throw new Z3Exception("Unknown sort kind");
        }
    }
}
