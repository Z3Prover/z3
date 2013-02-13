/**
 * This file was automatically generated from Sort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
     * Comparison operator. <param name="a">A Sort</param> <param name="b">A
     * Sort</param>
     * 
     * @return True if <paramref name="a"/> and <paramref name="b"/> are from
     *         the same context and represent the same sort; false otherwise.
     **/
    /* Overloaded operators are not translated. */

    /**
     * Comparison operator. <param name="a">A Sort</param> <param name="b">A
     * Sort</param>
     * 
     * @return True if <paramref name="a"/> and <paramref name="b"/> are not
     *         from the same context or represent different sorts; false
     *         otherwise.
     **/
    /* Overloaded operators are not translated. */

    /**
     * Equality operator for objects of type Sort. <param name="o"></param>
     * 
     * @return
     **/
    public boolean equals(Object o)
    {
        Sort casted = null;

	try {
	    casted = Sort.class.cast(o);
	} catch (ClassCastException e) {
	    return false;
	}

	return this.getNativeObject() == casted.getNativeObject();
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
    public int getId() throws Z3Exception
    {
        return Native.getSortId(getContext().nCtx(), getNativeObject());
    }

    /**
     * The kind of the sort.
     **/
    public Z3_sort_kind getSortKind() throws Z3Exception
    {
        return Z3_sort_kind.fromInt(Native.getSortKind(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * The name of the sort
     **/
    public Symbol getName() throws Z3Exception
    {
        return Symbol.create(getContext(),
                Native.getSortName(getContext().nCtx(), getNativeObject()));
    }

    /**
     * A string representation of the sort.
     **/
    public String toString()
    {
        try
        {
            return Native.sortToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    /**
     * Sort constructor
     **/
    protected Sort(Context ctx) throws Z3Exception
    {
        super(ctx);
        {
        }
    }

    Sort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
        {
        }
    }

    void checkNativeObject(long obj) throws Z3Exception
    {
        if (Native.getAstKind(getContext().nCtx(), obj) != Z3_ast_kind.Z3_SORT_AST
                .toInt())
            throw new Z3Exception("Underlying object is not a sort");
        super.checkNativeObject(obj);
    }

    static Sort create(Context ctx, long obj) throws Z3Exception
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
        default:
            throw new Z3Exception("Unknown sort kind");
        }
    }
}
