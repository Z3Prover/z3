/**
 * This file was automatically generated from Sort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * The Sort class implements type information for ASTs.
     **/
    public class Sort extends AST
    {
        /**
         * Comparison operator.
         * <param name="a">A Sort</param>
         * <param name="b">A Sort</param>
         * @return True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
         * and represent the same sort; false otherwise.
         **/
         /* Overloaded operators are not translated. */

        /**
         * Comparison operator.
         * <param name="a">A Sort</param>
         * <param name="b">A Sort</param>
         * @return True if <paramref name="a"/> and <paramref name="b"/> are not from the same context 
         * or represent different sorts; false otherwise.
         **/
         /* Overloaded operators are not translated. */

        /**
         * Equality operator for objects of type Sort.
         * <param name="o"></param>
         * @return 
         **/
        public boolean Equals(Object o)
        {
            Sort casted = (Sort) o;
            if (casted == null) return false;
            return this == casted;
        }

        /**
         * Hash code generation for Sorts
         * @return A hash code
         **/
        public int GetHashCode()
        {
            return super.GetHashCode();
        }

        /**
         * Returns a unique identifier for the sort.
         **/
            public int Id()  { return Native.getSortId(Context().nCtx(), NativeObject()); }

        /**
         * The kind of the sort.
         **/
        public Z3_sort_kind SortKind()  { return Z3_sort_kind.fromInt(Native.getSortKind(Context().nCtx(), NativeObject())); }

        /**
         * The name of the sort
         **/
        public Symbol Name() 
            {
                
                return Symbol.Create(Context(), Native.getSortName(Context().nCtx(), NativeObject()));
            }

        /**
         * A string representation of the sort.
         **/
        public String toString()
        {
            return Native.sortToString(Context().nCtx(), NativeObject());
        }

        /**
         * Sort constructor
         **/
    protected Sort(Context ctx) { super(ctx); {  }}
    Sort(Context ctx, long obj) { super(ctx, obj); {  }}

        void CheckNativeObject(long obj)
        {
            if (Native.getAstKind(Context().nCtx(), obj) != Z3_ast_kind.Z3_SORT_AST.toInt())
                throw new Z3Exception("Underlying object is not a sort");
            super.CheckNativeObject(obj);
        }

        static Sort Create(Context ctx, long obj)
        {
            
            

            switch (Z3_sort_kind.fromInt(Native.getSortKind(ctx.nCtx(), obj)))
            {
                case Z3_ARRAY_SORT: return new ArraySort(ctx, obj);
                case Z3_BOOL_SORT: return new BoolSort(ctx, obj);
                case Z3_BV_SORT: return new BitVecSort(ctx, obj);
                case Z3_DATATYPE_SORT: return new DatatypeSort(ctx, obj);
                case Z3_INT_SORT: return new IntSort(ctx, obj);
                case Z3_REAL_SORT: return new RealSort(ctx, obj);
                case Z3_UNINTERPRETED_SORT: return new UninterpretedSort(ctx, obj);
                case Z3_FINITE_DOMAIN_SORT: return new FiniteDomainSort(ctx, obj);
                case Z3_RELATION_SORT: return new RelationSort(ctx, obj);
                default:
                    throw new Z3Exception("Unknown sort kind");
            }
        }
    }    
