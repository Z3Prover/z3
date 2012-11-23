/**
 * This file was automatically generated from TupleSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Tuple sorts.
     **/
    public class TupleSort extends Sort
    {
        /**
         * The constructor function of the tuple.
         **/
        public FuncDecl MkDecl() 
            {
                

                return new FuncDecl(Context, Native.getTupleSortMkDecl(Context().nCtx(), NativeObject()));
            }

        /**
         * The number of fields in the tuple.
         **/
        public long NumFields()  { return Native.getTupleSortNumFields(Context().nCtx(), NativeObject()); }

        /**
         * The field declarations.
         **/
        public FuncDecl[] FieldDecls() 
            {
                

                long n = NumFields;
                FuncDecl[] res = new FuncDecl[n];
                for (long i; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.getTupleSortFieldDecl(Context().nCtx(), NativeObject(), i));
                return res;
            }

        TupleSort(Context ctx, Symbol name, long numFields, Symbol[] fieldNames, Sort[] fieldSorts)
        { super(ctx);
            
            

            long t = 0;
            NativeObject() = Native.mkTupleSort(ctx.nCtx(), name.NativeObject, numFields,
                                                   Symbol.ArrayToNative(fieldNames), AST.ArrayToNative(fieldSorts),
                                                   t, new long[numFields]);
        }
    };
