/**
 * This file was automatically generated from DatatypeSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Datatype sorts.
     **/
    public class DatatypeSort extends Sort
    {
        /**
         * The number of constructors of the datatype sort.
         **/
        public long NumConstructors()  { return Native.getDatatypeSortNumConstructors(Context().nCtx(), NativeObject()); }

        /**
         * The constructors.
         **/
        public FuncDecl[] Constructors() 
            {
                

                long n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (long i; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.getDatatypeSortConstructor(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The recognizers.
         **/
        public FuncDecl[] Recognizers() 
            {
                

                long n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (long i; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.getDatatypeSortRecognizer(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The constructor accessors.
         **/
        public FuncDecl[][] Accessors() 
            {
                

                long n = NumConstructors;
                FuncDecl[][] res = new FuncDecl[n][];
                for (long i; i < n; i++)
                {
                    FuncDecl fd = new FuncDecl(Context, Native.getDatatypeSortConstructor(Context().nCtx(), NativeObject(), i));
                    long ds = fd.DomainSize;
                    FuncDecl[] tmp = new FuncDecl[ds];
                    for (long j; j < ds; j++)
                        tmp[j] = new FuncDecl(Context, Native.getDatatypeSortConstructorAccessor(Context().nCtx(), NativeObject(), i, j));
                    res[i] = tmp;
                }
                return res;
        }

    DatatypeSort(Context ctx, long obj) { super(ctx, obj); {  }}

        DatatypeSort(Context ctx, Symbol name, Constructor[] constructors)
        { super(ctx, Native.mkDatatype(ctx.nCtx(), name.NativeObject, (long)constructors.Length, ArrayToNative(constructors)));
            
            
            
        }
    };
