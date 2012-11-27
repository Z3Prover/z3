/**
 * This file was automatically generated from DatatypeSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * Datatype sorts.
     **/
    public class DatatypeSort extends Sort
    {
        /**
         * The number of constructors of the datatype sort.
         **/
        public int NumConstructors()  { return Native.getDatatypeSortNumConstructors(Context().nCtx(), NativeObject()); }

        /**
         * The constructors.
         **/
        public FuncDecl[] Constructors() 
            {
                

                int n = NumConstructors();
                FuncDecl[] res = new FuncDecl[n];
                for (int i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context(), Native.getDatatypeSortConstructor(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The recognizers.
         **/
        public FuncDecl[] Recognizers() 
            {
                

                int n = NumConstructors();
                FuncDecl[] res = new FuncDecl[n];
                for (int i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context(), Native.getDatatypeSortRecognizer(Context().nCtx(), NativeObject(), i));
                return res;
            }

        /**
         * The constructor accessors.
         **/
        public FuncDecl[][] Accessors() 
            {
                

                int n = NumConstructors();
                FuncDecl[][] res = new FuncDecl[n][];
                for (int i = 0; i < n; i++)
                {
                    FuncDecl fd = new FuncDecl(Context(), Native.getDatatypeSortConstructor(Context().nCtx(), NativeObject(), i));
                    int ds = fd.DomainSize();
                    FuncDecl[] tmp = new FuncDecl[ds];
                    for (int j = 0; j < ds; j++)
                        tmp[j] = new FuncDecl(Context(), Native.getDatatypeSortConstructorAccessor(Context().nCtx(), NativeObject(), i, j));
                    res[i] = tmp;
                }
                return res;
        }

    DatatypeSort(Context ctx, long obj) { super(ctx, obj); {  }}

        DatatypeSort(Context ctx, Symbol name, Constructor[] constructors)
        { super(ctx, Native.mkDatatype(ctx.nCtx(), name.NativeObject(), (int)constructors.length, ArrayToNative(constructors)));
            
            
            
        }
    };
