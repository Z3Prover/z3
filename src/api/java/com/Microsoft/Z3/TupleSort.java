/**
 * This file was automatically generated from TupleSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

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
                

                return new FuncDecl(Context(), Native.getTupleSortMkDecl(Context().nCtx(), NativeObject()));
            }

        /**
         * The number of fields in the tuple.
         **/
        public int NumFields()  { return Native.getTupleSortNumFields(Context().nCtx(), NativeObject()); }

        /**
         * The field declarations.
         **/
        public FuncDecl[] FieldDecls() 
            {
                

                int n = NumFields();
                FuncDecl[] res = new FuncDecl[n];
                for (int i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context(), Native.getTupleSortFieldDecl(Context().nCtx(), NativeObject(), i));
                return res;
            }

        TupleSort(Context ctx, Symbol name, int numFields, Symbol[] fieldNames, Sort[] fieldSorts)
        { super(ctx);
            
            

            long t = 0;
            setNativeObject(Native.mkTupleSort(ctx.nCtx(), name.NativeObject(), numFields,
					       Symbol.ArrayToNative(fieldNames), AST.ArrayToNative(fieldSorts),
					       t, new long[numFields]));
        }
    };
