/**
 * This file was automatically generated from EnumSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Enumeration sorts.
     **/
    public class EnumSort extends Sort
    {
        /**
         * The function declarations of the constants in the enumeration.
         **/
        public FuncDecl[] ConstDecls() 
            {
                

                return _constdecls;
            }

        /**
         * The constants in the enumeration.
         **/
        public Expr[] Consts() 
            {
                

                return _consts;
            }

        /**
         * The test predicates for the constants in the enumeration.
         **/
        public FuncDecl[] TesterDecls() 
            {
                

                return _testerdecls;
            }


        private void ObjectInvariant()
        {
            
            
            
        }



        private FuncDecl[] _constdecls = null, _testerdecls = null;
        private Expr[] _consts = null;

        EnumSort(Context ctx, Symbol name, Symbol[] enumNames)
        { super(ctx);
            
            
            

            int n = enumNames.Length;
            long[] n_constdecls = new long[n];
            long[] n_testers = new long[n];
            NativeObject() = Native.mkEnumerationSort(ctx.nCtx(), name.NativeObject, (long)n,
                                                         Symbol.ArrayToNative(enumNames), n_constdecls, n_testers);
            _constdecls = new FuncDecl[n];
            for (long i; i < n; i++)
                _constdecls[i] = new FuncDecl(ctx, n_constdecls[i]);
            _testerdecls = new FuncDecl[n];
            for (long i; i < n; i++)
                _testerdecls[i] = new FuncDecl(ctx, n_testers[i]);
            _consts = new Expr[n];
            for (long i; i < n; i++)
                _consts[i] = ctx.MkApp(_constdecls[i]);
        }
    };
