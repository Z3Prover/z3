/**
 * This file was automatically generated from Constructor.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Constructors are used for datatype sorts.
     **/
    public class Constructor extends Z3Object
    {
        /**
         * The number of fields of the constructor.
         **/
        public long NumFields() 
            {
                init();
                return n;
            }

        /**
         * The function declaration of the constructor.
         **/
        public FuncDecl ConstructorDecl() 
            {
                
                init();
                return m_constructorDecl;
            }

        /**
         * The function declaration of the tester.
         **/
        public FuncDecl TesterDecl() 
            {
                
                init();
                return m_testerDecl;
            }

        /**
         * The function declarations of the accessors
         **/
        public FuncDecl[] AccessorDecls() 
            {
                
                init(); 
                return m_accessorDecls;
            }

        /**
         * Destructor.
         **/
        protected void finalize()
        {
            Native.delConstructor(Context().nCtx(), NativeObject());
        }


        private void ObjectInvariant()
        {
            
            
        }


        private long n = 0;
        private FuncDecl m_testerDecl = null;
        private FuncDecl m_constructorDecl = null;
        private FuncDecl[] m_accessorDecls = null;

        Constructor(Context ctx, Symbol name, Symbol recognizer, Symbol[] fieldNames,
                             Sort[] sorts, long[] sortRefs)
        { super(ctx);
            
            
            

            n = AST.ArrayLength(fieldNames);

            if (n != AST.ArrayLength(sorts))
                throw new Z3Exception("Number of field names does not match number of sorts");
            if (sortRefs != null && sortRefs.Length != n)
                throw new Z3Exception("Number of field names does not match number of sort refs");

            if (sortRefs == null) sortRefs = new long[n];

            NativeObject() = Native.mkConstructor(ctx.nCtx(), name.NativeObject, recognizer.NativeObject,
                                                    n,
                                                    Symbol.ArrayToNative(fieldNames),
                                                    Sort.ArrayToNative(sorts),
                                                    sortRefs);

        }

        private void init()
        {
            
            
            

            if (m_testerDecl != null) return;
            long constructor = 0;
            long tester = 0;
            long[] accessors = new long[n];
            Native.queryConstructor(Context().nCtx(), NativeObject(), n, constructor, tester, accessors);
            m_constructorDecl = new FuncDecl(Context, constructor);
            m_testerDecl = new FuncDecl(Context, tester);
            m_accessorDecls = new FuncDecl[n];
            for (long i; i < n; i++)
                m_accessorDecls[i] = new FuncDecl(Context, accessors[i]);
        }

    }
