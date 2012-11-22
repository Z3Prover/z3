/**
 * This file was automatically generated from Constructor.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Constructors are used for datatype sorts.
     **/
    public class Constructor extends Z3Object
    {
        /**
         * The number of fields of the constructor.
         **/
        public Integer NumFields()  { init();  return n; }

        /**
         * The function declaration of the constructor.
         **/
        public FuncDecl ConstructorDecl()  {
                
                init();  return mConstructorDecl; }

        /**
         * The function declaration of the tester.
         **/
        public FuncDecl TesterDecl()  {
                
                init();  return mTesterDecl; }

        /**
         * The function declarations of the accessors
         **/
        public FuncDecl[] AccessorDecls()  {
                
                init();  return mAccessorDecls; }

        /**
         * Destructor.
         **/
        protected void finalize()
        {
            Native.delConstructor(Context.nCtx, NativeObject);
        }


        private void ObjectInvariant()
        {
            
            
        }
        

        private Integer n = 0;
        private FuncDecl mTesterDecl = null;
        private FuncDecl mConstructorDecl = null;
        private FuncDecl[] mAccessorDecls = null;

        Constructor(Context ctx, Symbol name, Symbol recognizer, Symbol[] fieldNames,
                             Sort[] sorts, Integer[] sortRefs)
            { super(ctx);
            
            
            

            n = AST.ArrayLength(fieldNames);

            if (n != AST.ArrayLength(sorts))
                throw new Z3Exception("Number of field names does not match number of sorts");
            if (sortRefs != null && sortRefs.Length != n)
                throw new Z3Exception("Number of field names does not match number of sort refs");
            
            if (sortRefs == null) sortRefs = new Integer[n];

            NativeObject = Native.mkConstructor(ctx.nCtx, name.NativeObject, recognizer.NativeObject,
                                                    n,
                                                    Symbol.ArrayToNative(fieldNames),
                                                    Sort.ArrayToNative(sorts),
                                                    sortRefs);

        }

        private void init() 
        {
            
            
            

            if (mTesterDecl != null) return;
            IntPtr constructor = IntPtr.Zero;
            IntPtr tester = IntPtr.Zero;
            IntPtr[] accessors = new IntPtr[n];
            Native.queryConstructor(Context.nCtx, NativeObject, n, constructor, tester, accessors);
            mConstructorDecl = new FuncDecl(Context, constructor);
            mTesterDecl = new FuncDecl(Context, tester);
            mAccessorDecls = new FuncDecl[n];
            for (Integer i = 0; i < n; i++)
                mAccessorDecls[i] = new FuncDecl(Context, accessors[i]);
        }

    }

    /**
     * Lists of constructors
     **/
    public class ConstructorList extends Z3Object
    {
        /**
         * Destructor.
         **/
        protected void finalize()
        {         
            Native.delConstructorList(Context.nCtx, NativeObject);
        }

        ConstructorList(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }

        ConstructorList(Context ctx, Constructor[] constructors)
            { super(ctx);
            
            

            NativeObject = Native.mkConstructorList(Context.nCtx, (Integer)constructors.Length, Constructor.ArrayToNative(constructors));
        }        
    }
