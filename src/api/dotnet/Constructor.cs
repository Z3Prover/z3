/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Constructor.cs

Abstract:

    Z3 Managed API: Constructors

Author:

    Christoph Wintersteiger (cwinter) 2012-03-22

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Constructors are used for datatype sorts.
    /// </summary>
    public class Constructor : Z3Object
    {
        /// <summary>
        /// The number of fields of the constructor.
        /// </summary>
        public uint NumFields
        {
            get
            {                
                return n;
            }
        }

        /// <summary>
        /// The function declaration of the constructor.
        /// </summary>
        public FuncDecl ConstructorDecl
        {
            get
            {
                IntPtr constructor = IntPtr.Zero;
                IntPtr tester = IntPtr.Zero;
                IntPtr[] accessors = new IntPtr[n];
                Native.Z3_query_constructor(Context.nCtx, NativeObject, n, ref constructor, ref tester, accessors);
                return new FuncDecl(Context, constructor);                
            }
        }

        /// <summary>
        /// The function declaration of the tester.
        /// </summary>
        public FuncDecl TesterDecl
        {
            get
            {
                IntPtr constructor = IntPtr.Zero;
                IntPtr tester = IntPtr.Zero;
                IntPtr[] accessors = new IntPtr[n];
                Native.Z3_query_constructor(Context.nCtx, NativeObject, n, ref constructor, ref tester, accessors);
                return new FuncDecl(Context, tester);                
            }
        }

        /// <summary>
        /// The function declarations of the accessors
        /// </summary>
        public FuncDecl[] AccessorDecls
        {
            get
            {
                IntPtr constructor = IntPtr.Zero;
                IntPtr tester = IntPtr.Zero;
                IntPtr[] accessors = new IntPtr[n];
                Native.Z3_query_constructor(Context.nCtx, NativeObject, n, ref constructor, ref tester, accessors);                
                FuncDecl[] t = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    t[i] = new FuncDecl(Context, accessors[i]); 
                return t;
            }
        }

        /// <summary>
        /// Destructor.
        /// </summary>
        ~Constructor()
        {
            Native.Z3_del_constructor(Context.nCtx, NativeObject);
        }        

        #region Internal
        private uint n = 0;
        
        internal Constructor(Context ctx, Symbol name, Symbol recognizer, Symbol[] fieldNames,
                             Sort[] sorts, uint[] sortRefs)
            : base(ctx)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(name != null);
            Debug.Assert(recognizer != null);

            n = AST.ArrayLength(fieldNames);

            if (n != AST.ArrayLength(sorts))
                throw new Z3Exception("Number of field names does not match number of sorts");
            if (sortRefs != null && sortRefs.Length != n)
                throw new Z3Exception("Number of field names does not match number of sort refs");

            if (sortRefs == null) sortRefs = new uint[n];

            NativeObject = Native.Z3_mk_constructor(ctx.nCtx, name.NativeObject, recognizer.NativeObject,
                                                    n,
                                                    Symbol.ArrayToNative(fieldNames),
                                                    Sort.ArrayToNative(sorts),
                                                    sortRefs);

        }

        #endregion
    }
}
