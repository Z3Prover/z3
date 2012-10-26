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

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Constructors are used for datatype sorts.
    /// </summary>
    [ContractVerification(true)]
    public class Constructor : Z3Object
    {
        /// <summary>
        /// The number of fields of the constructor.
        /// </summary>
        public uint NumFields
        {
            get { init();  return n; }
        }

        /// <summary>
        /// The function declaration of the constructor.
        /// </summary>
        public FuncDecl ConstructorDecl
        {
            get {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                init();  return m_constructorDecl; }
        }

        /// <summary>
        /// The function declaration of the tester.
        /// </summary>
        public FuncDecl TesterDecl
        {
            get {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                init();  return m_testerDecl; }
        }

        /// <summary>
        /// The function declarations of the accessors
        /// </summary>
        public FuncDecl[] AccessorDecls
        {
            get {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);
                init();  return m_accessorDecls; }
        }        

        /// <summary>
        /// Destructor.
        /// </summary>
        ~Constructor()
        {
            Native.Z3_del_constructor(Context.nCtx, NativeObject);
        }

        #region Object invariant

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(m_testerDecl  == null || m_constructorDecl != null);
            Contract.Invariant(m_testerDecl == null || m_accessorDecls != null);
        }
        
        #endregion

        #region Internal
        readonly private uint n = 0;
        private FuncDecl m_testerDecl = null;
        private FuncDecl m_constructorDecl = null;
        private FuncDecl[] m_accessorDecls = null;

        internal Constructor(Context ctx, Symbol name, Symbol recognizer, Symbol[] fieldNames,
                             Sort[] sorts, uint[] sortRefs)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(recognizer != null);

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

        private void init() 
        {
            Contract.Ensures(m_constructorDecl != null);
            Contract.Ensures(m_testerDecl != null);
            Contract.Ensures(m_accessorDecls != null);

            if (m_testerDecl != null) return;
            IntPtr constructor = IntPtr.Zero;
            IntPtr tester = IntPtr.Zero;
            IntPtr[] accessors = new IntPtr[n];
            Native.Z3_query_constructor(Context.nCtx, NativeObject, n, ref constructor, ref tester, accessors);
            m_constructorDecl = new FuncDecl(Context, constructor);
            m_testerDecl = new FuncDecl(Context, tester);
            m_accessorDecls = new FuncDecl[n];
            for (uint i = 0; i < n; i++)
                m_accessorDecls[i] = new FuncDecl(Context, accessors[i]);
        }

        #endregion
    }

    /// <summary>
    /// Lists of constructors
    /// </summary>
    public class ConstructorList : Z3Object
    {
        /// <summary>
        /// Destructor.
        /// </summary>
        ~ConstructorList()
        {         
            Native.Z3_del_constructor_list(Context.nCtx, NativeObject);
        }

        #region Internal
        internal ConstructorList(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }

        internal ConstructorList(Context ctx, Constructor[] constructors)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(constructors != null);

            NativeObject = Native.Z3_mk_constructor_list(Context.nCtx, (uint)constructors.Length, Constructor.ArrayToNative(constructors));
        }        
        #endregion
    }
}
