/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ASTVector.cs

Abstract:

    Z3 Managed API: AST Vectors

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Vectors of ASTs.
    /// </summary>
    internal class ASTVector : Z3Object
    {
        /// <summary>
        /// The size of the vector
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_ast_vector_size(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Retrieves the i-th object in the vector.
        /// </summary>
        /// <remarks>May throw an IndexOutOfBoundsException when <paramref name="i"/> is out of range.</remarks>
        /// <param name="i">Index</param>
        /// <returns>An AST</returns>
        public AST this[uint i]
        {
            get
            {
                Contract.Ensures(Contract.Result<AST>() != null);

                return new AST(Context, Native.Z3_ast_vector_get(Context.nCtx, NativeObject, i));
            }
            set
            {
                Contract.Requires(value != null);

                Native.Z3_ast_vector_set(Context.nCtx, NativeObject, i, value.NativeObject);
            }
        }

        /// <summary>
        /// Resize the vector to <paramref name="newSize"/>.
        /// </summary>
        /// <param name="newSize">The new size of the vector.</param>
        public void Resize(uint newSize)
        {
            Native.Z3_ast_vector_resize(Context.nCtx, NativeObject, newSize);
        }

        /// <summary>
        /// Add the AST <paramref name="a"/> to the back of the vector. The size
        /// is increased by 1.
        /// </summary>
        /// <param name="a">An AST</param>
        public void Push(AST a)
        {
            Contract.Requires(a != null);

            Native.Z3_ast_vector_push(Context.nCtx, NativeObject, a.NativeObject);
        }

        /// <summary>
        /// Translates all ASTs in the vector to <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A new ASTVector</returns>
        public ASTVector Translate(Context ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<ASTVector>() != null);

            return new ASTVector(Context, Native.Z3_ast_vector_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /// <summary>
        /// Retrieves a string representation of the vector. 
        /// </summary>    
        public override string ToString()
        {
            return Native.Z3_ast_vector_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal ASTVector(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        internal ASTVector(Context ctx) : base(ctx, Native.Z3_mk_ast_vector(ctx.nCtx)) { Contract.Requires(ctx != null); }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_ast_vector_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_ast_vector_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.ASTVector_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.ASTVector_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
