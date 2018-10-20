/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ASTMap.cs

Abstract:

    Z3 Managed API: AST Maps

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Map from AST to AST
    /// </summary>
    internal class ASTMap : Z3Object
    {
        /// <summary>
        /// Checks whether the map contains the key <paramref name="k"/>.
        /// </summary>
        /// <param name="k">An AST</param>
        /// <returns>True if <paramref name="k"/> is a key in the map, false otherwise.</returns>
        public bool Contains(AST k)
        {
            Debug.Assert(k != null);

            return 0 != Native.Z3_ast_map_contains(Context.nCtx, NativeObject, k.NativeObject);
        }

        /// <summary>
        /// Finds the value associated with the key <paramref name="k"/>.
        /// </summary>
        /// <remarks>
        /// This function signs an error when <paramref name="k"/> is not a key in the map.
        /// </remarks>
        /// <param name="k">An AST</param>    
        public AST Find(AST k)
        {
            Debug.Assert(k != null);

            return new AST(Context, Native.Z3_ast_map_find(Context.nCtx, NativeObject, k.NativeObject));
        }

        /// <summary>
        /// Stores or replaces a new key/value pair in the map.
        /// </summary>
        /// <param name="k">The key AST</param>
        /// <param name="v">The value AST</param>
        public void Insert(AST k, AST v)
        {
            Debug.Assert(k != null);
            Debug.Assert(v != null);

            Native.Z3_ast_map_insert(Context.nCtx, NativeObject, k.NativeObject, v.NativeObject);
        }

        /// <summary>
        /// Erases the key <paramref name="k"/> from the map.
        /// </summary>
        /// <param name="k">An AST</param>
        public void Erase(AST k)
        {
            Debug.Assert(k != null);

            Native.Z3_ast_map_erase(Context.nCtx, NativeObject, k.NativeObject);
        }

        /// <summary>
        /// Removes all keys from the map.
        /// </summary>
        public void Reset()
        {
            Native.Z3_ast_map_reset(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// The size of the map
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_ast_map_size(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The keys stored in the map.
        /// </summary>
        public AST[] Keys
        {
            get
            {
                ASTVector res = new ASTVector(Context, Native.Z3_ast_map_keys(Context.nCtx, NativeObject));
                return res.ToArray();
            }
        }

        /// <summary>
        /// Retrieves a string representation of the map. 
        /// </summary>    
        public override string ToString()
        {
            return Native.Z3_ast_map_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal ASTMap(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal ASTMap(Context ctx)
            : base(ctx, Native.Z3_mk_ast_map(ctx.nCtx))
        {
            Debug.Assert(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_ast_map_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_ast_map_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.ASTMap_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.ASTMap_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
