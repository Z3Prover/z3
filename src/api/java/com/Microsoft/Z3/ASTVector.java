/**
 * This file was automatically generated from ASTVector.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Vectors of ASTs.
     **/
    class ASTVector extends Z3Object
    {
        /**
         * The size of the vector
         **/
        public Integer Size()  { return Native.astVectorSize(Context.nCtx, NativeObject); }

        /**
         * Retrieves the i-th object in the vector.
         * <remarks>May throw an IndexOutOfBoundsException when <paramref name="i"/> is out of range.</remarks>
         * <param name="i">Index</param>
         * @return An AST
         **/
        public AST this[Integer i]() 
            {
                

                return new AST(Context, Native.astVectorGet(Context.nCtx, NativeObject, i));
            set
            {
                

                Native.astVectorSet(Context.nCtx, NativeObject, i, value.NativeObject);
            }
        }

        /**
         * Resize the vector to <paramref name="newSize"/>.
         * <param name="newSize">The new size of the vector.</param>
         **/
        public void Resize(Integer newSize)
        {
            Native.astVectorResize(Context.nCtx, NativeObject, newSize);
        }

        /**
         * Add the AST <paramref name="a"/> to the back of the vector. The size
         * is increased by 1.
         * <param name="a">An AST</param>
         **/
        public void Push(AST a)
        {
            

            Native.astVectorPush(Context.nCtx, NativeObject, a.NativeObject);
        }

        /**
         * Translates all ASTs in the vector to <paramref name="ctx"/>.
         * <param name="ctx">A context</param>
         * @return A new ASTVector
         **/
        public ASTVector Translate(Context ctx)
        {
            
            

            return new ASTVector(Context, Native.astVectorTranslate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /**
         * Retrieves a string representation of the vector. 
         **/
        public String toString()
        {
            return Native.astVectortoString(Context.nCtx, NativeObject);
        }

        ASTVector(Context ctx, IntPtr obj) { super(ctx, obj);  }
        ASTVector(Context ctx) { super(ctx, Native.mkAstVector(ctx.nCtx));  }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.astVectorIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.astVectorDecRef(ctx.nCtx, obj);
            }
        };

        void IncRef(IntPtr o)
        {
            Context.ASTVectorDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.ASTVectorDRQ.Add(o);
            super.DecRef(o);
        }
    }
