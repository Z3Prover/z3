/**
 * This file was automatically generated from ASTVector.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * Vectors of ASTs.
     **/
    class ASTVector extends Z3Object
    {
        /**
         * The size of the vector
         **/
        public int Size()  { return Native.astVectorSize(Context().nCtx(), NativeObject()); }

        /**
         * Retrieves the i-th object in the vector.
         * <remarks>May throw an IndexOutOfBoundsException when <paramref name="i"/> is out of range.</remarks>
         * <param name="i">Index</param>
         * @return An AST
         **/
        public AST get(int i) 
            {
                

                return new AST(Context(), Native.astVectorGet(Context().nCtx(), NativeObject(), i));
            }
        public void set(int i, AST value) 
            {
                

                Native.astVectorSet(Context().nCtx(), NativeObject(), i, value.NativeObject());
            }

        /**
         * Resize the vector to <paramref name="newSize"/>.
         * <param name="newSize">The new size of the vector.</param>
         **/
        public void Resize(int newSize)
        {
            Native.astVectorResize(Context().nCtx(), NativeObject(), newSize);
        }

        /**
         * Add the AST <paramref name="a"/> to the back of the vector. The size
         * is increased by 1.
         * <param name="a">An AST</param>
         **/
        public void Push(AST a)
        {
            

            Native.astVectorPush(Context().nCtx(), NativeObject(), a.NativeObject());
        }

        /**
         * Translates all ASTs in the vector to <paramref name="ctx"/>.
         * <param name="ctx">A context</param>
         * @return A new ASTVector
         **/
        public ASTVector Translate(Context ctx)
        {
            
            

            return new ASTVector(Context(), Native.astVectorTranslate(Context().nCtx(), NativeObject(), ctx.nCtx()));
        }

        /**
         * Retrieves a string representation of the vector. 
         **/
        public String toString()
        {
            return Native.astVectorToString(Context().nCtx(), NativeObject());
        }

    ASTVector(Context ctx, long obj) { super(ctx, obj); {  }}
    ASTVector(Context ctx) { super(ctx, Native.mkAstVector(ctx.nCtx())); {  }}

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.astVectorIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.astVectorDecRef(ctx.nCtx(), obj);
            }
        };

        void IncRef(long o)
        {
            Context().ASTVector_DRQ().IncAndClear(Context(), o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context().ASTVector_DRQ().Add(o);
            super.DecRef(o);
        }
    }
