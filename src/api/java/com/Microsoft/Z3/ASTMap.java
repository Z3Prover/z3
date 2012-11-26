/**
 * This file was automatically generated from ASTMap.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

    /**
     * Map from AST to AST
     **/
    class ASTMap extends Z3Object
    {
        /**
         * Checks whether the map contains the key <paramref name="k"/>.
         * <param name="k">An AST</param>
         * @return True if <paramref name="k"/> is a key in the map, false otherwise.
         **/
        public boolean Contains(AST k)
        {
            

            return Native.astMapContains(Context().nCtx(), NativeObject(), k.NativeObject()) ;
        }

        /**
         * Finds the value associated with the key <paramref name="k"/>.
         * <remarks>
         * This function signs an error when <paramref name="k"/> is not a key in the map.
         * </remarks>
         * <param name="k">An AST</param>    
         **/
        public AST Find(AST k)
        {
            
            

            return new AST(Context(), Native.astMapFind(Context().nCtx(), NativeObject(), k.NativeObject()));
        }

        /**
         * Stores or replaces a new key/value pair in the map.
         * <param name="k">The key AST</param>
         * <param name="v">The value AST</param>
         **/
        public void Insert(AST k, AST v)
        {
            
            

            Native.astMapInsert(Context().nCtx(), NativeObject(), k.NativeObject(), v.NativeObject());
        }

        /**
         * Erases the key <paramref name="k"/> from the map.
         * <param name="k">An AST</param>
         **/
        public void Erase(AST k)
        {
            

            Native.astMapErase(Context().nCtx(), NativeObject(), k.NativeObject());
        }

        /**
         * Removes all keys from the map.
         **/
        public void Reset()
        {
            Native.astMapReset(Context().nCtx(), NativeObject());
        }

        /**
         * The size of the map
         **/
        public int Size()  { return Native.astMapSize(Context().nCtx(), NativeObject()); }

        /**
         * The keys stored in the map.
         **/
        public ASTVector Keys() 
            {
                return new ASTVector(Context(), Native.astMapKeys(Context().nCtx(), NativeObject()));
            }

        /**
         * Retrieves a string representation of the map. 
         **/
        public String toString()
        {
            return Native.astMapToString(Context().nCtx(), NativeObject());
        }

        ASTMap(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        ASTMap(Context ctx)
        { super(ctx, Native.mkAstMap(ctx.nCtx()));
            
        }

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.astMapIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.astMapDecRef(ctx.nCtx(), obj);
            }
        };

        void IncRef(long o)
        {
            Context().ASTMap_DRQ().IncAndClear(Context(), o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context().ASTMap_DRQ().Add(o);
            super.DecRef(o);
        }
    }
