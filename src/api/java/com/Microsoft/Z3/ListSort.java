/**
 * This file was automatically generated from ListSort.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * List sorts.
     **/
    public class ListSort extends Sort
    {
        /**
         * The declaration of the nil function of this list sort.
         **/
        public FuncDecl NilDecl() 
            {
                
                return nilDecl;
            }

        /**
         * The empty list.
         **/
        public Expr Nil() 
            {
                
                return nilConst;
            }

        /**
         * The declaration of the isNil function of this list sort.
         **/
        public FuncDecl IsNilDecl() 
            {
                
                return isNilDecl;
            }

        /**
         * The declaration of the cons function of this list sort.
         **/
        public FuncDecl ConsDecl() 
            {
                
                return consDecl;
            }

        /**
         * The declaration of the isCons function of this list sort.
         * 
         **/
        public FuncDecl IsConsDecl() 
            {
                
                return isConsDecl;
            }

        /**
         * The declaration of the head function of this list sort.
         **/
        public FuncDecl HeadDecl() 
            {
                
                return headDecl;
            }

        /**
         * The declaration of the tail function of this list sort.
         **/
        public FuncDecl TailDecl() 
            {
                
                return tailDecl;
            }


        private void ObjectInvariant()
        {
            
            
            
            
            
            
            
        }



        private FuncDecl nilDecl, isNilDecl, consDecl, isConsDecl, headDecl, tailDecl;
        private Expr nilConst;

        ListSort(Context ctx, Symbol name, Sort elemSort)
        { super(ctx);
            
            
            

            long inil = 0,
                   iisnil = 0,
                   icons = 0,
                   iiscons = 0,
                   ihead = 0,
                   itail = 0;

            NativeObject() = Native.mkListSort(ctx.nCtx(), name.NativeObject, elemSort.NativeObject,
                                                  inil, iisnil, icons, iiscons, ihead, itail);
            nilDecl = new FuncDecl(ctx, inil);
            isNilDecl = new FuncDecl(ctx, iisnil);
            consDecl = new FuncDecl(ctx, icons);
            isConsDecl = new FuncDecl(ctx, iiscons);
            headDecl = new FuncDecl(ctx, ihead);
            tailDecl = new FuncDecl(ctx, itail);
            nilConst = ctx.MkConst(nilDecl);
        }
    };
