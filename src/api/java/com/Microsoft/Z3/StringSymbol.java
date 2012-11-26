/**
 * This file was automatically generated from StringSymbol.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */
/* using System.Runtime.InteropServices; */


    /**
     * Named symbols
     **/
    public class StringSymbol extends Symbol
    {
        /**
         * The string value of the symbol.
         * <remarks>Throws an exception if the symbol is not of string kind.</remarks>
         **/
        public String String() 
            {
                

                if (!IsStringSymbol())
                    throw new Z3Exception("String requested from non-String symbol");
                return Native.getSymbolString(Context().nCtx(), NativeObject());
            }

        StringSymbol(Context ctx, long obj)
        { super(ctx, obj);
            
        }

        StringSymbol(Context ctx, String s)
        { super(ctx, Native.mkStringSymbol(ctx.nCtx(), s));
            
        }

        void CheckNativeObject(long obj)
        {
            if ((Z3_symbol_kind)Native.getSymbolKind(Context().nCtx(), obj) != Z3_symbol_kind.Z3_STRING_SYMBOL)
                throw new Z3Exception("Symbol is not of String kind");

            super.CheckNativeObject(obj);
        }
    }
