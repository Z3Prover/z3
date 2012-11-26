/**
 * This file was automatically generated from IntSymbol.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */
/* using System.Runtime.InteropServices; */

    /**
     * Numbered symbols
     **/
    public class IntSymbol extends Symbol
    {
        /**
         * The int value of the symbol.
         * <remarks>Throws an exception if the symbol is not of int kind. </remarks>
         **/
        public int Int() 
            {
                if (!IsIntSymbol())
                    throw new Z3Exception("Int requested from non-Int symbol");
                return Native.getSymbolInt(Context().nCtx(), NativeObject());
            }

        IntSymbol(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        IntSymbol(Context ctx, int i)
        { super(ctx, Native.mkIntSymbol(ctx.nCtx(), i));
            
        }

        void CheckNativeObject(long obj)
        {
            if ((Z3_symbol_kind)Native.getSymbolKind(Context().nCtx(), obj) != Z3_symbol_kind.Z3_INT_SYMBOL)
                throw new Z3Exception("Symbol is not of integer kind");
            super.CheckNativeObject(obj);
        }
    }
