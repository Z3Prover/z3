/**
 * This file was automatically generated from ConstructorList.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */
/* using System.Collections.Generic; */
/* using System.Linq; */
/* using System.Text; */


    /**
     * Lists of constructors
     **/
    public class ConstructorList extends Z3Object
    {
        /**
         * Destructor.
         **/
        protected void finalize()
        {
            Native.delConstructorList(Context().nCtx(), NativeObject());
        }

        ConstructorList(Context ctx, long obj)
        { super(ctx, obj);
            
        }

        ConstructorList(Context ctx, Constructor[] constructors)
        { super(ctx);
            
            

            setNativeObject(Native.mkConstructorList(Context().nCtx(), (long)constructors.Length, Constructor.ArrayToNative(constructors)));
        }
    }
