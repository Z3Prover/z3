/**
 * This file was automatically generated from ParamDescrs.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

import com.Microsoft.Z3.Enumerations.*;

/**
 * A ParamDescrs describes a set of parameters.
 **/
public class ParamDescrs extends Z3Object
{
    /**
     * validate a set of parameters.
     **/
    public void Validate(Params p)
    {

        Native.paramsValidate(Context().nCtx(), p.NativeObject(),
                NativeObject());
    }

    /**
     * Retrieve kind of parameter.
     **/
    public Z3_param_kind GetKind(Symbol name)
    {

        return Z3_param_kind.fromInt(Native.paramDescrsGetKind(
                Context().nCtx(), NativeObject(), name.NativeObject()));
    }

    /**
     * Retrieve all names of parameters.
     * 
     * @throws Z3Exception
     **/
    public Symbol[] Names() throws Z3Exception
    {
        int sz = Native.paramDescrsSize(Context().nCtx(), NativeObject());
        Symbol[] names = new Symbol[sz];
        for (int i = 0; i < sz; ++i)
        {
            names[i] = Symbol.Create(Context(), Native.paramDescrsGetName(
                    Context().nCtx(), NativeObject(), i));
        }
        return names;
    }

    /**
     * The size of the ParamDescrs.
     **/
    public int Size()
    {
        return Native.paramDescrsSize(Context().nCtx(), NativeObject());
    }

    /**
     * Retrieves a string representation of the ParamDescrs.
     **/
    public String toString()
    {
        return Native.paramDescrsToString(Context().nCtx(), NativeObject());
    }

    ParamDescrs(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void IncRef(long o) throws Z3Exception
    {
        Context().ParamDescrs_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        Context().ParamDescrs_DRQ().Add(o);
        super.DecRef(o);
    }
}
