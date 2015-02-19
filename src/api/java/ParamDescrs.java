/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ParamDescrs.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_param_kind;

/**
 * A ParamDescrs describes a set of parameters.
 **/
public class ParamDescrs extends Z3Object
{
    /**
     * validate a set of parameters.
     **/
    public void validate(Params p) throws Z3Exception
    {

        Native.paramsValidate(getContext().nCtx(), p.getNativeObject(),
                getNativeObject());
    }

    /**
     * Retrieve kind of parameter.
     **/
    public Z3_param_kind getKind(Symbol name) throws Z3Exception
    {

        return Z3_param_kind.fromInt(Native.paramDescrsGetKind(
                getContext().nCtx(), getNativeObject(), name.getNativeObject()));
    }

    /**
     * Retrieve all names of parameters.
     * 
     * @throws Z3Exception
     **/
    public Symbol[] getNames() throws Z3Exception
    {
        int sz = Native.paramDescrsSize(getContext().nCtx(), getNativeObject());
        Symbol[] names = new Symbol[sz];
        for (int i = 0; i < sz; ++i)
        {
            names[i] = Symbol.create(getContext(), Native.paramDescrsGetName(
                    getContext().nCtx(), getNativeObject(), i));
        }
        return names;
    }

    /**
     * The size of the ParamDescrs.
     **/
    public int size() throws Z3Exception
    {
        return Native.paramDescrsSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieves a string representation of the ParamDescrs.
     **/
    public String toString()
    {
        try
        {
            return Native.paramDescrsToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    ParamDescrs(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().getParamDescrsDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().getParamDescrsDRQ().add(o);
        super.decRef(o);
    }
}
