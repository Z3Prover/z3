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
public class ParamDescrs extends Z3Object {
    /**
     * validate a set of parameters.
     **/
    public void validate(Params p)
    {

        Native.paramsValidate(getContext().nCtx(), p.getNativeObject(),
                getNativeObject());
    }

    /**
     * Retrieve kind of parameter.
     **/
    public Z3_param_kind getKind(Symbol name)
    {

        return Z3_param_kind.fromInt(Native.paramDescrsGetKind(
                getContext().nCtx(), getNativeObject(), name.getNativeObject()));
    }

    /**
     * Retrieve documentation of parameter.
     **/

     public String getDocumentation(Symbol name)
     {
	 return Native.paramDescrsGetDocumentation(getContext().nCtx(), getNativeObject(), name.getNativeObject());
     }

    /**
     * Retrieve all names of parameters.
     * 
     * @throws Z3Exception
     **/
    public Symbol[] getNames()
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
    public int size()
    {
        return Native.paramDescrsSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieves a string representation of the ParamDescrs.
     **/
    @Override
    public String toString() {
        return Native.paramDescrsToString(getContext().nCtx(), getNativeObject());
    }

    ParamDescrs(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        Native.paramDescrsIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getParamDescrsDRQ().storeReference(getContext(), this);
    }
}
