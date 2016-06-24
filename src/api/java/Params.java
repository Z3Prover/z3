/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Params.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 


package com.microsoft.z3;

/**
 * A ParameterSet represents a configuration in the form of Symbol/value pairs.
 **/
public class Params extends Z3Object {
    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, boolean value)
    {
        Native.paramsSetBool(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), (value));
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, double value)
    {
        Native.paramsSetDouble(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), value);
    }
    
    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, String value)
    {

        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), 
                getContext().mkSymbol(value).getNativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, Symbol value)
    {

        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), value.getNativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, boolean value)
    {
        Native.paramsSetBool(getContext().nCtx(), getNativeObject(), 
                getContext().mkSymbol(name).getNativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, int value)
    {
        Native.paramsSetUint(getContext().nCtx(), getNativeObject(), getContext()
                .mkSymbol(name).getNativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, double value)
    {
        Native.paramsSetDouble(getContext().nCtx(), getNativeObject(), getContext()
                .mkSymbol(name).getNativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, Symbol value)
    {
        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(), getContext()
                .mkSymbol(name).getNativeObject(), value.getNativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, String value)
    {

        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(),
                getContext().mkSymbol(name).getNativeObject(),
                getContext().mkSymbol(value).getNativeObject());
    }
    
    /**
     * A string representation of the parameter set.
     **/
    @Override
    public String toString()
    {
        return Native.paramsToString(getContext().nCtx(), getNativeObject());
    }

    Params(Context ctx)
    {
        super(ctx, Native.mkParams(ctx.nCtx()));
    }


    @Override
    void incRef() {
        Native.paramsIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getParamsDRQ().storeReference(getContext(), this);
    }
}
