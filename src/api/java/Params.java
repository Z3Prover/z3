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
public class Params extends Z3Object
{
    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, boolean value) throws Z3Exception
    {
        Native.paramsSetBool(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), (value) ? true : false);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, double value) throws Z3Exception
    {
        Native.paramsSetDouble(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), value);
    }
    
    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, String value) throws Z3Exception
    {

        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), 
                getContext().mkSymbol(value).getNativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(Symbol name, Symbol value) throws Z3Exception
    {

        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(),
                name.getNativeObject(), value.getNativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, boolean value) throws Z3Exception
    {
        Native.paramsSetBool(getContext().nCtx(), getNativeObject(), 
                getContext().mkSymbol(name).getNativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, int value) throws Z3Exception
    {
        Native.paramsSetUint(getContext().nCtx(), getNativeObject(), getContext()
                .mkSymbol(name).getNativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, double value) throws Z3Exception
    {
        Native.paramsSetDouble(getContext().nCtx(), getNativeObject(), getContext()
                .mkSymbol(name).getNativeObject(), value);
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, Symbol value) throws Z3Exception
    {
        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(), getContext()
                .mkSymbol(name).getNativeObject(), value.getNativeObject());
    }

    /**
     * Adds a parameter setting.
     **/
    public void add(String name, String value) throws Z3Exception
    {

        Native.paramsSetSymbol(getContext().nCtx(), getNativeObject(),
                getContext().mkSymbol(name).getNativeObject(),
                getContext().mkSymbol(value).getNativeObject());
    }
    
    /**
     * A string representation of the parameter set.
     **/
    public String toString()
    {
        try
        {
            return Native.paramsToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    Params(Context ctx) throws Z3Exception
    {
        super(ctx, Native.mkParams(ctx.nCtx()));
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().getParamsDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().getParamsDRQ().add(o);
        super.decRef(o);
    }
}
