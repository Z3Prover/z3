/**
 * This file was automatically generated from Params.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
        getContext().params_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().params_DRQ().add(o);
        super.decRef(o);
    }
}
