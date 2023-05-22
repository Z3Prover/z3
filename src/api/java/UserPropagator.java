/**
Copyright (c) 2023 Microsoft Corporation

Module Name:

    UserPropagator.java

Abstract:

    User Propagator plugin
    
**/


package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_lbool;
import java.util.*;

/**
 * User Propagator
 **/
@SuppressWarnings("unchecked")
public class UserPropagator implements AutoCloseable {

    Solver solver;
    Context ctx;
    
    /**
     * Create a UserPropagator from a solver.
     **/
    public UserPropagator(Solver s)
    {
	this.solver = s;
    }

    /**
     * Create a UserPropagator from a context.
     **/
    public UserPropagator(Context _ctx)
    {
	this.ctx = _ctx;
    }

    /**
     * Disposes of the propagator.
     **/
    @Override
    public void close()
    {
	this.solver = null;
	this.ctx = null;
    }
}

