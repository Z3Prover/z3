/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    UserPropagator.cs

Abstract:

    User Propagator plugin
    
Author:

    Nikolaj Bjorner (nbjorner) 2022-05-07
    
Notes:

// Todo: fresh, created, declare user function, register_cb, decide, 

--*/

using System;
using System.Diagnostics;
using System.Linq;
using System.Collections.Generic;
using System.Runtime.InteropServices;

namespace Microsoft.Z3
{

    using Z3_solver_callback = System.IntPtr;
    using Z3_context = System.IntPtr;
    using Z3_solver = System.IntPtr;
    using voidp = System.IntPtr;
    using Z3_ast = System.IntPtr;


    /// <summary>
    /// Propagator context for .Net
    /// </summary>        
    public class UserPropagator 
    {
        /// <summary>
        /// Delegate type for fixed callback
        /// </summary>                
	public delegate void FixedEh(Expr term, Expr value);

        /// <summary>
        /// Delegate type for equality or disequality callback
        /// </summary>                
	public delegate void EqEh(Expr term, Expr value);


	Solver solver;
	GCHandle gch;
	Z3_solver_callback callback;
	FixedEh fixed_eh;
	Action  final_eh;
	EqEh    eq_eh;
	EqEh    diseq_eh;


	static void _push(voidp ctx, Z3_solver_callback cb) {
	   var gch = GCHandle.FromIntPtr(ctx);
	   var prop = (UserPropagator)gch.Target;
	   prop.callback = cb;
	   prop.Push();
	}
	
	unsafe static void _pop(voidp ctx, Z3_solver_callback cb, uint num_scopes) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   prop.callback = cb;
	   prop.Pop(num_scopes);
	}
	
	static voidp _fresh(voidp ctx, Z3_context new_context) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   throw new Z3Exception("fresh is NYI");
	}

	static void _fixed(voidp ctx, Z3_solver_callback cb, Z3_ast _term, Z3_ast _value) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   var term = Expr.Create(prop.solver.Context, _term);
	   var value = Expr.Create(prop.solver.Context, _value);
	   prop.callback = cb;
	   prop.fixed_eh(term, value);
	}

	static void _final(voidp ctx, Z3_solver_callback cb) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   prop.callback = cb;
	   prop.final_eh();	
	}

	static void _eq(voidp ctx, Z3_solver_callback cb, Z3_ast a, Z3_ast b) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   var s = Expr.Create(prop.solver.Context, a);
	   var t = Expr.Create(prop.solver.Context, b);
	   prop.callback = cb;
	   prop.eq_eh(s, t);
	}

	static void _diseq(voidp ctx, Z3_solver_callback cb, Z3_ast a, Z3_ast b) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   var s = Expr.Create(prop.solver.Context, a);
	   var t = Expr.Create(prop.solver.Context, b);
	   prop.callback = cb;
	   prop.diseq_eh(s, t);
	}

        /// <summary>
        /// Propagator constructor from a solver class.
        /// </summary>        
        public UserPropagator(Solver s)
	{
	    gch = GCHandle.Alloc(this);
	    solver = s;
	    var cb = GCHandle.ToIntPtr(gch);
	    Native.Z3_solver_propagate_init(solver.Context.nCtx, solver.NativeObject, cb, _push, _pop, _fresh);
	}

        /// <summary>
        /// Release provate memory.
        /// </summary>            
	~UserPropagator()
	{
            gch.Free();
 	}

        /// <summary>
        /// Virtual method for push. It must be overwritten by inherited class.
	/// </summary>        
	public virtual void Push() { throw new Z3Exception("Push method should be overwritten"); }

        /// <summary>
        /// Virtual method for pop. It must be overwritten by inherited class.
	/// </summary>        
	public virtual void Pop(uint n) { throw new Z3Exception("Pop method should be overwritten"); } 

        /// <summary>
        /// Virtual method for fresh. It must be overwritten by inherited class.
	/// </summary>
	public virtual UserPropagator Fresh(Context ctx) { throw new Z3Exception("Fresh method should be overwritten"); }

        /// <summary>
        /// Declare combination of assigned expressions a conflict
	/// </summary>
	void Conflict(params Expr[] terms) {
	     Propagate(terms, solver.Context.MkFalse());
        }

        /// <summary>
        /// Propagate consequence
	/// </summary>
        void Propagate(Expr[] terms, Expr conseq) {
	     var nTerms = Z3Object.ArrayToNative(terms);
	     Native.Z3_solver_propagate_consequence(solver.Context.nCtx, this.callback, (uint)nTerms.Length, nTerms, 0u, null, null, conseq.NativeObject);
        }


        /// <summary>
        /// Set fixed callback
	/// </summary>
        public FixedEh Fixed
	{
	    set
	    {
	       this.fixed_eh = value;
	       Native.Z3_solver_propagate_fixed(solver.Context.nCtx, solver.NativeObject, _fixed);
	    }
	}

        /// <summary>
        /// Set final callback
	/// </summary>
	public Action Final
	{
	    set
	    {
	       this.final_eh = value;
	       Native.Z3_solver_propagate_final(solver.Context.nCtx, solver.NativeObject, _final);
            }
        }

        /// <summary>
        /// Set equality event callback
	/// </summary>
	public EqEh Eq
	{
           set
	   {
 	      this.eq_eh = value;
	      Native.Z3_solver_propagate_eq(solver.Context.nCtx, solver.NativeObject, _eq);
	   }
        }

        /// <summary>
        /// Set disequality event callback
	/// </summary>
	public EqEh Diseq
	{
           set
	   {
 	      this.diseq_eh = value;
	      Native.Z3_solver_propagate_diseq(solver.Context.nCtx, solver.NativeObject, _diseq);
	   }
        }

        /// <summary>
        /// Track assignments to a term
	/// </summary>
        public void Register(Expr term) {
            Native.Z3_solver_propagate_register(solver.Context.nCtx, solver.NativeObject, term.NativeObject);
        }	
    }
}
