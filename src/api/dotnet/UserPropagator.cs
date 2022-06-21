/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    UserPropagator.cs

Abstract:

    User Propagator plugin
    
Author:

    Nikolaj Bjorner (nbjorner) 2022-05-07
    
Notes:


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

        /// <summary>
        /// Delegate type for when a new term using a registered function symbol is created internally
        /// </summary>                
	public delegate void CreatedEh(Expr term);

        /// <summary>
        /// Delegate type for callback into solver's branching
	/// <param name="term">A bit-vector or Boolean used for branching</param>
	/// <param name="idx">If the term is a bit-vector, then an index into the bit-vector being branched on</param>
	/// <param name="phase">Set phase to -1 (false) or 1 (true) to override solver's phase</param>
	/// </summary>                
	public delegate void DecideEh(ref Expr term, ref uint idx, ref int phase);

	Solver solver;
	Context  ctx;
	GCHandle gch;
	Z3_solver_callback callback = IntPtr.Zero;
	FixedEh fixed_eh;
	Action  final_eh;
	EqEh    eq_eh;
	EqEh    diseq_eh;
	CreatedEh created_eh;
	DecideEh  decide_eh;

	void Callback(Action fn, Z3_solver_callback cb) {
	    this.callback = cb;
	    try {	    
	        fn();
	    }
	    catch {
	        // TBD: add debug log or exception handler		
	    }
	    finally {
	       this.callback = IntPtr.Zero;
	    }
	}


	static void _push(voidp ctx, Z3_solver_callback cb) {
	   var gch = GCHandle.FromIntPtr(ctx);
	   var prop = (UserPropagator)gch.Target;
	   prop.Callback(() => prop.Push(), cb);
	}
	
	static void _pop(voidp ctx, Z3_solver_callback cb, uint num_scopes) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   prop.Callback(() => prop.Pop(num_scopes), cb);
	}
	
	static voidp _fresh(voidp _ctx, Z3_context new_context) {
	   var gch = GCHandle.FromIntPtr(_ctx);
           var prop = (UserPropagator)gch.Target;
           var ctx = new Context(new_context);
           var prop1 = prop.Fresh(ctx);
           return GCHandle.ToIntPtr(prop1.gch);
	}

	static void _fixed(voidp ctx, Z3_solver_callback cb, Z3_ast _term, Z3_ast _value) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   using var term = Expr.Create(prop.ctx, _term);
	   using var value = Expr.Create(prop.ctx, _value);
	   prop.Callback(() => prop.fixed_eh(term, value), cb);
	}

	static void _final(voidp ctx, Z3_solver_callback cb) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   prop.Callback(() => prop.final_eh(), cb);
	}

	static void _eq(voidp ctx, Z3_solver_callback cb, Z3_ast a, Z3_ast b) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   using var s = Expr.Create(prop.ctx, a);
	   using var t = Expr.Create(prop.ctx, b);
	   prop.Callback(() => prop.eq_eh(s, t), cb);
	}

	static void _diseq(voidp ctx, Z3_solver_callback cb, Z3_ast a, Z3_ast b) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   using var s = Expr.Create(prop.ctx, a);
	   using var t = Expr.Create(prop.ctx, b);
	   prop.Callback(() => prop.diseq_eh(s, t), cb);
	}

	static void _created(voidp ctx, Z3_solver_callback cb, Z3_ast a) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   using var t = Expr.Create(prop.ctx, a);
	   prop.Callback(() => prop.created_eh(t), cb);
	}

	static void _decide(voidp ctx, Z3_solver_callback cb, ref Z3_ast a, ref uint idx, ref int phase) {
	   var gch = GCHandle.FromIntPtr(ctx);
           var prop = (UserPropagator)gch.Target;
	   var t = Expr.Create(prop.ctx, a);
	   var u = t;
	   prop.callback = cb;
	   prop.decide_eh(ref t, ref idx, ref phase);
	   prop.callback = IntPtr.Zero;
	   if (u != t) 
	       a = t.NativeObject;
	}

        /// <summary>
        /// Propagator constructor from a solver class.
        /// </summary>        
        public UserPropagator(Solver s)
	{
	    gch = GCHandle.Alloc(this);
	    solver = s;
	    ctx = solver.Context;
	    var cb = GCHandle.ToIntPtr(gch);
	    Native.Z3_solver_propagate_init(ctx.nCtx, solver.NativeObject, cb, _push, _pop, _fresh);
	}

        /// <summary>
        /// Propagator constructor from a context. It is used from inside of Fresh.
        /// </summary>        
        public UserPropagator(Context _ctx)
	{
	    gch = GCHandle.Alloc(this);
            solver = null;
	    ctx = _ctx;
	}

        /// <summary>
        /// Release provate memory.
        /// </summary>            
	~UserPropagator()
	{
            if (gch != null)
                gch.Free();
            if (solver == null)
                ctx.Dispose();
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
        /// Virtual method for fresh. It can be overwritten by inherited class.
	/// </summary>
	public virtual UserPropagator Fresh(Context ctx) { return new UserPropagator(ctx); }

        /// <summary>
        /// Declare combination of assigned expressions a conflict
	/// </summary>
	void Conflict(params Expr[] terms) {
	     Propagate(terms, ctx.MkFalse());
        }

        /// <summary>
        /// Propagate consequence
	/// </summary>
        void Propagate(Expr[] terms, Expr conseq) {
	     var nTerms = Z3Object.ArrayToNative(terms);
	     Native.Z3_solver_propagate_consequence(ctx.nCtx, this.callback, (uint)nTerms.Length, nTerms, 0u, null, null, conseq.NativeObject);
        }


        /// <summary>
        /// Set fixed callback
	/// </summary>
        public FixedEh Fixed
	{
	    set
	    {
	       this.fixed_eh = value;
               if (solver != null)
                   Native.Z3_solver_propagate_fixed(ctx.nCtx, solver.NativeObject, _fixed);
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
               if (solver != null)
 	          Native.Z3_solver_propagate_final(ctx.nCtx, solver.NativeObject, _final);
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
              if (solver != null)
  	         Native.Z3_solver_propagate_eq(ctx.nCtx, solver.NativeObject, _eq);
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
              if (solver != null)
                 Native.Z3_solver_propagate_diseq(ctx.nCtx, solver.NativeObject, _diseq);
	   }
        }

        /// <summary>
        /// Set created callback
	/// </summary>
	public CreatedEh Created
	{
           set
	   {
 	      this.created_eh = value;
              if (solver != null)
                  Native.Z3_solver_propagate_created(ctx.nCtx, solver.NativeObject, _created);
	   }
        }

        /// <summary>
        /// Set decision callback
	/// </summary>
	public DecideEh Decide
	{
           set
	   {
 	      this.decide_eh = value;
              if (solver != null)
                  Native.Z3_solver_propagate_decide(ctx.nCtx, solver.NativeObject, _decide);
	   }
        }

        /// <summary>
        /// Track assignments to a term
	/// </summary>
        public void Register(Expr term) {
            if (this.callback != IntPtr.Zero) {
               Native.Z3_solver_propagate_register_cb(ctx.nCtx, callback, term.NativeObject);
            }
            else {
               Native.Z3_solver_propagate_register(ctx.nCtx, solver.NativeObject, term.NativeObject);
            }
        }	
    }
}
