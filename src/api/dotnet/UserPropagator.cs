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
    public class UserPropagator : IDisposable
    {
        /// <summary>
        /// Delegate type for fixed callback
        /// Note that the life-time of the term and value only applies within the scope of the callback.
        /// That means the term and value cannot be stored in an array, dictionary or similar and accessed after the callback has returned.
        /// Use the functionality Dup on expressions to create a duplicate copy that extends the lifetime.
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
        /// Delegate type for callback into solver's branching. The values can be overridden by calling <see cref="NextSplit" />.
        /// </summary>
        /// <param name="term">A bit-vector or Boolean used for branching</param>
        /// <param name="idx">If the term is a bit-vector, then an index into the bit-vector being branched on</param>
        /// <param name="phase">The tentative truth-value</param>
        public delegate void DecideEh(Expr term, uint idx, bool phase);
        
        // access managed objects through a static array.
        // thread safety is ignored for now.
        GCHandle gch;
        Solver solver;
        Context ctx;
        Z3_solver_callback callback = IntPtr.Zero;
        int callbackNesting = 0;
        FixedEh fixed_eh;
        Action final_eh;
        EqEh eq_eh;
        EqEh diseq_eh;
        CreatedEh created_eh;
        DecideEh decide_eh;

        Native.Z3_push_eh push_eh;
        Native.Z3_pop_eh pop_eh;
        Native.Z3_fresh_eh fresh_eh;

        Native.Z3_fixed_eh fixed_wrapper;
        Native.Z3_final_eh final_wrapper;
        Native.Z3_eq_eh eq_wrapper;
        Native.Z3_eq_eh diseq_wrapper;
        Native.Z3_decide_eh decide_wrapper;
        Native.Z3_created_eh created_wrapper;

        void Callback(Action fn, Z3_solver_callback cb)
        {
            this.callbackNesting++;
            this.callback = cb;
            try
            {
                fn();
            }
            catch
            {
                // TBD: add debug log or exception handler
            }
            finally
            {
                callbackNesting--;
                if (callbackNesting == 0) // callbacks can be nested (e.g., internalizing new element in "created")
                    this.callback = IntPtr.Zero;
            }
        }


        static void _push(voidp ctx, Z3_solver_callback cb)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            prop.Callback(() => prop.Push(), cb);
        }

        static void _pop(voidp ctx, Z3_solver_callback cb, uint num_scopes)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            prop.Callback(() => prop.Pop(num_scopes), cb);
        }

        static voidp _fresh(voidp _ctx, Z3_context new_context)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(_ctx).Target;
            var ctx = new Context(new_context);
            var prop1 = prop.Fresh(prop.ctx);
            return GCHandle.ToIntPtr(prop1.gch);
        }

        static void _fixed(voidp ctx, Z3_solver_callback cb, Z3_ast _term, Z3_ast _value)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            using var term = Expr.Create(prop.ctx, _term);
            using var value = Expr.Create(prop.ctx, _value);
            prop.Callback(() => prop.fixed_eh(term, value), cb);
        }

        static void _final(voidp ctx, Z3_solver_callback cb)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            prop.Callback(() => prop.final_eh(), cb);
        }

        static void _eq(voidp ctx, Z3_solver_callback cb, Z3_ast a, Z3_ast b)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            using var s = Expr.Create(prop.ctx, a);
            using var t = Expr.Create(prop.ctx, b);
            prop.Callback(() => prop.eq_eh(s, t), cb);
        }

        static void _diseq(voidp ctx, Z3_solver_callback cb, Z3_ast a, Z3_ast b)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            using var s = Expr.Create(prop.ctx, a);
            using var t = Expr.Create(prop.ctx, b);
            prop.Callback(() => prop.diseq_eh(s, t), cb);
        }

        static void _created(voidp ctx, Z3_solver_callback cb, Z3_ast a)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            using var t = Expr.Create(prop.ctx, a);
            prop.Callback(() => prop.created_eh(t), cb);
        }

        static void _decide(voidp ctx, Z3_solver_callback cb, Z3_ast a, uint idx, bool phase)
        {
            var prop = (UserPropagator)GCHandle.FromIntPtr(ctx).Target;
            using var t = Expr.Create(prop.ctx, a);
            prop.Callback(() => prop.decide_eh(t, idx, phase), cb);
        }

        /// <summary>
        /// Propagator constructor from a solver class.
        /// </summary>        
        public UserPropagator(Solver s)
        {
            gch = GCHandle.Alloc(this);
            solver = s;
            ctx = solver.Context;
            push_eh = _push;
            pop_eh = _pop;
            fresh_eh = _fresh;
            Native.Z3_solver_propagate_init(ctx.nCtx, solver.NativeObject, GCHandle.ToIntPtr(gch), push_eh, pop_eh, fresh_eh);
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
        /// Release private memory.
        /// </summary>            
        ~UserPropagator()
        {
            Dispose();
        }
        
        /// <summary>
        /// Must be called. The object will not be garbage collected automatically even if the context is disposed
        /// </summary>
        public virtual void Dispose()
        {
            if (!gch.IsAllocated)
                return;
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
        public void Conflict(params Expr[] terms)
        {
            Propagate(terms, ctx.MkFalse());
        }

        /// <summary>
        /// Declare combination of assigned expressions a conflict
        /// </summary>
        public void Conflict(IEnumerable<Expr> terms)
        {
            Propagate(terms, ctx.MkFalse());
        }

        /// <summary>
        /// Propagate consequence
        /// <returns>
        /// <see langword="true" /> if the propagated expression is new for the solver;
        /// <see langword="false" /> if the propagation was ignored
        /// </returns>
        /// </summary>
        public bool Propagate(IEnumerable<Expr> terms, Expr conseq)
        {
            return Propagate(terms, new EqualityPairs(), conseq);
        }

        /// <summary>
        /// Propagate consequence
        /// <returns>
        /// <see langword="true" /> if the propagated expression is new for the solver;
        /// <see langword="false" /> if the propagation was ignored
        /// </returns>
        /// </summary>
        public bool Propagate(IEnumerable<Expr> terms, EqualityPairs equalities, Expr conseq)
        {
            var nTerms = Z3Object.ArrayToNative(terms.ToArray());
            var nLHS = Z3Object.ArrayToNative(equalities.LHS.ToArray());
            var nRHS = Z3Object.ArrayToNative(equalities.RHS.ToArray());
            return Native.Z3_solver_propagate_consequence(ctx.nCtx, this.callback, (uint)nTerms.Length, nTerms, (uint)equalities.Count, nLHS, nRHS, conseq.NativeObject) != 0;
        }


        /// <summary>
        /// Set fixed callback
        /// </summary>
        public FixedEh Fixed
        {
            set
            {
                this.fixed_wrapper = _fixed;
                this.fixed_eh = value;
                if (solver != null)
                    Native.Z3_solver_propagate_fixed(ctx.nCtx, solver.NativeObject, fixed_wrapper);
            }
        }

        /// <summary>
        /// Set final callback
        /// </summary>
        public Action Final
        {
            set
            {
                this.final_wrapper = _final;
                this.final_eh = value;
                if (solver != null)
                    Native.Z3_solver_propagate_final(ctx.nCtx, solver.NativeObject, final_wrapper);
            }
        }

        /// <summary>
        /// Set equality event callback
        /// </summary>
        public EqEh Eq
        {
            set
            {
                this.eq_wrapper = _eq;
                this.eq_eh = value;
                if (solver != null)
                    Native.Z3_solver_propagate_eq(ctx.nCtx, solver.NativeObject, eq_wrapper);
            }
        }

        /// <summary>
        /// Set disequality event callback
        /// </summary>
        public EqEh Diseq
        {
            set
            {
                this.diseq_wrapper = _diseq;
                this.diseq_eh = value;
                if (solver != null)
                    Native.Z3_solver_propagate_diseq(ctx.nCtx, solver.NativeObject, diseq_wrapper);
            }
        }

        /// <summary>
        /// Set created callback
        /// </summary>
        public CreatedEh Created
        {
            set
            {
                this.created_wrapper = _created;
                this.created_eh = value;
                if (solver != null)
                    Native.Z3_solver_propagate_created(ctx.nCtx, solver.NativeObject, created_wrapper);
            }
        }

        /// <summary>
        /// Set decision callback
        /// </summary>
        public DecideEh Decide
        {
            set
            {
                this.decide_wrapper = _decide;
                this.decide_eh = value;
                if (solver != null)
                    Native.Z3_solver_propagate_decide(ctx.nCtx, solver.NativeObject, decide_wrapper);
            }
        }


        /// <summary>
        /// Set the next decision
        /// <param name="e">A bit-vector or Boolean used for branching. Use <see langword="null" /> to clear</param>
        /// <param name="idx">If the term is a bit-vector, then an index into the bit-vector being branched on</param>
        /// <param name="phase">The tentative truth-value (-1/false, 1/true, 0/let Z3 decide)</param>
        /// </summary>
        /// <returns>
        /// <see langword="true" /> in case the value was successfully set;
        /// <see langword="false" /> if the next split could not be set
        /// </returns>
        public bool NextSplit(Expr e, uint idx, int phase)
        {
            return Native.Z3_solver_next_split(ctx.nCtx, this.callback, e?.NativeObject ?? IntPtr.Zero, idx, phase) != 0;
        }

        /// <summary>
        /// Track assignments to a term
        /// </summary>
        public void Register(Expr term)
        {
            if (this.callback != IntPtr.Zero)
            {
                Native.Z3_solver_propagate_register_cb(ctx.nCtx, callback, term.NativeObject);
            }
            else
            {
                Native.Z3_solver_propagate_register(ctx.nCtx, solver.NativeObject, term.NativeObject);
            }
        }
    }

    /// <summary>
    /// A list of equalities used as justifications for propagation
    /// </summary>
    public class EqualityPairs {

        readonly List<Expr> lhsList = new List<Expr>();
        readonly List<Expr> rhsList = new List<Expr>();

        /// <summary>
        /// The left hand sides of the equalities
        /// </summary>
        public Expr[] LHS => lhsList.ToArray();

        /// <summary>
        /// The right hand sides of the equalities
        /// </summary>
        public Expr[] RHS => rhsList.ToArray();

        /// <summary>
        /// The number of equalities
        /// </summary>
        public int Count => lhsList.Count;

        /// <summary>
        /// Adds an equality to the list. The sorts of the arguments have to be the same.
        /// <param name="lhs">The left hand side of the equality</param>
        /// <param name="rhs">The right hand side of the equality</param>
        /// </summary>
        public void Add(Expr lhs, Expr rhs) {
            lhsList.Add(lhs);
            rhsList.Add(rhs);
        }

        /// <summary>
        /// Checks if two equality lists are equal.
        /// The function does not take symmetries, shuffling, or duplicates into account.
        /// </summary>
        public override bool Equals(object obj) {
            if (ReferenceEquals(this, obj))
                return true;
            if (!(obj is EqualityPairs other))
                return false;
            if (lhsList.Count != other.lhsList.Count)
                return false;
            for (int i = 0; i < lhsList.Count; i++) {
                if (!lhsList[i].Equals(other.lhsList[i]))
                    return false;
            }
            return true;
        }

        /// <summary>
        /// Gets a hash code for the list of equalities
        /// </summary>
        public override int GetHashCode() {
            int hash = lhsList.Count;
            unchecked {
                for (int i = 0; i < lhsList.Count; i++) {
                    hash ^= lhsList[i].GetHashCode();
                    hash *= 17;
                    hash ^= rhsList[i].GetHashCode();
                    hash *= 29;
                }
                return hash;
            }
        }
    }
}
