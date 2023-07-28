/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    OnClause.cs

Abstract:

    Callback on clause inferences
    
Author:

    Nikolaj Bjorner (nbjorner) 2022-10-19
    
Notes:


--*/

using System;
using System.Diagnostics;
using System.Linq;
using System.Collections.Generic;
using System.Runtime.InteropServices;

namespace Microsoft.Z3
{

    using Z3_context = System.IntPtr;
    using Z3_solver = System.IntPtr;
    using voidp = System.IntPtr;
    using uintp = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_ast_vector = System.IntPtr;


    /// <summary>
    /// OnClause - clause inference callback
    /// </summary>        
    public class OnClause : IDisposable
    {
        /// <summary>
        /// Delegate type for when clauses are inferred.
	/// An inference is a pair comprising of
        /// - a proof (hint). A partial (or comprehensive) derivation justifying the inference.
	/// - a clause (vector of literals)	
        /// The life-time of the proof hint and clause vector is limited to the scope of the callback.
        /// should the callback want to store hints or clauses it will need to call Dup on the hints
        /// and/or extract literals from the clause, respectively.
        /// </summary>                
        public delegate void OnClauseEh(Expr proof_hint, ASTVector clause);

        
        // access managed objects through a static array.
        // thread safety is ignored for now.
        GCHandle gch;
        Solver solver;
        Context ctx;
	OnClauseEh on_clause;

        Native.Z3_on_clause_eh on_clause_eh;

	static void _on_clause(voidp ctx, Z3_ast _proof_hint, uint n, uint[] deps, Z3_ast_vector _clause) 
        {
             var onc = (OnClause)GCHandle.FromIntPtr(ctx).Target;
             using var proof_hint = Expr.Create(onc.ctx, _proof_hint);
             using var clause = new ASTVector(onc.ctx, _clause);
             onc.on_clause(proof_hint, clause);
	}

        /// <summary>
        /// OnClause constructor
        /// </summary>        
        public OnClause(Solver s, OnClauseEh onc)
        {
            gch = GCHandle.Alloc(this);
            solver = s;
            ctx = solver.Context;
            on_clause = onc;
            on_clause_eh = _on_clause;
            Native.Z3_solver_register_on_clause(ctx.nCtx, solver.NativeObject, GCHandle.ToIntPtr(gch), on_clause_eh);
        }

        /// <summary>
        /// Release private memory.
        /// </summary>            
        ~OnClause()
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
        }
    }
}
