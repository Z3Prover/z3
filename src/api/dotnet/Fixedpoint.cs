/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Fixedpoints.cs

Abstract:

    Z3 Managed API: Fixedpoints

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Object for managing fixedpoints
    /// </summary>
    [ContractVerification(true)]
    public class Fixedpoint : Z3Object
    {

        /// <summary>
        /// A string that describes all available fixedpoint solver parameters.
        /// </summary>
        public string Help
        {
            get
            {
                Contract.Ensures(Contract.Result<string>() != null);
                return Native.Z3_fixedpoint_get_help(Context.nCtx, NativeObject);
            }
        }

        /// <summary>
        /// Sets the fixedpoint solver parameters.
        /// </summary>
        public Params Parameters
        {
            set
            {
                Contract.Requires(value != null);
                Context.CheckContextMatch(value);
                Native.Z3_fixedpoint_set_params(Context.nCtx, NativeObject, value.NativeObject);
            }
        }

        /// <summary>
        /// Retrieves parameter descriptions for Fixedpoint solver.
        /// </summary>
        public ParamDescrs ParameterDescriptions
        {
            get { return new ParamDescrs(Context, Native.Z3_fixedpoint_get_param_descrs(Context.nCtx, NativeObject)); }
        }


        /// <summary>
        /// Assert a constraint (or multiple) into the fixedpoint solver.
        /// </summary>        
        public void Assert(params BoolExpr[] constraints)
        {
            Contract.Requires(constraints != null);
            Contract.Requires(Contract.ForAll(constraints, c => c != null));

            Context.CheckContextMatch<BoolExpr>(constraints);
            foreach (BoolExpr a in constraints)
            {
                Native.Z3_fixedpoint_assert(Context.nCtx, NativeObject, a.NativeObject);
            }
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(params BoolExpr[] constraints)
        {
            Assert(constraints);
        }

        /// <summary>
        /// Register predicate as recursive relation.
        /// </summary>       
        public void RegisterRelation(FuncDecl f)
        {
            Contract.Requires(f != null);

            Context.CheckContextMatch(f);
            Native.Z3_fixedpoint_register_relation(Context.nCtx, NativeObject, f.NativeObject);
        }

        /// <summary>
        /// Add rule into the fixedpoint solver.
        /// </summary>        
        public void AddRule(BoolExpr rule, Symbol name = null)
        {
            Contract.Requires(rule != null);

            Context.CheckContextMatch(rule);
            Native.Z3_fixedpoint_add_rule(Context.nCtx, NativeObject, rule.NativeObject, AST.GetNativeObject(name));
        }

        /// <summary>
        /// Add table fact to the fixedpoint solver.
        /// </summary>        
        public void AddFact(FuncDecl pred, params uint[] args)
        {
            Contract.Requires(pred != null);
            Contract.Requires(args != null);

            Context.CheckContextMatch(pred);
            Native.Z3_fixedpoint_add_fact(Context.nCtx, NativeObject, pred.NativeObject, (uint)args.Length, args);
        }

        /// <summary>
        /// Query the fixedpoint solver.
        /// A query is a conjunction of constraints. The constraints may include the recursively defined relations.
        /// The query is satisfiable if there is an instance of the query variables and a derivation for it.
        /// The query is unsatisfiable if there are no derivations satisfying the query variables. 
        /// </summary>        
        public Status Query(BoolExpr query)
        {
            Contract.Requires(query != null);

            Context.CheckContextMatch(query);
            Z3_lbool r = (Z3_lbool)Native.Z3_fixedpoint_query(Context.nCtx, NativeObject, query.NativeObject);
            switch (r)
            {
                case Z3_lbool.Z3_L_TRUE: return Status.SATISFIABLE;
                case Z3_lbool.Z3_L_FALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        /// <summary>
        /// Query the fixedpoint solver.
        /// A query is an array of relations.
        /// The query is satisfiable if there is an instance of some relation that is non-empty.
        /// The query is unsatisfiable if there are no derivations satisfying any of the relations.
        /// </summary>        
        public Status Query(FuncDecl[] relations)
        {
            Contract.Requires(relations != null);
            Contract.Requires(Contract.ForAll(0, relations.Length, i => relations[i] != null));

            Context.CheckContextMatch<FuncDecl>(relations);
            Z3_lbool r = (Z3_lbool)Native.Z3_fixedpoint_query_relations(Context.nCtx, NativeObject,
                                   AST.ArrayLength(relations), AST.ArrayToNative(relations));
            switch (r)
            {
                case Z3_lbool.Z3_L_TRUE: return Status.SATISFIABLE;
                case Z3_lbool.Z3_L_FALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        /// <summary>
        /// Creates a backtracking point.
        /// </summary>
        /// <seealso cref="Pop"/>
        public void Push()
        {
            Native.Z3_fixedpoint_push(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Backtrack one backtracking point.
        /// </summary>
        /// <remarks>Note that an exception is thrown if Pop is called without a corresponding <c>Push</c></remarks>
        /// <seealso cref="Push"/>
        public void Pop()
        {
            Native.Z3_fixedpoint_pop(Context.nCtx, NativeObject);
        }


        /// <summary>
        /// Update named rule into in the fixedpoint solver.
        /// </summary>        
        public void UpdateRule(BoolExpr rule, Symbol name)
        {
            Contract.Requires(rule != null);

            Context.CheckContextMatch(rule);
            Native.Z3_fixedpoint_update_rule(Context.nCtx, NativeObject, rule.NativeObject, AST.GetNativeObject(name));
        }

        /// <summary>
        /// Retrieve satisfying instance or instances of solver, 
        /// or definitions for the recursive predicates that show unsatisfiability.
        /// </summary>                
        public Expr GetAnswer()
        {
            IntPtr ans = Native.Z3_fixedpoint_get_answer(Context.nCtx, NativeObject);
            return (ans == IntPtr.Zero) ? null : Expr.Create(Context, ans);
        }

        /// <summary>
        /// Retrieve explanation why fixedpoint engine returned status Unknown.
        /// </summary>                
        public string GetReasonUnknown()
        {
            Contract.Ensures(Contract.Result<string>() != null);

            return Native.Z3_fixedpoint_get_reason_unknown(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Retrieve the number of levels explored for a given predicate.
        /// </summary>                
        public uint GetNumLevels(FuncDecl predicate)
        {
            return Native.Z3_fixedpoint_get_num_levels(Context.nCtx, NativeObject, predicate.NativeObject);
        }

        /// <summary>
        /// Retrieve the cover of a predicate.
        /// </summary>                
        public Expr GetCoverDelta(int level, FuncDecl predicate)
        {
            IntPtr res = Native.Z3_fixedpoint_get_cover_delta(Context.nCtx, NativeObject, level, predicate.NativeObject);
            return (res == IntPtr.Zero) ? null : Expr.Create(Context, res);
        }

        /// <summary>
        /// Add <tt>property</tt> about the <tt>predicate</tt>.
        /// The property is added at <tt>level</tt>.
        /// </summary>                
        public void AddCover(int level, FuncDecl predicate, Expr property)
        {
            Native.Z3_fixedpoint_add_cover(Context.nCtx, NativeObject, level, predicate.NativeObject, property.NativeObject);
        }

        /// <summary>
        /// Retrieve internal string representation of fixedpoint object.
        /// </summary>                
        public override string ToString()
        {
            return Native.Z3_fixedpoint_to_string(Context.nCtx, NativeObject, 0, null);
        }

        /// <summary>
        /// Instrument the Datalog engine on which table representation to use for recursive predicate.
        /// </summary>                
        public void SetPredicateRepresentation(FuncDecl f, Symbol[] kinds)
        {
            Contract.Requires(f != null);

            Native.Z3_fixedpoint_set_predicate_representation(Context.nCtx, NativeObject,
                               f.NativeObject, AST.ArrayLength(kinds), Symbol.ArrayToNative(kinds));

        }

        /// <summary>
        /// Convert benchmark given as set of axioms, rules and queries to a string.
        /// </summary>                
        public string ToString(BoolExpr[] queries)
        {

            return Native.Z3_fixedpoint_to_string(Context.nCtx, NativeObject,
                             AST.ArrayLength(queries), AST.ArrayToNative(queries));
        }

        /// <summary>
        /// Retrieve set of rules added to fixedpoint context.
        /// </summary>                
        public BoolExpr[] Rules
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr[]>() != null);

                ASTVector av = new ASTVector(Context, Native.Z3_fixedpoint_get_rules(Context.nCtx, NativeObject));
                return av.ToBoolExprArray();
            }
        }

        /// <summary>
        /// Retrieve set of assertions added to fixedpoint context.
        /// </summary>                
        public BoolExpr[] Assertions
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr[]>() != null);

                ASTVector av = new ASTVector(Context, Native.Z3_fixedpoint_get_assertions(Context.nCtx, NativeObject));
                return av.ToBoolExprArray();
            }
        }

        /// <summary>
        /// Fixedpoint statistics.
        /// </summary>
        public Statistics Statistics
        {
            get
            {
                Contract.Ensures(Contract.Result<Statistics>() != null);

                return new Statistics(Context, Native.Z3_fixedpoint_get_statistics(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Parse an SMT-LIB2 file with fixedpoint rules. 
        /// Add the rules to the current fixedpoint context. 
        /// Return the set of queries in the file.
        /// </summary>                
        public BoolExpr[] ParseFile(string file)
        {
            ASTVector av = new ASTVector(Context, Native.Z3_fixedpoint_from_file(Context.nCtx, NativeObject, file));
            return av.ToBoolExprArray();
        }

        /// <summary>
        /// Similar to ParseFile. Instead it takes as argument a string.
        /// </summary>
        public BoolExpr[] ParseString(string s)
        {
            ASTVector av = new ASTVector(Context, Native.Z3_fixedpoint_from_string(Context.nCtx, NativeObject, s));
            return av.ToBoolExprArray();
        }


        #region Internal
        internal Fixedpoint(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal Fixedpoint(Context ctx)
            : base(ctx, Native.Z3_mk_fixedpoint(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_fixedpoint_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_fixedpoint_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.Fixedpoint_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Fixedpoint_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
