/**
 * This file was automatically generated from Fixedpoint.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Object for managing fixedpoints
     **/
    public class Fixedpoint extends Z3Object
    {

        /**
         * A string that describes all available fixedpoint solver parameters.
         **/
        public String Help() 
            {
                
                return Native.fixedpointGetHelp(Context.nCtx, NativeObject);
        }

        /**
         * Sets the fixedpoint solver parameters.
         **/
        public void setParameters(Params value) 
            {
                
                Context.CheckContextMatch(value);
                Native.fixedpointSetParams(Context.nCtx, NativeObject, value.NativeObject);
        }

        /**
         * Retrieves parameter descriptions for Fixedpoint solver.
         **/
        public ParamDescrs ParameterDescriptions()  { return new ParamDescrs(Context, Native.fixedpointGetParamDescrs(Context.nCtx, NativeObject)); }


        /**
         * Assert a constraint (or multiple) into the fixedpoint solver.
         **/
        public void Assert(BoolExpr[] constraints)
        {
            
            

            Context.CheckContextMatch(constraints);
            for (BoolExpr.Iterator a = constraints.iterator(); a.hasNext(); )
            {
                Native.fixedpointAssert(Context.nCtx, NativeObject, a.NativeObject);
            }
        }

        /**
         * Register predicate as recursive relation.
         **/
        public void RegisterRelation(FuncDecl f)
        {
            

            Context.CheckContextMatch(f);
            Native.fixedpointRegisterRelation(Context.nCtx, NativeObject, f.NativeObject);
        }

        /**
         * Add rule into the fixedpoint solver.
         **/
        public void AddRule(BoolExpr rule, Symbol name)
        {
            

            Context.CheckContextMatch(rule);
            Native.fixedpointAddRule(Context.nCtx, NativeObject, rule.NativeObject, AST.GetNativeObject(name));
        }

        /**
         * Add table fact to the fixedpoint solver.
         **/
        public void AddFact(FuncDecl pred, Integer[] args)
        {
            
            

            Context.CheckContextMatch(pred);
            Native.fixedpointAddFact(Context.nCtx, NativeObject, pred.NativeObject, (Integer)args.Length, args);
        }

        /**
         * Query the fixedpoint solver.
         * A query is a conjunction of constraints. The constraints may include the recursively defined relations.
         * The query is satisfiable if there is an instance of the query variables and a derivation for it.
         * The query is unsatisfiable if there are no derivations satisfying the query variables. 
         **/
        public Status Query(BoolExpr query)
        {
            

            Context.CheckContextMatch(query);
            Z3Lboolean r = (Z3Lboolean)Native.fixedpointQuery(Context.nCtx, NativeObject, query.NativeObject);
            switch (r)
            {
                case Z3Lboolean.Z3LTRUE: return Status.SATISFIABLE;
                case Z3Lboolean.Z3LFALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        /**
         * Query the fixedpoint solver.
         * A query is an array of relations.
         * The query is satisfiable if there is an instance of some relation that is non-empty.
         * The query is unsatisfiable if there are no derivations satisfying any of the relations.
         **/
        public Status Query(FuncDecl[] relations)
        {
            
            

            Context.CheckContextMatch(relations);
            Z3Lboolean r = (Z3Lboolean)Native.fixedpointQueryRelations(Context.nCtx, NativeObject,
                                   AST.ArrayLength(relations), AST.ArrayToNative(relations));
            switch (r)
            {
                case Z3Lboolean.Z3LTRUE: return Status.SATISFIABLE;
                case Z3Lboolean.Z3LFALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        /**
         * Creates a backtracking point.
         * <seealso cref="Pop"/>
         **/
        public void Push()
        {
            Native.fixedpointPush(Context.nCtx, NativeObject);
        }

        /**
         * Backtrack one backtracking point.
         * <remarks>Note that an exception is thrown if Pop is called without a corresponding <code>Push</code></remarks>
         * <seealso cref="Push"/>
         **/
        public void Pop()
        {
            Native.fixedpointPop(Context.nCtx, NativeObject);
        }


        /**
         * Update named rule into in the fixedpoint solver.
         **/
        public void UpdateRule(BoolExpr rule, Symbol name)
        {
            

            Context.CheckContextMatch(rule);
            Native.fixedpointUpdateRule(Context.nCtx, NativeObject, rule.NativeObject, AST.GetNativeObject(name));
        }

        /**
         * Retrieve satisfying instance or instances of solver, 
         * or definitions for the recursive predicates that show unsatisfiability.
         **/
        public Expr GetAnswer()
        {
            IntPtr ans = Native.fixedpointGetAnswer(Context.nCtx, NativeObject);
            return (ans == IntPtr.Zero) ? null : Expr.Create(Context, ans);
        }

        /**
         * Retrieve explanation why fixedpoint engine returned status Unknown.
         **/
        public String GetReasonUnknown()
        {
            

            return Native.fixedpointGetReasonUnknown(Context.nCtx, NativeObject);
        }

        /**
         * Retrieve the number of levels explored for a given predicate.
         **/
        public Integer GetNumLevels(FuncDecl predicate)
        {
            return Native.fixedpointGetNumLevels(Context.nCtx, NativeObject, predicate.NativeObject);
        }

        /**
         * Retrieve the cover of a predicate.
         **/
        public Expr GetCoverDelta(int level, FuncDecl predicate)
        {
            IntPtr res = Native.fixedpointGetCoverDelta(Context.nCtx, NativeObject, level, predicate.NativeObject);
            return (res == IntPtr.Zero) ? null : Expr.Create(Context, res);
        }

        /**
         * Add <tt>property</tt> about the <tt>predicate</tt>.
         * The property is added at <tt>level</tt>.
         **/
        public void AddCover(int level, FuncDecl predicate, Expr property)
        {
            Native.fixedpointAddCover(Context.nCtx, NativeObject, level, predicate.NativeObject, property.NativeObject);
        }

        /**
         * Retrieve internal string representation of fixedpoint object.
         **/
        public String toString()
        {
            return Native.fixedpointtoString(Context.nCtx, NativeObject, 0, null);
        }

        /**
         * Instrument the Datalog engine on which table representation to use for recursive predicate.
         **/
        public void SetPredicateRepresentation(FuncDecl f, Symbol[] kinds)
        {
            

            Native.fixedpointSetPredicateRepresentation(Context.nCtx, NativeObject,
                               f.NativeObject, AST.ArrayLength(kinds), Symbol.ArrayToNative(kinds));

        }

        /**
         * Convert benchmark given as set of axioms, rules and queries to a string.
         **/
        public String toString(BoolExpr[] queries)
        {

            return Native.fixedpointtoString(Context.nCtx, NativeObject,
                             AST.ArrayLength(queries), AST.ArrayToNative(queries));
        }

        /**
         * Retrieve set of rules added to fixedpoint context.
         **/
        public BoolExpr[] Rules {() 
                

                ASTVector v = new ASTVector(Context, Native.fixedpointGetRules(Context.nCtx, NativeObject));
                Integer n = v.Size;
                BoolExpr[] res = new BoolExpr[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = new BoolExpr(Context, v[i].NativeObject);
                return res;
        }

        /**
         * Retrieve set of assertions added to fixedpoint context.
         **/
        public BoolExpr[] Assertions {() 
                

                ASTVector v = new ASTVector(Context, Native.fixedpointGetAssertions(Context.nCtx, NativeObject));
                Integer n = v.Size;
                BoolExpr[] res = new BoolExpr[n];
                for (Integer i = 0; i < n; i++)
                    res[i] = new BoolExpr(Context, v[i].NativeObject);
                return res;
        }


        Fixedpoint(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        Fixedpoint(Context ctx)
            { super(ctx, Native.mkFixedpoint(ctx.nCtx));
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.fixedpointIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.fixedpointDecRef(ctx.nCtx, obj);
            }
        };

        void IncRef(IntPtr o)
        {
            Context.FixedpointDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.FixedpointDRQ.Add(o);
            super.DecRef(o);
        }
    }
