
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.Threading;
using System.Globalization;
using System.Collections.Generic;
using Microsoft.SolverFoundation.Common;
using Microsoft.SolverFoundation.Properties;
using Microsoft.SolverFoundation.Solvers;
using Microsoft.SolverFoundation.Services;
using Microsoft.Z3;
using System.Linq;
using System.Diagnostics;
using System.IO;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    /// <summary>
    /// The class is implementation of the MSF constraint solver
    /// using the Microsoft Z3 solver as the backend. 
    /// This solver supports Int, Real constraints and their arbitrary boolean combinations.
    /// </summary>
    public class Z3TermSolver : TermModel, ITermSolver, INonlinearSolution, IReportProvider
    {
        private NonlinearResult _result;
        private Z3BaseSolver _solver;

        /// <summary>Constructor that initializes the base classes</summary>
        public Z3TermSolver() : base(null) 
        {
            _solver = new Z3BaseSolver(this);
        }

        /// <summary>Constructor that initializes the base classes</summary>
        public Z3TermSolver(ISolverEnvironment context) : this() { }

        /// <summary>
        /// Shutdown can be called when when the solver is not active, i.e. 
        /// when it is done with Solve() or it has gracefully returns from Solve()
        /// after an abort.
        /// </summary>
        public void Shutdown() { _solver.DestructSolver(true); }

        private BoolExpr MkBool(int rid)
        {
            var context = _solver.Context;

            if (IsConstant(rid))
            {
                Rational lower, upper;
                GetBounds(rid, out lower, out upper);
                Debug.Assert(lower == upper);
                if (lower.IsZero) return context.MkFalse();
                return context.MkTrue();
            }
            if (IsOperation(rid))
            {
                BoolExpr[] children;
                ArithExpr[] operands;
                TermModelOperation op = GetOperation(rid);
                switch(op) {
                   case TermModelOperation.And:
                        Debug.Assert(GetOperandCount(rid) >= 2, "Conjunction requires at least two operands.");
                        children = (GetOperands(rid)).Select(x => MkBool(x)).ToArray();
                        return context.MkAnd(children);
                    case TermModelOperation.Or:
                        Debug.Assert(GetOperandCount(rid) >= 2, "Disjunction requires at least two operands.");
                        children = (GetOperands(rid)).Select(x => MkBool(x)).ToArray();
                        return context.MkOr(children);
                    case TermModelOperation.Not:
                        Debug.Assert(GetOperandCount(rid) == 1, "Negation is unary.");
                        return context.MkNot(MkBool(GetOperand(rid, 0)));
                    case TermModelOperation.If:
                        Debug.Assert(GetOperandCount(rid) == 3, "If is ternary.");
                        BoolExpr b = MkBool(GetOperand(rid, 0));
                        Expr x1 = MkBool(GetOperand(rid, 1));
                        Expr x2 = MkBool(GetOperand(rid, 2));
                        return (BoolExpr)context.MkITE(b, x1, x2);
                    case TermModelOperation.Unequal:
                        Debug.Assert(GetOperandCount(rid) >= 2, "Distinct should have at least two operands.");
                        return context.MkDistinct((GetOperands(rid)).Select(x => MkTerm(x)).ToArray());
                    case TermModelOperation.Greater:
                    case TermModelOperation.Less:
                    case TermModelOperation.GreaterEqual:
                    case TermModelOperation.LessEqual:
                    case TermModelOperation.Equal:
                        Debug.Assert(GetOperandCount(rid) >= 2, "Comparison should have at least two operands.");
                        operands = (GetOperands(rid)).Select(x => MkTerm(x)).ToArray();
                        return ReduceComparison(GetOperation(rid), operands);
                    case TermModelOperation.Identity:
                        Debug.Assert(GetOperandCount(rid) == 1, "Identity takes exactly one operand.");
                        return MkBool(GetOperand(rid, 0));
                    default:
                        return context.MkEq(MkTerm(rid), _solver.GetNumeral(Rational.One));
                }
            }
            return context.MkEq(MkTerm(rid), _solver.GetNumeral(Rational.One));
        }

        private ArithExpr MkBoolToArith(BoolExpr e)
        {
            var context = _solver.Context;
            return (ArithExpr)context.MkITE(e, _solver.GetNumeral(Rational.One), _solver.GetNumeral(Rational.Zero));
        }

        private ArithExpr MkTerm(int rid) 
        {
            var context = _solver.Context;

            if (IsConstant(rid))
            {
                Rational lower, upper;
                GetBounds(rid, out lower, out upper);
                Debug.Assert(lower == upper);
                return _solver.GetNumeral(lower);
            }
            else if (IsOperation(rid)) 
            {
                ArithExpr[] operands;
                TermModelOperation op = GetOperation(rid);
                switch(op) 
                {
                    case TermModelOperation.And:
                    case TermModelOperation.Or:
                    case TermModelOperation.Not:
                    case TermModelOperation.Unequal:
                    case TermModelOperation.Greater:
                    case TermModelOperation.Less:
                    case TermModelOperation.GreaterEqual:
                    case TermModelOperation.LessEqual:
                    case TermModelOperation.Equal:
                        return MkBoolToArith(MkBool(rid));
                    case TermModelOperation.If:
                        Debug.Assert(GetOperandCount(rid) == 3, "If is ternary.");
                        BoolExpr b = MkBool(GetOperand(rid, 0));
                        Expr x1 = MkTerm(GetOperand(rid, 1));
                        Expr x2 = MkTerm(GetOperand(rid, 2));
                        return (ArithExpr)context.MkITE(b, x1, x2);
                    case TermModelOperation.Plus:
                        Debug.Assert(GetOperandCount(rid) >= 2, "Plus takes at least two operands.");
                        operands = (GetOperands(rid)).Select(x => MkTerm(x)).ToArray();
                        return context.MkAdd(operands);
                    case TermModelOperation.Minus:
                        Debug.Assert(GetOperandCount(rid) == 1, "Minus takes exactly one operand.");
                        return context.MkUnaryMinus(MkTerm(GetOperand(rid, 0)));
                    case TermModelOperation.Times:
                        Debug.Assert(GetOperandCount(rid) >= 2, "Times requires at least two operands.");
                        operands = (GetOperands(rid)).Select(x => MkTerm(x)).ToArray();
                        return context.MkMul(operands);
                    case TermModelOperation.Identity:
                        Debug.Assert(GetOperandCount(rid) == 1, "Identity takes exactly one operand.");
                        return MkTerm(GetOperand(rid, 0));
                    case TermModelOperation.Abs:
                        Debug.Assert(GetOperandCount(rid) == 1, "Abs takes exactly one operand.");
                        ArithExpr e = MkTerm(GetOperand(rid, 0));
                        ArithExpr minusE = context.MkUnaryMinus(e);
                        ArithExpr zero = _solver.GetNumeral(Rational.Zero);
                        return (ArithExpr)context.MkITE(context.MkGe(e, zero), e, minusE);
                    default:
                        Console.Error.WriteLine("{0} operation isn't supported.", op);
                        throw new NotSupportedException();
                }
            }
            else
            {
                return _solver.GetVariable(rid);
            }
        }

        private BoolExpr ReduceComparison(TermModelOperation type, ArithExpr[] operands)
        {
            var context = _solver.Context;
            Debug.Assert(operands.Length >= 2);            
            Func<ArithExpr, ArithExpr, BoolExpr> mkComparison;
            switch (type)
            {
                case TermModelOperation.Greater:
                    mkComparison = (x, y) => context.MkGt(x, y);
                    break;
                case TermModelOperation.Less:
                    mkComparison = (x, y) => context.MkLt(x, y);
                    break;
                case TermModelOperation.GreaterEqual:
                    mkComparison = (x, y) => context.MkGe(x, y);
                    break;
                case TermModelOperation.LessEqual:
                    mkComparison = (x, y) => context.MkLe(x, y);
                    break;
                case TermModelOperation.Equal:
                    mkComparison = (x, y) => context.MkEq(x, y);
                    break;
                default:
                    throw new NotSupportedException();
            }

            BoolExpr current = mkComparison(operands[0], operands[1]);
            for (int i = 1; i < operands.Length - 1; ++i)
                current = context.MkAnd(current, mkComparison(operands[i], operands[i + 1]));
            return current;
        }

        private bool IsBoolRow(int rid)
        {
            Rational lower, upper;
            GetBounds(rid, out lower, out upper);

            return lower == upper && lower.IsOne && IsBoolTerm(rid);
        }

        private bool IsBoolTerm(int rid)
        {
            if (IsConstant(rid))
            {
                Rational lower, upper;
                GetBounds(rid, out lower, out upper);
                Debug.Assert(lower == upper);
                return lower.IsOne || lower.IsZero;
            }
            if (IsOperation(rid))
            {
                TermModelOperation op = GetOperation(rid);
                switch (op)
                {
                    case TermModelOperation.And:
                    case TermModelOperation.Or:
                    case TermModelOperation.Not:
                    case TermModelOperation.LessEqual:
                    case TermModelOperation.Less:
                    case TermModelOperation.Greater:
                    case TermModelOperation.GreaterEqual:
                    case TermModelOperation.Unequal:
                    case TermModelOperation.Equal:                        
                        return true;
                    case TermModelOperation.If:
                        return IsBoolTerm(GetOperand(rid, 1)) &&
                                IsBoolTerm(GetOperand(rid, 2));
                    case TermModelOperation.Identity:
                        return IsBoolTerm(GetOperand(rid, 0));
                    default:
                        return false;
                }
            }
            return false;
        }

        /// <summary>
        /// Adds a MSF row to the Z3 assertions.
        /// </summary>
        /// <param name="rid">The MSF row id</param>
        private void AddRow(int rid)
        {
            if (IsConstant(rid))
                return;

            if (IsBoolRow(rid))
            {
                _solver.AssertBool(MkBool(rid));
                return;
            }
            // Start with the 0 term
            ArithExpr row = MkTerm(rid);
            _solver.AssertArith(rid, row);
        }

        private TermModelOperation[] _supportedOperations =
                { TermModelOperation.And,
                  TermModelOperation.Or,
                  TermModelOperation.Not,
                  TermModelOperation.Unequal,
                  TermModelOperation.Greater,
                  TermModelOperation.Less,
                  TermModelOperation.GreaterEqual,
                  TermModelOperation.LessEqual,
                  TermModelOperation.Equal,
                  TermModelOperation.If,
                  TermModelOperation.Plus,
                  TermModelOperation.Minus,
                  TermModelOperation.Times,
                  TermModelOperation.Identity,
                  TermModelOperation.Abs };

        /// <summary>
        /// Gets the operations supported by the solver.
        /// </summary>
        /// <returns>All the TermModelOperations supported by the solver.</returns>
        public IEnumerable<TermModelOperation> SupportedOperations
        {
            get { return _supportedOperations; }
        }

        /// <summary>
        /// Set results based on internal solver status
        /// </summary>
        private void SetResult(Z3Result status)
        {
            switch (status)
            {
                case Z3Result.Optimal:
                    _result = NonlinearResult.Optimal;
                    break;
                case Z3Result.LocalOptimal:
                    _result = NonlinearResult.LocalOptimal;
                    break;
                case Z3Result.Feasible:
                    _result = NonlinearResult.Feasible;
                    break;
                case Z3Result.Infeasible:
                    _result = NonlinearResult.Infeasible;
                    break;
                case Z3Result.Interrupted:
                    _result = NonlinearResult.Interrupted;
                    break;
                default:
                    Debug.Assert(false, "Unrecognized Z3 Result");
                    break;
            }
        }

        /// <summary>
        /// Starts solving the problem using the Z3 solver.
        /// </summary>
        /// <param name="parameters">Parameters to the solver</param>
        /// <returns>The solution to the problem</returns>
        public INonlinearSolution Solve(ISolverParameters parameters)
        {
            // Get the Z3 parameters
            var z3Params = parameters as Z3BaseParams;
            Debug.Assert(z3Params != null, "Parameters should be an instance of Z3BaseParams.");

            _solver.Solve(z3Params, Goals, AddRow, MkTerm, SetResult);

            return this;
        }

        double INonlinearSolution.GetValue(int vid)
        {
            Debug.Assert(_solver.Variables.ContainsKey(vid), "This index should correspond to a variable.");
            return GetValue(vid).ToDouble();
        }

        public int SolvedGoalCount
        {
            get { return GoalCount; }
        }

        public double GetSolutionValue(int goalIndex)
        {
            var goal = Goals.ElementAt(goalIndex);
            Debug.Assert(goal != null, "Goal should be an element of the goal list.");
            return GetValue(goal.Index).ToDouble();
        }

        public void GetSolvedGoal(int goalIndex, out object key, out int vid, out bool minimize, out bool optimal)
        {
            var goal = Goals.ElementAt(goalIndex);
            Debug.Assert(goal != null, "Goal should be an element of the goal list.");
            key = goal.Key;
            vid = goal.Index;
            minimize = goal.Minimize;
            optimal = _result == NonlinearResult.Optimal;
        }

        public NonlinearResult Result
        {
            get { return _result; }
        }

        public Report GetReport(SolverContext context, Solution solution, SolutionMapping solutionMapping)
        {
            PluginSolutionMapping pluginSolutionMapping = solutionMapping as PluginSolutionMapping;
            if (pluginSolutionMapping == null && solutionMapping != null)
                throw new ArgumentException("solutionMapping is not a LinearSolutionMapping", "solutionMapping");
            return new Z3TermSolverReport(context, this, solution, pluginSolutionMapping);
        }
    }

    public class Z3TermSolverReport : Report
    {
        public Z3TermSolverReport(SolverContext context, ISolver solver, Solution solution, PluginSolutionMapping pluginSolutionMapping)
            : base(context, solver, solution, pluginSolutionMapping)
        {          
        }
    }
}
