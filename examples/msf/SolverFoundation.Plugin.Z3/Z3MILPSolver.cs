
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.IO;

using Microsoft.Z3;
using Microsoft.SolverFoundation.Common;
using Microsoft.SolverFoundation.Services;
using Microsoft.SolverFoundation.Plugin;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    /// <summary>
    /// The class is implementation of the MSF mixed linear programming solver 
    /// using the Microsoft Z3 solver as the backend.
    /// </summary>
    public class Z3MILPSolver : LinearModel, ILinearSolver, ILinearSolution, IReportProvider
    {
        #region Private members

        private LinearResult _result;       
        private LinearSolutionQuality _solutionQuality;
        private Z3BaseSolver _solver;

        #endregion Private members

        #region Solver construction and destruction

        /// <summary>Constructor that initializes the base clases</summary>
        public Z3MILPSolver() : base(null) 
        {
            _result = LinearResult.Feasible;
            _solver = new Z3BaseSolver(this);
        }

        /// <summary>Constructor that initializes the base clases</summary>
        public Z3MILPSolver(ISolverEnvironment context) : this() { }

        /// <summary>
        /// Shutdown can be called when when the solver is not active, i.e. 
        /// when it is done with Solve() or it has gracefully returns from Solve()
        /// after an abort.
        /// </summary>
        public void Shutdown() { _solver.DestructSolver(true); }

        #endregion Solver construction and destruction

        #region Obtaining information about the solution

        public ILinearSolverReport GetReport(LinearSolverReportType reportType)
        {
            // We don't support sensitivity report
            return null;
        }

        #endregion Obtaining information about the solution

        #region Construction of the problem

        /// <summary>
        /// Get corresponding Z3 formula of a MSF row.
        /// </summary>
        /// <param name="rid">The MSF row id</param>
        private ArithExpr MkGoalRow(int rid)
        {
            // Start with the 0 term
            List<ArithExpr> row = new List<ArithExpr>();

            // Now, add all the entries of this row
            foreach (LinearEntry entry in GetRowEntries(rid))
            {
                // Get the variable and constant in the row
                ArithExpr e = _solver.GetVariable(entry.Index);                
                if (!entry.Value.IsOne)
                {
                    e = _solver.Context.MkMul(_solver.GetNumeral(entry.Value, e.Sort), e);
                }
                row.Add(e);
            }
            switch (row.Count)
            {
                case 0: return _solver.GetNumeral(new Rational());
                case 1: return row[0];
                default: return _solver.Context.MkAdd(row.ToArray());
            }
        }

        /// <summary>
        /// Adds a MSF row to the Z3 assertions.
        /// </summary>
        /// <param name="rid">The MSF row id</param>
        private void AddRow(int rid)
        {
            // Start with the 0 term
            ArithExpr row = MkGoalRow(rid);
            _solver.AssertArith(rid, row);
        }

        /// <summary>
        /// Set results based on internal solver status
        /// </summary>
        private void SetResult(Z3Result status)
        {
            switch (status)
            {
                case Z3Result.Optimal:
                    _result = LinearResult.Optimal;
                    _solutionQuality = LinearSolutionQuality.Exact;
                    break;
                case Z3Result.LocalOptimal:
                    _result = LinearResult.Feasible;
                    _solutionQuality = LinearSolutionQuality.Approximate;
                    break;
                case Z3Result.Feasible:
                    _result = LinearResult.Feasible;
                    _solutionQuality = LinearSolutionQuality.Exact;
                    break;
                case Z3Result.Infeasible:
                    _result = LinearResult.InfeasiblePrimal;
                    _solutionQuality = LinearSolutionQuality.None;
                    break;
                case Z3Result.Interrupted:
                    _result = LinearResult.Interrupted;
                    _solutionQuality = LinearSolutionQuality.None;
                    break;
                default:
                    Debug.Assert(false, "Unrecognized Z3 Result");
                    break;
            } 
        }

        #endregion Construction of the problem

        #region Solving the problem            
        
        /// <summary>
        /// Starts solving the problem using the Z3 solver.
        /// </summary>
        /// <param name="parameters">Parameters to the solver</param>
        /// <returns>The solution to the problem</returns>
        public ILinearSolution Solve(ISolverParameters parameters)
        {
            // Get the Z3 parameters
            var z3Params = parameters as Z3BaseParams;
            Debug.Assert(z3Params != null, "Parameters should be an instance of Z3BaseParams.");
            
            _solver.Solve(z3Params, Goals, AddRow, MkGoalRow, SetResult);

            return this;
        }

        #endregion Solving the problem

        #region ILinearSolution Members

        public Rational GetSolutionValue(int goalIndex)
        {
            var goal = Goals.ElementAt(goalIndex);
            Debug.Assert(goal != null, "Goal should be an element of the goal list.");
            return GetValue(goal.Index);
        }

        public void GetSolvedGoal(int goalIndex, out object key, out int vid, out bool minimize, out bool optimal)
        {
            var goal = Goals.ElementAt(goalIndex);
            Debug.Assert(goal != null, "Goal should be an element of the goal list.");
            key = goal.Key;
            vid = goal.Index;
            minimize = goal.Minimize;
            optimal = _result == LinearResult.Optimal;
        }

        // LpResult is LP relaxation assignment.
        
        public LinearResult LpResult
        {
            get { return _result; }
        }

        public Rational MipBestBound
        {
            get
            {
                Debug.Assert(GoalCount > 0, "MipBestBound is only applicable for optimization instances.");
                return GetSolutionValue(0);
            }
        }

        public LinearResult MipResult
        {
            get { return _result; }
        }

        public LinearResult Result
        {
            get { return _result; }
        }

        public LinearSolutionQuality SolutionQuality
        {
            get { return _solutionQuality; }
        }

        public int SolvedGoalCount
        {
            get { return GoalCount; }
        }

        #endregion

        public Report GetReport(SolverContext context, Solution solution, SolutionMapping solutionMapping)
        {
            LinearSolutionMapping lpSolutionMapping = solutionMapping as LinearSolutionMapping;
            if (lpSolutionMapping == null && solutionMapping != null)
                throw new ArgumentException("solutionMapping is not a LinearSolutionMapping", "solutionMapping");
            return new Z3LinearSolverReport(context, this, solution, lpSolutionMapping);
        }
    }

    /// <summary>
    /// Class implementing the LinearReport.
    /// </summary>
    public class Z3LinearSolverReport : LinearReport
    {
        public Z3LinearSolverReport(SolverContext context, ISolver solver, Solution solution, LinearSolutionMapping solutionMapping)
          : base(context, solver, solution, solutionMapping) {
        }
    }
}
