
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using System.Linq;
using System.Text;
using System.Diagnostics;
using Microsoft.Z3;
using Microsoft.SolverFoundation.Common;
using Microsoft.SolverFoundation.Services;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    internal enum Z3Result
    {
        Optimal,
        LocalOptimal,
        Feasible,
        Interrupted,
        Infeasible
    }

    /// <summary>
    /// The basic solver class to take care of transformation from an MSF instance to an Z3 instance
    /// </summary>
    internal class Z3BaseSolver
    {
        /// <summary>Representing MSF model</summary>
        private IRowVariableModel _model;

        /// <summary>The Z3 solver we are currently using</summary>
        private Context _context = null;

        /// <summary>Default optimization solver</summary>
        private Optimize _optSolver = null;

        /// <summary>Marks when we are inside the Solve() method</summary>
        private bool _isSolving = false;

        /// <summary>A map from MSF variable ids to Z3 variables</summary>
        private Dictionary<int, Expr> _variables = new Dictionary<int, Expr>();

        /// <summary>A map from MSF variable ids to Z3 goal ids</summary>
        private Dictionary<IGoal, uint> _goals = new Dictionary<IGoal, uint>();

        internal Z3BaseSolver(IRowVariableModel model)
        {
            _model = model;
        }

        internal Context Context 
        { 
            get { return _context; }
        }

        internal Dictionary<int, Expr> Variables
        {
            get { return _variables; }
        }

        internal Dictionary<IGoal, uint> Goals
        {
            get { return _goals; }
        }

        /// <summary>
        /// Destructs a currently active Z3 solver and the associated data.
        /// </summary>
        internal void DestructSolver(bool checkInSolve)
        {
            if (_context != null)
            {
                if (checkInSolve && !_isSolving)
                {
                    _variables.Clear();
                    if (!_isSolving)
                    {
                        _optSolver.Dispose();
                        _context.Dispose();
                    }
                }
                else
                {
                    Console.Error.WriteLine("Z3 destruction is invoked while in Solving phase.");
                }
            }
        }

        /// <summary>
        /// Constructs a Z3 solver to be used.
        /// </summary>
        internal void ConstructSolver(Z3BaseParams parameters)
        {
            // If Z3 is there already, kill it
            if (_context != null)
            {
                DestructSolver(false);
            }

            _context = new Context();
            _optSolver = _context.MkOptimize();
            var p = _context.MkParams();

            switch (parameters.OptKind)
            {
                case OptimizationKind.BoundingBox:
                    p.Add("priority", _context.MkSymbol("box"));
                    break;
                case OptimizationKind.Lexicographic:
                    p.Add("priority", _context.MkSymbol("lex"));
                    break;
                case OptimizationKind.ParetoOptimal:
                    p.Add("priority", _context.MkSymbol("pareto"));
                    break;
                default:
                    Debug.Assert(false, String.Format("Unknown optimization option {0}", parameters.OptKind));
                    break;
            }

            switch (parameters.CardinalityAlgorithm)
            {
                case CardinalityAlgorithm.FuMalik:
                    p.Add("maxsat_engine", _context.MkSymbol("fu_malik"));
                    break;
                case CardinalityAlgorithm.CoreMaxSAT:
                    p.Add("maxsat_engine", _context.MkSymbol("core_maxsat"));
                    break;
                default:
                    Debug.Assert(false, String.Format("Unknown cardinality algorithm option {0}", parameters.CardinalityAlgorithm));
                    break;
            }

            switch (parameters.PseudoBooleanAlgorithm)
            {
                case PseudoBooleanAlgorithm.WeightedMaxSAT:
                    p.Add("wmaxsat_engine", _context.MkSymbol("wmax"));
                    break;
                case PseudoBooleanAlgorithm.IterativeWeightedMaxSAT:
                    p.Add("wmaxsat_engine", _context.MkSymbol("iwmax"));
                    break;
                case PseudoBooleanAlgorithm.BisectionWeightedMaxSAT:
                    p.Add("wmaxsat_engine", _context.MkSymbol("bwmax"));
                    break;
                case PseudoBooleanAlgorithm.WeightedPartialMaxSAT2:
                    p.Add("wmaxsat_engine", _context.MkSymbol("wpm2"));
                    break;
                default:
                    Debug.Assert(false, String.Format("Unknown pseudo-boolean algorithm option {0}", parameters.PseudoBooleanAlgorithm));
                    break;
            }

            switch (parameters.ArithmeticStrategy)
            {
                case ArithmeticStrategy.Basic:
                    p.Add("engine", _context.MkSymbol("basic"));
                    break;
                case ArithmeticStrategy.Farkas:
                    p.Add("engine", _context.MkSymbol("farkas"));
                    break;
                default:
                    Debug.Assert(false, String.Format("Unknown arithmetic strategy option {0}", parameters.ArithmeticStrategy));
                    break;
            }

            _optSolver.Parameters = p;
        }

        internal ArithExpr GetVariable(int vid)
        {
            Expr variable;
            if (!_variables.TryGetValue(vid, out variable))
            {
                AddVariable(vid);
                variable = _variables[vid];
            }
            return (ArithExpr)variable;
        }

        internal void AssertBool(BoolExpr row)
        {
            _optSolver.Assert(row);
        }

        internal void AssertArith(int vid, ArithExpr variable)
        {
            // Get the bounds on the row
            Rational lower, upper;
            _model.GetBounds(vid, out lower, out upper);

            // Case of equality
            if (lower == upper)
            {
                // Create the equality term
                Expr eqConst = GetNumeral(lower, variable.Sort);
                BoolExpr constraint = _context.MkEq(eqConst, variable);
                // Assert the constraint
                _optSolver.Assert(constraint);
            }
            else
            {
                // If upper bound is finite assert the upper bound constraint
                if (lower.IsFinite)
                {
                    // Create the lower Bound constraint
                    ArithExpr lowerTerm = GetNumeral(lower, variable.Sort);
                    BoolExpr constraint = _context.MkLe(lowerTerm, variable);
                    // Assert the constraint
                    _optSolver.Assert(constraint);
                }
                // If lower bound is finite assert the lower bound constraint
                if (upper.IsFinite)
                {
                    // Create the upper bound constraint
                    ArithExpr upperTerm = GetNumeral(upper, variable.Sort);
                    BoolExpr constraint = _context.MkGe(upperTerm, variable);
                    // Assert the constraint
                    _optSolver.Assert(constraint);
                }
            }
        }

        /// <summary>
        /// Adds a MSF variable with the coresponding assertion to the Z3 variables.
        /// </summary>
        /// <param name="vid">The MSF id of the variable</param>
        internal void AddVariable(int vid)
        {
            // Is the variable an integer
            bool isInteger = _model.GetIntegrality(vid);

            // Construct the sort we will be using
            Sort sort = isInteger ? (Sort)_context.IntSort : (Sort)_context.RealSort;

            // Get the variable key
            object key = _model.GetKeyFromIndex(vid);

            // Try to construct the name
            string name;
            if (key != null) name = String.Format("x_{0}_{1}", key, vid);
            else name = String.Format("x_{0}", vid);
            ArithExpr variable = (ArithExpr)_context.MkConst(name, sort);

            // Create the variable and add it to the map
            Debug.Assert(!_variables.ContainsKey(vid), "Variable names should be unique.");
            _variables.Add(vid, variable);

            AssertArith(vid, variable);
        }

        internal ArithExpr GetNumeral(Rational rational, Sort sort = null)
        {
            return Utils.GetNumeral(_context, rational, sort);
        }

        internal void Solve(Z3BaseParams parameters, IEnumerable<IGoal> modelGoals, 
                            Action<int> addRow, Func<int, ArithExpr> mkGoalRow, Action<Z3Result> setResult)
        {
            _variables.Clear();
            _goals.Clear();

            try
            {
                // Mark that we are in solving phase
                _isSolving = true;

                // Construct Z3
                ConstructSolver(parameters);

                // Add all the variables
                foreach (int vid in _model.VariableIndices)
                {
                    AddVariable(vid);
                }

                // Add all the rows
                foreach (int rid in _model.RowIndices)
                {
                    addRow(rid);
                }

                // Add enabled goals to optimization problem
                foreach (IGoal g in modelGoals)
                {
                    if (!g.Enabled) continue;

                    ArithExpr gr = mkGoalRow(g.Index);
                    if (g.Minimize)
                        _goals.Add(g, _optSolver.MkMinimize(gr));
                    else
                        _goals.Add(g, _optSolver.MkMaximize(gr));
                }

                if (_goals.Any() && parameters.SMT2LogFile != null)
                {
                    Debug.WriteLine("Dumping SMT2 benchmark to log file...");
                    File.WriteAllText(parameters.SMT2LogFile, _optSolver.ToString());
                }

                bool aborted = parameters.QueryAbort();

                if (!aborted)
                {
                    // Start the abort thread
                    AbortWorker abortWorker = new AbortWorker(_context, parameters.QueryAbort);
                    Thread abortThread = new Thread(abortWorker.Start);
                    abortThread.Start();

                    // Now solve the problem
                    Status status = _optSolver.Check();

                    // Stop the abort thread
                    abortWorker.Stop();
                    abortThread.Join();

                    switch (status)
                    {
                        case Status.SATISFIABLE:
                            Microsoft.Z3.Model model = _optSolver.Model;
                            Debug.Assert(model != null, "Should be able to get Z3 model.");
                            // Remember the solution values                                
                            foreach (KeyValuePair<int, Expr> pair in _variables)
                            {
                                var value = Utils.ToRational(model.Eval(pair.Value, true));
                                _model.SetValue(pair.Key, value);
                            }
                            // Remember all objective values
                            foreach (var pair in _goals)
                            {
                                var optimalValue = Utils.ToRational(_optSolver.GetUpper(pair.Value));
                                _model.SetValue(pair.Key.Index, optimalValue);
                            }
                            model.Dispose();
                            setResult(_goals.Any() ? Z3Result.Optimal : Z3Result.Feasible);
                            break;
                        case Status.UNSATISFIABLE:
                            setResult(Z3Result.Infeasible);
                            break;
                        case Status.UNKNOWN:
                            if (abortWorker.Aborted)
                            {
                                Microsoft.Z3.Model subOptimalModel = _optSolver.Model;
                                if (subOptimalModel != null && subOptimalModel.NumConsts != 0)
                                {
                                    // Remember the solution values                                
                                    foreach (KeyValuePair<int, Expr> pair in _variables)
                                    {
                                        var value = Utils.ToRational(subOptimalModel.Eval(pair.Value, true));
                                        _model.SetValue(pair.Key, value);
                                    }
                                    // Remember all objective values
                                    foreach (var pair in _goals)
                                    {
                                        var optimalValue = Utils.ToRational(_optSolver.GetUpper(pair.Value));
                                        _model.SetValue(pair.Key.Index, optimalValue);
                                    }
                                    subOptimalModel.Dispose();

                                    setResult(Z3Result.LocalOptimal);
                                }
                                else
                                    setResult(Z3Result.Infeasible);
                            }
                            else
                                setResult(Z3Result.Interrupted);
                            break;
                        default:
                            Debug.Assert(false, "Unrecognized Z3 Status");
                            break;
                    }
                }
            }
            finally
            {
                _isSolving = false;
            }

            // Now kill Z3
            DestructSolver(true);
        }
    }
}
