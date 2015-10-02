
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.SolverFoundation.Common;
using Microsoft.SolverFoundation.Solvers;
using Microsoft.SolverFoundation.Services;
using Microsoft.SolverFoundation.Plugin.Z3;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.SolverFoundation.Plugin.Z3.Tests
{
    [TestClass]
    public class SolverTests
    {
        [TestMethod]
        public void TestMILPSolver1()
        {
            var solver = new Z3MILPSolver();
            int goal;

            solver.AddRow("goal", out goal);
            int x1, x2, z;

            // 0 <= x1 <= 2
            solver.AddVariable("x1", out x1);
            solver.SetBounds(x1, 0, 2);

            // 0 <= x2 <= 2
            solver.AddVariable("x2", out x2);
            solver.SetBounds(x2, 0, 2);

            // z is an integer in [0,1]
            solver.AddVariable("z", out z);
            solver.SetIntegrality(z, true);
            solver.SetBounds(z, 0, 1);

            //max x1 + x2 
            solver.SetCoefficient(goal, x1, 1);
            solver.SetCoefficient(goal, x2, 1);
            solver.AddGoal(goal, 1, false);

            // 0 <= x1 -z <= 1 
            int row1;
            solver.AddRow("rowI1", out row1);
            solver.SetBounds(row1, 0, 1);
            solver.SetCoefficient(row1, x1, 1);
            solver.SetCoefficient(row1, z, -1);

            // 0 <= x2 + z <= 2
            int row2;
            solver.AddRow("rowI2", out row2);
            solver.SetBounds(row2, 0, 2);
            solver.SetCoefficient(row2, x2, 1);
            solver.SetCoefficient(row2, z, 1);

            var p = new Z3MILPParams();
            solver.Solve(p);

            Assert.IsTrue(solver.Result == LinearResult.Optimal);
            Assert.AreEqual(solver.GetValue(x1), 2 * Rational.One);
            Assert.AreEqual(solver.GetValue(x2), Rational.One);
            Assert.AreEqual(solver.GetValue(z), Rational.One);
            Assert.AreEqual(solver.GetValue(goal), 3 * Rational.One);
        }

        [TestMethod]
        public void TestMILPSolver2()
        {
            var solver = new Z3MILPSolver();
            int goal, extraGoal;

            Rational M = 100;
            solver.AddRow("goal", out goal);
            int x1, x2, z;

            // 0 <= x1 <= 100
            solver.AddVariable("x1", out x1);
            solver.SetBounds(x1, 0, M);

            // 0 <= x2 <= 100
            solver.AddVariable("x2", out x2);
            solver.SetBounds(x2, 0, M);

            // z is an integer in [0,1]
            solver.AddVariable("z", out z);
            solver.SetIntegrality(z, true);
            solver.SetBounds(z, 0, 1);

            solver.SetCoefficient(goal, x1, 1);
            solver.SetCoefficient(goal, x2, 2);
            solver.AddGoal(goal, 1, false);

            solver.AddRow("extraGoal", out extraGoal);

            solver.SetCoefficient(extraGoal, x1, 2);
            solver.SetCoefficient(extraGoal, x2, 1);
            solver.AddGoal(extraGoal, 2, false);

            // x1 + x2 >= 1
            int row;
            solver.AddRow("row", out row);
            solver.SetBounds(row, 1, Rational.PositiveInfinity);
            solver.SetCoefficient(row, x1, 1);
            solver.SetCoefficient(row, x2, 1);


            // x1 - M*z <= 0
            int row1;
            solver.AddRow("rowI1", out row1);
            solver.SetBounds(row1, Rational.NegativeInfinity, 0);
            solver.SetCoefficient(row1, x1, 1);
            solver.SetCoefficient(row1, z, -M);

            // x2 - M* (1-z) <= 0
            int row2;
            solver.AddRow("rowI2", out row2);
            solver.SetBounds(row2, Rational.NegativeInfinity, M);
            solver.SetCoefficient(row2, x2, 1);
            solver.SetCoefficient(row2, z, M);

            var p = new Z3MILPParams();
            p.OptKind = OptimizationKind.BoundingBox;

            solver.Solve(p);
            Assert.IsTrue(solver.Result == LinearResult.Optimal);
            Assert.AreEqual(solver.GetValue(goal), 200 * Rational.One);
            Assert.AreEqual(solver.GetValue(extraGoal), 200 * Rational.One);
        }
    }
}
