
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
    public class ServiceTests
    {
        [TestInitialize]
        public void SetUp()
        {
            SolverContext context = SolverContext.GetContext();
            context.ClearModel();
        }

        private void TestService1(Directive directive)
        {
            SolverContext context = SolverContext.GetContext();
            Model model = context.CreateModel();

            Decision x1 = new Decision(Domain.RealRange(0, 2), "x1");
            Decision x2 = new Decision(Domain.RealRange(0, 2), "x2");

            Decision z = new Decision(Domain.IntegerRange(0, 1), "z");

            model.AddDecisions(x1, x2, z);

            model.AddConstraint("Row0", x1 - z <= 1);
            model.AddConstraint("Row1", x2 + z <= 2);

            Goal goal = model.AddGoal("Goal0", GoalKind.Maximize, x1 + x2);

            Solution solution = context.Solve(directive);
            Assert.IsTrue(goal.ToInt32() == 3);
            context.ClearModel();
        }

        private void TestService2(Directive directive)
        {
            SolverContext context = SolverContext.GetContext();
            Model model = context.CreateModel();

            Decision x1 = new Decision(Domain.RealNonnegative, "x1");
            Decision x2 = new Decision(Domain.RealNonnegative, "x2");

            Decision z = new Decision(Domain.IntegerRange(0, 1), "z");

            Rational M = 100;
            
            model.AddDecisions(x1, x2, z);

            model.AddConstraint("Row0", x1 + x2 >= 1);
            model.AddConstraint("Row1", x1 - z * 100 <= 0);
            model.AddConstraint("Row2", x2 + z * 100 <= 100);

            Goal goal = model.AddGoal("Goal0", GoalKind.Maximize, x1 + x2);

            Solution solution = context.Solve(directive);
            Assert.IsTrue(goal.ToInt32() == 100);
            context.ClearModel();
        }

        [TestMethod]
        public void TestService1()
        {
            TestService1(new Z3MILPDirective());
            TestService1(new Z3TermDirective());
        }

        [TestMethod]
        public void TestService2()
        {
            TestService2(new Z3MILPDirective());
            TestService2(new Z3TermDirective());
        }

    }
}
