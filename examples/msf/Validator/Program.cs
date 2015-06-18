
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using Microsoft.SolverFoundation.Common;
using Microsoft.SolverFoundation.Solvers;
using Microsoft.SolverFoundation.Plugin.Z3;
using Microsoft.SolverFoundation.Services;
using System.Text;

namespace Validator
{
    class Program
    {
        static void LoadModel(SolverContext context, string fileName)
        { 
            string ext = Path.GetExtension(fileName).ToLower();

            if (ext == ".mps")
            {
                context.LoadModel(FileFormat.MPS, Path.GetFullPath(fileName));
            }
            else if (ext == ".smps")
            {
                context.LoadModel(FileFormat.SMPS, Path.GetFullPath(fileName));
            }
            else if (ext == ".oml")
            {
                context.LoadModel(FileFormat.OML, Path.GetFullPath(fileName));
            }
            else
            {
                throw new NotSupportedException("This file format hasn't been supported.");
            }
        }

        static void ExecuteZ3(string fileName, Z3BaseDirective directive)
        {
            SolverContext context = SolverContext.GetContext();
            try
            {
                LoadModel(context, fileName);

                Solution solution = context.Solve(directive);
                Report report = solution.GetReport();
                Console.Write("{0}", report);
            }
            catch (Exception e)
            {
                Console.WriteLine("Skipping unsolvable instance in {0} with error message '{1}'.", fileName, e.Message);
            }
            finally
            {
                context.ClearModel();
            }
        }

        static void ConvertToSMT2(string fileName, Z3BaseDirective directive)
        {
            SolverContext context = SolverContext.GetContext();
            try
            {
                LoadModel(context, fileName);

                if (context.CurrentModel.Goals.Any())
                {
                    directive.SMT2LogFile = Path.ChangeExtension(fileName, ".smt2");
                    context.Solve(() => true, directive);
                }
            }
            catch (Exception e)
            {
                Console.WriteLine("Skipping unconvertable instance in {0} with error message '{1}'.", fileName, e.Message);
            }
            finally
            {
                context.ClearModel();
            }       
        }

        static void ValidateZ3(string fileName, Z3BaseDirective directive)
        {
            SolverContext context = SolverContext.GetContext();
            try
            {
                LoadModel(context, fileName);

                if (context.CurrentModel.Goals.Any())
                {
                    var msfDirective = (directive is Z3MILPDirective) ? (Directive)new MixedIntegerProgrammingDirective() { TimeLimit = 10000 }
                                            : (Directive)new Directive() { TimeLimit = 10000 };
                    var sol1 = context.Solve(msfDirective);
                    
                    Console.WriteLine("Solved the model using MSF.");
                    Console.Write("{0}", sol1.GetReport());
                    var expectedGoals = sol1.Goals.Select(x => x.ToDouble());
                    context.ClearModel();

                    context.LoadModel(FileFormat.OML, Path.GetFullPath(fileName));
                    directive.SMT2LogFile = Path.ChangeExtension(fileName, ".smt2");
                    var sol2 = context.Solve(directive);
                    //Console.Write("{0}", sol2.GetReport());
                    var actualGoals = sol2.Goals.Select(x => x.ToDouble());

                    Console.WriteLine("Solved the model using Z3.");
                    var goalPairs = expectedGoals.Zip(actualGoals, (expected, actual) => new { expected, actual }).ToArray();
                    bool validated = goalPairs.All(p => Math.Abs(p.expected - p.actual) <= 0.0001);
                    if (validated)
                    {
                        Console.WriteLine("INFO: Two solvers give approximately the same results.");
                    }
                    else
                    {
                        Console.Error.WriteLine("ERROR: Discrepancy found between results.");
                        if (!validated && File.Exists(directive.SMT2LogFile))
                        {
                            var sb = new StringBuilder();                            
                            for(int i = 0; i < goalPairs.Length; i++)
                            {
                                sb.AppendFormat("\n(echo \"Goal {0}: actual |-> {1:0.0000}, expected |-> {2:0.0000}\")",
                                    i + 1, goalPairs[i].actual, goalPairs[i].expected);
                            }
                            Console.Error.WriteLine(sb.ToString());
                            File.AppendAllText(directive.SMT2LogFile, sb.ToString());
                        }
                    }
                }
                else
                {
                    Console.WriteLine("Ignoring this instance without having any goal.");
                }
            }
            catch (Exception e)
            {
                Console.WriteLine("Skipping unsolvable instance in {0} with error message '{1}'.", 
                    fileName, e.Message);
            }
            finally
            {
                context.ClearModel();
            }
        }

        static void Main(string[] args)
        {
            Z3BaseDirective directive = new Z3MILPDirective();

            for (int i = 0; i < args.Length; ++i) {
                if (args[i] == "-s" || args[i] == "-solve")
                {
                    ExecuteZ3(args[i + 1], directive);
                    return;
                }
                if (args[i] == "-c" || args[i] == "-convert")
                {
                    ConvertToSMT2(args[i + 1], directive);
                    return;
                }
                if (args[i] == "-v" || args[i] == "-validate")
                {
                    ValidateZ3(args[i + 1], directive);
                    return;
                }
                if (args[i] == "-t" || args[i] == "-term")
                {
                    directive = new Z3TermDirective();
                }
            }

            if (args.Length > 0)
            {
                ExecuteZ3(args[0], directive);
                return;
            }

            Console.WriteLine(@"
Validator is a simple command line to migrate benchmarks from OML, MPS and SMPS to SMT2 formats.

Commands:
    -solve <file_name> : solving the model using Z3
    -convert <file_name> : converting the model into SMT2 format
    -validate <file_name> : validating by comparing results between Z3 and MSF solvers
    -term : change the default Z3 MILP solver to Z3 Term solver

    where <file_name> is any file with OML, MPS or SMPS extension.

Examples:
    Validator.exe -convert model.mps
    Validator.exe -term -solve model.oml

");
        }
    }
}
