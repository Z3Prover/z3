
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using System;
using System.Text;
using Microsoft.SolverFoundation.Services;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    /// <summary>
    /// Combining objective functions
    /// </summary>
    public enum OptimizationKind
    {
        Lexicographic,
        BoundingBox,
        ParetoOptimal
    };

    /// <summary>
    /// Algorithm for solving cardinality constraints
    /// </summary>
    public enum CardinalityAlgorithm
    { 
        FuMalik,
        CoreMaxSAT
    }

    /// <summary>
    /// Algorithm for solving pseudo-boolean constraints
    /// </summary>
    public enum PseudoBooleanAlgorithm
    { 
        WeightedMaxSAT,
        IterativeWeightedMaxSAT,
        BisectionWeightedMaxSAT,
        WeightedPartialMaxSAT2
    }

    /// <summary>
    /// Strategy for solving arithmetic optimization
    /// </summary>
    public enum ArithmeticStrategy
    { 
        Basic,
        Farkas
    }

    public abstract class Z3BaseDirective : Directive
    {
        protected OptimizationKind _optKind;
        protected CardinalityAlgorithm _cardAlgorithm;
        protected PseudoBooleanAlgorithm _pboAlgorithm;
        protected ArithmeticStrategy _arithStrategy;

        protected string _smt2LogFile;

        public Z3BaseDirective()
        {
            Arithmetic = Arithmetic.Exact;
        }

        public OptimizationKind OptKind
        {
            get { return _optKind; }
            set { _optKind = value; }
        }

        public CardinalityAlgorithm CardinalityAlgorithm
        {
            get { return _cardAlgorithm; }
            set { _cardAlgorithm = value; }
        }

        public PseudoBooleanAlgorithm PseudoBooleanAlgorithm
        {
            get { return _pboAlgorithm; }
            set { _pboAlgorithm = value; }
        }

        public ArithmeticStrategy ArithmeticStrategy
        {
            get { return _arithStrategy; }
            set { _arithStrategy = value; }
        }

        public string SMT2LogFile
        {
            get { return _smt2LogFile; }
            set { _smt2LogFile = value; }
        }

        public override string ToString() 
        {
            var sb = new StringBuilder();
            sb.Append(this.GetType().Name);
            sb.Append("(");
            sb.AppendFormat("OptKind: {0}, ", _optKind);
            sb.AppendFormat("SMT2LogFile: {0}", _smt2LogFile);
            sb.Append(")");
            return sb.ToString();
        }
    }
}
