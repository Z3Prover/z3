
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

﻿using Microsoft.SolverFoundation.Services;
using System;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    /// <summary>
    /// Implementation of the solver parameters for Z3
    /// </summary>
    public class Z3BaseParams : ISolverParameters
    {
        #region Private Members

        /// <summary>The abort method we can call (defaults to always false) 
        protected Func<bool> _queryAbortFunction = delegate() { return false; };

        /// <summary>The directive to use</summary>
        protected Directive _directive = null;

        protected OptimizationKind _optKind;
        protected CardinalityAlgorithm _cardAlgorithm;
        protected PseudoBooleanAlgorithm _pboAlgorithm;
        protected ArithmeticStrategy _arithStrategy;

        protected string _smt2LogFile;

        #endregion Private Members

        #region Construction

        public Z3BaseParams() { }

        public Z3BaseParams(Directive directive)
        {
            _directive = directive;

            var z3Directive = directive as Z3BaseDirective;
            if (z3Directive != null)
            {
                _optKind = z3Directive.OptKind;
                _cardAlgorithm = z3Directive.CardinalityAlgorithm;
                _pboAlgorithm = z3Directive.PseudoBooleanAlgorithm;
                _arithStrategy = z3Directive.ArithmeticStrategy;
                _smt2LogFile = z3Directive.SMT2LogFile;
            }
        }

        public Z3BaseParams(Func<bool> queryAbortFunction)
        {
            _queryAbortFunction = queryAbortFunction;
        }

        public Z3BaseParams(Z3BaseParams z3Parameters)
        {
            _queryAbortFunction = z3Parameters._queryAbortFunction;
        }

        #endregion Construction

        #region ISolverParameters Members

        /// <summary>
        /// Getter for the abort method
        /// </summary>
        public Func<bool> QueryAbort
        {
            get { return _queryAbortFunction; }
            set { _queryAbortFunction = value; }
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

        #endregion
    }

}