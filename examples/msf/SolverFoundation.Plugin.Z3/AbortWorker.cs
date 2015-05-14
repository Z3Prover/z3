using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using Microsoft.Z3;

namespace Microsoft.SolverFoundation.Plugin.Z3
{
    /// <summary>
    /// Thread that will wait until the query abort function returns true or 
    /// the stop method is called. If the abort function returns true at some
    /// point it will issue a softCancel() call to Z3.
    /// </summary>
    internal class AbortWorker
    {
        #region Private Members

        /// <summary>The Z3 solver</summary>
        private Microsoft.Z3.Context _context;
        /// <summary>The abort function to use to check if we are aborted</summary>
        private Func<bool> _QueryAbortFunction;
        /// <summary>Flag indicating that worker should stop</summary>
        private bool _stop = false;
        /// <summary>Flag indicating that we have been sent an abort signal</summary>
        private bool _aborted = false;

        #endregion Private Members

        #region Construction

        /// <summary>
        /// Worker constructor taking a Z3 instance and a function to periodically
        /// check for aborts.
        /// </summary>
        /// <param name="z3">Z3 instance</param>
        /// <param name="queryAbortFunction">method to call to check for aborts</param>
        public AbortWorker(Context context, Func<bool> queryAbortFunction)
        {
            _context = context;
            _QueryAbortFunction = queryAbortFunction;
        }

        #endregion Construction

        #region Public Methods

        /// <summary>
        /// Stop the abort worker.
        /// </summary>
        public void Stop()
        {
            _stop = true;
        }

        /// <summary>
        /// Is true if we have been aborted.
        /// </summary>
        public bool Aborted
        {
            get
            {
                return _aborted;
            }
        }

        /// <summary>
        /// Starts the abort worker. The worker checks the abort method
        /// periodically until either it is stopped by a call to the Stop()
        /// method or it gets an abort signal. In the latter case it will
        /// issue a soft abort signal to Z3.
        /// </summary>
        public void Start()
        {
            // We go until someone stops us
            _stop = false;
            while (!_stop && !_QueryAbortFunction())
            {
                // Wait for a while
                Thread.Sleep(10);
            }
            // If we were stopped on abort, cancel z3
            if (!_stop)
            {
                _context.Interrupt();
                _aborted = true;
            }
        }

        #endregion Public Methods
    }
}
