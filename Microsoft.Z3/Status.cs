/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Status.cs

Abstract:

    Z3 Managed API: Status

Author:

    Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
--*/

using System;

namespace Microsoft.Z3
{
  /// <summary>
  /// Status values.
  /// </summary>
  public enum Status
  {    
    /// <summary>
    /// Used to signify an unsatisfiable status.
    /// </summary>
    UNSATISFIABLE = -1,

    /// <summary>
    /// Used to signify an unknown status.
    /// </summary>
    UNKNOWN = 0,

    /// <summary>
    /// Used to signify a satisfiable status.
    /// </summary>
    SATISFIABLE = 1
  }

}
