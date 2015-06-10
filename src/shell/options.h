
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


/**
   \page cmdline Command line options
   
   \section informat Input format
   
   Z3 understands a set of default file extensions, and will invoke a parser based on the extension.

   - \ext{smt2} - <a href="http://www.smtlib.org">SMT-LIB 2</a> format, this is the preferred input format.

   - \ext{dimacs}, \ext{cnf} - DIMACS format used by regular SAT solvers.
   
   - \ext{dl} - Datalog input format.

   - \ext{smt} - (deprecated) <a href="http://www.smtlib.org">SMT-LIB 1</a> format.

   You can tell Z3 explicitly which grammar the input belongs to by using the following options:
   
   \cmdopt{smt2} use parser for SMT-LIB 2.0 input format.

   \cmdopt{dimacs} use dimacs parser to read the input file.

   \section cmdlinemis Miscellaneous

   \cmdopt{h\, ?}      prints the help message.

   \cmdopt{version}    prints version number of Z3.

  \cmdopt{v:level}    be verbose, where <level> is the verbosity level.

  \cmdopt{nw}         disable warning messages.

  \cmdopt{ini:file}   configuration file.
  Several parameters are available besides the ones listed by \ty{/h}.
  These parameters can be loaded from an initialization file by using
  this option. 

  \cmdopt{ini?}       display all available INI file parameters.

  The available \ref config can also be supplied on the command 
  line as a pair parameter-name=parameter-value.

   \section cmdlineres Resources

   \cmdopt{T:timeout}  set the timeout (in seconds).
   Setting this option causes the entire process to exit. 
   It is a reliable way to kill Z3.

   \cmdopt{t:timeout}  set the soft timeout (in seconds). 
   It only kills the current query.

   \cmdopt{memory:Megabytes}  set a limit for virtual memory consumption.
   This limit for virtual memory consumption is approximate, but in 
   general a good guideline for controlling the memory consumption of Z3. If the
   memory consumption exceeds the specified number of Megabytes, Z3 exits with a warning
   message. 

  \section cmdlineout Output

  \cmdopt{st}         display statistics.
  This option can be used to dump various statistics about the search, 
  such as number of splits, conflict clauses, and quantifier instantiations.
   
  \section cmdlinesearch Search heuristics

  \cmdopt{rs:num}     random seed.
*/
