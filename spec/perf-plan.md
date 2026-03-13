\# This is a specification for evaluating and improving theory\_nseq.

. Build a debug version of z3 in the z3\\build directory

. Build a release version of z3 in the z3\\release directory

. To use zipt run .\\ZIPT\\bin\\Debug\\net8.0\\ZIPT.exe -v <filename>

. To profile debug theory\_seq use C:\\c3\\build\\z3.exe <filename> -T:10 -st -tr:seq

. To profile debug theory\_nseq use C:\\c3\\build\\z3.exe <filename> -T:10 -st smt.seq.solver=nseq -tr:seq

. QF\_S benchmarks are in C:\\c3\\tests\\non-incremental\\QF\_S



\# Task



. Pick 50 benchmarks from QF\_S

. Run theory\_seq, theory\_nseq and zipt on each benchmark

. Create a report with timing information and status (sat/unsat/unknown/bug/crash)

. Select at most 3 benchmarks where theory\_nseq is worse than either theory\_seq or zipt.

. profile these benchmarks using debug builds of z3 and zipt in trace mode.  Copy .z3-trace files to allow inspection.

. Use information from the trace files to create a report of what needs to be implemented for theory\_nseq based on zipt.

