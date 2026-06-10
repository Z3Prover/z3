Overall plan is to implement a union-find based bisimulation algorithm for 
regular expressions in Z3. Work in the current xor branch.
The algorithm to do so is described in the paper \\git\\ere\\cav26\\paper.tex



* Read the \\git\\ere\\cav26\\paper.tex with the union-find algorithm.
* Add to seq\_rewriter preferrably separate class as seq\_rewriter.cpp is now big and messy.
* for union-find use util/union\_find.h
* add OP\_RE\_XOR operator to seq\_decl\_plugin with name "re.xor" that represents the xor of two regexes (symmetric difference).
* use it in theory\_seq when processing equalities between two ground regexes.
* use it in seq\_rewriter when simplifying equality between two ground regexes.



\- identify SMT benchmarks that use this. A particular set of benchmarks for this is with the following command. 

set OPTIONS1="-T:5 model\_validate=true"

&#x20;

gh workflow run ramon.yml -f runner=rise-runner-2 -f z3\_opts=%OPTIONS1% -f z3\_inputs=inputs/regex-equivalence -f job\_tag=regex-equivalence -f z3\_repo=Z3Prover/z3 -f z3\_ref=master


These particular benchmarks were in fact extracted from the C:\\git\\ere\\cav26\\benchmarks folder. 



Once implemented I want you to compare the performance of the baseline (old implementation) with the updated one, 
initially just of the given benchmarks that should give a pretty good baseline.



