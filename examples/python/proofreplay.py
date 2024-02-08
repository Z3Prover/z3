# This script illustrates uses of proof replay and proof logs over the Python interface.

from z3 import *

example1 = """
(declare-sort T) 

(declare-fun subtype (T T) Bool)

;; subtype is reflexive
(assert (forall ((x T)) (subtype x x)))

;; subtype is antisymmetric
(assert (forall ((x T) (y T)) (=> (and (subtype x y)
                                       (subtype y x))
                                       (= x y))))
;; subtype is transitive
(assert (forall ((x T) (y T) (z T)) (=> (and (subtype x y)
                                             (subtype y z))
                                             (subtype x z))))
;; subtype has the tree-property
(assert (forall ((x T) (y T) (z T)) (=> (and (subtype x z)
                                             (subtype y z))
                                        (or (subtype x y)
                                            (subtype y x)))))

;; now we define a simple example using the axiomatization above.
(declare-const obj-type T)
(declare-const int-type T)
(declare-const real-type T)
(declare-const complex-type T)
(declare-const string-type T)

;; we have an additional axiom: every type is a subtype of obj-type
(assert (forall ((x T)) (subtype x obj-type)))

(assert (subtype int-type real-type))
(assert (subtype real-type complex-type))
(assert (not (subtype string-type real-type)))
(declare-const root-type T)
(assert (subtype obj-type root-type))
"""

if __name__ == "__main__":
    print("Solve and log inferences")
    print("--------------------------------------------------------")

    # inference logging, replay, and checking is supported for
    # the core enabled by setting sat.euf = true.
    # setting the default tactic to 'sat' bypasses other tactics that could
    # end up using different solvers.     
    set_param("sat.euf", True)
    set_param("tactic.default_tactic", "sat")

    # Set a log file to trace inferences
    set_param("sat.smt.proof", "proof_log.smt2")
    s = Solver()
    s.from_string(example1)
    print(s.check())
    print(s.statistics())
    print("Parse the logged inferences and replay them")
    print("--------------------------------------------------------")

    # Reset the log file to an invalid (empty) file name.
    set_param("sat.smt.proof", "")

    # Turn off proof checking. It is on by default when parsing proof logs.
    set_param("solver.proof.check", False)        
    s = Solver()
    onc = OnClause(s, lambda pr, clause : print(pr, clause))
    s.from_file("proof_log.smt2")

    
    print("Parse the logged inferences and check them")
    print("--------------------------------------------------------")
    s = Solver()

    # Now turn on proof checking. It invokes the self-validator.
    # The self-validator produces log lines of the form:
    # (proofs +tseitin 60 +alldiff 8 +euf 3 +rup 5 +inst 6 -quant 3 -inst 2)
    # (verified-smt
    #  (inst (forall (vars (x T) (y T) (z T)) (or (subtype (:var 2) (:var 1)) ...
    # The 'proofs' line summarizes inferences that were self-validated.
    # The pair +tseitin 60 indicates that 60 inferences were validated as Tseitin
    # encodings.
    # The pair -inst 2 indicates that two quantifier instantiations were not self-validated
    # They were instead validated using a call to SMT solving. A log for an smt invocation
    # is exemplified in the next line.
    # Note that the pair +inst 6 indicates that 6 quantifier instantiations were validated
    # using a syntactic (cheap) check. Some quantifier instantiations based on quantifier elimination
    # are not simple substitutions and therefore a simple syntactic check does not suffice.
    set_param("solver.proof.check", True)
    s.from_file("proof_log.smt2")

    print("Verify and self-validate on the fly")
    print("--------------------------------------------------------")
    set_param("sat.smt.proof.check", True)
    s = Solver()
    s.from_string(example1)
    print(s.check())
    print(s.statistics())

    print("Verify and self-validate on the fly, but don't check rup")
    print("--------------------------------------------------------")
    set_param("sat.smt.proof.check", True)
    set_param("sat.smt.proof.check_rup", False)
    s = Solver()
    s.from_string(example1)
    print(s.check())
    print(s.statistics())

    

