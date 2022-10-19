# This script illustrates uses of proof logs over the Python interface.

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

def monitor_plain():
    print("Monitor all inferred clauses")
    s = Solver()
    s.from_string(example1)
    onc = OnClause(s, lambda pr, clause : print(pr, clause))
    print(s.check())

def log_instance(pr, clause):
    if pr.decl().name() == "inst":
        q = pr.arg(0).arg(0) # first argument is Not(q)
        for ch in pr.children():
            if ch.decl().name() == "bind":
                print("Binding")
                print(q)
                print(ch.children())
                break

def monitor_instances():
    print("Monitor just quantifier bindings")
    s = Solver()
    s.from_string(example1)
    onc = OnClause(s, log_instance)
    print(s.check())
    
def monitor_with_proofs():
    print("Monitor clauses annotated with detailed justifications")
    set_param(proof=True)
    s = Solver()
    s.from_string(example1)
    onc = OnClause(s, lambda pr, clause : print(pr, clause))
    print(s.check())

def monitor_new_core():
    print("Monitor proof objects from the new core")
    set_param("sat.euf", True)
    set_param("tactic.default_tactic", "sat")
    s = Solver()
    s.from_string(example1)
    onc = OnClause(s, lambda pr, clause : print(pr, clause))
    print(s.check())


if __name__ == "__main__":
    monitor_plain()
    monitor_instances()
    monitor_new_core()


# Monitoring with proofs cannot be done in the same session
#   monitor_with_proofs()
