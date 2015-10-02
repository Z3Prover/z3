############################################
# Copyright (c) Microsoft Corporation. All Rights Reserved. 
# 
# Check if the given graph has a Hamiltonian cycle.
#
# Author: Ganesh Gopalakrishnan ganesh@cs.utah.edu
############################################
from z3 import *

def gencon(gr):
    """
    Input a graph as an adjacency list, e.g. {0:[1,2], 1:[2], 2:[1,0]}.
    Produces solver to check if the given graph has
    a Hamiltonian cycle. Query the solver using s.check() and if sat,
    then s.model() spells out the cycle. Two example graphs from
    http://en.wikipedia.org/wiki/Hamiltonian_path are tested.

    =======================================================
    
    Explanation:
    
    Generate a list of Int vars. Constrain the first Int var ("Node 0") to be 0.
    Pick a node i, and attempt to number all nodes reachable from i to have a
    number one higher (mod L) than assigned to node i (use an Or constraint).
    
    =======================================================
    """
    L = len(gr)
    cv = [Int('cv%s'%i) for i in range(L)]
    s = Solver()
    s.add(cv[0]==0)
    for i in range(L):
        s.add(Or([cv[j]==(cv[i]+1)%L for j in gr[i]]))
    return s

def examples():
    # Example Graphs: The Dodecahedral graph from http://en.wikipedia.org/wiki/Hamiltonian_path
    grdodec = { 0: [1, 4, 5],
                1: [0, 7, 2],
                2: [1, 9, 3],
                3: [2, 11, 4],
                4: [3, 13, 0],
                5: [0, 14, 6],
                6: [5, 16, 7],
                7: [6, 8, 1],
                8: [7, 17, 9],
                9: [8, 10, 2],
                10: [9, 18, 11],
                11: [10, 3, 12],
                12: [11, 19, 13],
                13: [12, 14, 4],
                14: [13, 15, 5],
                15: [14, 16, 19],
                16: [6, 17, 15],
                17: [16, 8, 18],
                18: [10, 19, 17],
                19: [18, 12, 15] }
    import pprint
    pp = pprint.PrettyPrinter(indent=4)
    pp.pprint(grdodec)
    
    sdodec=gencon(grdodec)
    print(sdodec.check())
    print(sdodec.model())
    # =======================================================
    # See http://en.wikipedia.org/wiki/Hamiltonian_path for the Herschel graph
    # being the smallest possible polyhdral graph that does not have a Hamiltonian
    # cycle.
    #
    grherschel = { 0: [1, 9, 10, 7],
                   1: [0, 8, 2],
                   2: [1, 9, 3],
                   3: [2, 8, 4],
                   4: [3, 9, 10, 5],
                   5: [4, 8, 6],
                   6: [5, 10, 7],
                   7: [6, 8, 0],
                   8: [1, 3, 5, 7],
                   9: [2, 0, 4],
                   10: [6, 4, 0] }
    pp.pprint(grherschel)
    sherschel=gencon(grherschel)
    print(sherschel.check())
    # =======================================================

if __name__ == "__main__":
    examples()

