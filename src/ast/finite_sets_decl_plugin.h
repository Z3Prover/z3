/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_sets_decl_plugin.h

Abstract:
    Declaration plugin for finite sets signatures

Sort:
    FiniteSet(S)

Operators:
    set.empty : (FiniteSet S)
    set.union : (FiniteSet S) (FiniteSet S) -> (FiniteSet S)
    set.intersect : (FiniteSet S) (FiniteSet S) -> (FiniteSet S)
    set.difference : (FiniteSet S) (FiniteSet S) -> (FiniteSet S)
    set.singleton : S -> (FiniteSet S)
    set.in : S (FiniteSet S) -> Bool
    set.size : (FiniteSet S) -> Int
    set.subset : (FiniteSet S) (FiniteSet S) -> Bool
    set.map : (S -> T) (FiniteSet S) -> (FiniteSet T)
    set.filter : (S -> Bool) (FiniteSet S) -> (FiniteSet S)
    set.range : Int Int -> (FiniteSet Int)
   
--*/
