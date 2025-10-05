/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_rewriter.h

Abstract:
    Rewriting Simplification for finite sets


Sampe rewrite rules:
    set.union s set.empty -> s
    set.intersect s set.empty -> set.empty
    set.in x (set.singleton y) -> x = y

Generally this module implements basic algebraic simplificaiton rules for finite sets
where the signature is defined in finite_sets_decl_plugin.h.
   
--*/
