/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    z3_ast_containers.h

Abstract:

    AST Containers

Author:

    Christoph M. Wintersteiger (cwinter) 2015-12-03

Notes:

--*/
#ifndef Z3_AST_CONTAINERS_H_
#define Z3_AST_CONTAINERS_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /*@{*/

    /** @name AST vectors */
    /*@{*/
    /**
       \brief Return an empty AST vector.

       \remark Reference counting must be used to manage AST vectors, even when the Z3_context was
       created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_ast_vector', AST_VECTOR, (_in(CONTEXT),))
    */
    Z3_ast_vector Z3_API Z3_mk_ast_vector(Z3_context c);

    /**
       \brief Increment the reference counter of the given AST vector.

       def_API('Z3_ast_vector_inc_ref', VOID, (_in(CONTEXT), _in(AST_VECTOR)))
    */
    void Z3_API Z3_ast_vector_inc_ref(Z3_context c, Z3_ast_vector v);

    /**
       \brief Decrement the reference counter of the given AST vector.

       def_API('Z3_ast_vector_dec_ref', VOID, (_in(CONTEXT), _in(AST_VECTOR)))
    */
    void Z3_API Z3_ast_vector_dec_ref(Z3_context c, Z3_ast_vector v);

    /**
       \brief Return the size of the given AST vector.

       def_API('Z3_ast_vector_size', UINT, (_in(CONTEXT), _in(AST_VECTOR)))
    */
    unsigned Z3_API Z3_ast_vector_size(Z3_context c, Z3_ast_vector v);

    /**
       \brief Return the AST at position \c i in the AST vector \c v.

       \pre i < Z3_ast_vector_size(c, v)

       def_API('Z3_ast_vector_get', AST, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT)))
    */
    Z3_ast Z3_API Z3_ast_vector_get(Z3_context c, Z3_ast_vector v, unsigned i);

    /**
       \brief Update position \c i of the AST vector \c v with the AST \c a.

       \pre i < Z3_ast_vector_size(c, v)

       def_API('Z3_ast_vector_set', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT), _in(AST)))
    */
    void Z3_API Z3_ast_vector_set(Z3_context c, Z3_ast_vector v, unsigned i, Z3_ast a);

    /**
       \brief Resize the AST vector \c v.

       def_API('Z3_ast_vector_resize', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT)))
    */
    void Z3_API Z3_ast_vector_resize(Z3_context c, Z3_ast_vector v, unsigned n);

    /**
       \brief Add the AST \c a in the end of the AST vector \c v. The size of \c v is increased by one.

       def_API('Z3_ast_vector_push', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(AST)))
    */
    void Z3_API Z3_ast_vector_push(Z3_context c, Z3_ast_vector v, Z3_ast a);

    /**
       \brief Translate the AST vector \c v from context \c s into an AST vector in context \c t.

       def_API('Z3_ast_vector_translate', AST_VECTOR, (_in(CONTEXT), _in(AST_VECTOR), _in(CONTEXT)))
    */
    Z3_ast_vector Z3_API Z3_ast_vector_translate(Z3_context s, Z3_ast_vector v, Z3_context t);

    /**
       \brief Convert AST vector into a string.

       def_API('Z3_ast_vector_to_string', STRING, (_in(CONTEXT), _in(AST_VECTOR)))
    */
    Z3_string Z3_API Z3_ast_vector_to_string(Z3_context c, Z3_ast_vector v);

    /*@}*/

    /** @name AST maps */
    /*@{*/
    /**
    \brief Return an empty mapping from AST to AST

    \remark Reference counting must be used to manage AST maps, even when the Z3_context was
    created using #Z3_mk_context instead of #Z3_mk_context_rc.

    def_API('Z3_mk_ast_map', AST_MAP, (_in(CONTEXT),) )
    */
    Z3_ast_map Z3_API Z3_mk_ast_map(Z3_context c);

    /**
    \brief Increment the reference counter of the given AST map.

    def_API('Z3_ast_map_inc_ref', VOID, (_in(CONTEXT), _in(AST_MAP)))
    */
    void Z3_API Z3_ast_map_inc_ref(Z3_context c, Z3_ast_map m);

    /**
    \brief Decrement the reference counter of the given AST map.

    def_API('Z3_ast_map_dec_ref', VOID, (_in(CONTEXT), _in(AST_MAP)))
    */
    void Z3_API Z3_ast_map_dec_ref(Z3_context c, Z3_ast_map m);

    /**
    \brief Return true if the map \c m contains the AST key \c k.

    def_API('Z3_ast_map_contains', BOOL, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
    */
    Z3_bool Z3_API Z3_ast_map_contains(Z3_context c, Z3_ast_map m, Z3_ast k);

    /**
    \brief Return the value associated with the key \c k.

    The procedure invokes the error handler if \c k is not in the map.

    def_API('Z3_ast_map_find', AST, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
    */
    Z3_ast Z3_API Z3_ast_map_find(Z3_context c, Z3_ast_map m, Z3_ast k);

    /**
    \brief Store/Replace a new key, value pair in the given map.

    def_API('Z3_ast_map_insert', VOID, (_in(CONTEXT), _in(AST_MAP), _in(AST), _in(AST)))
    */
    void Z3_API Z3_ast_map_insert(Z3_context c, Z3_ast_map m, Z3_ast k, Z3_ast v);

    /**
    \brief Erase a key from the map.

    def_API('Z3_ast_map_erase', VOID, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
    */
    void Z3_API Z3_ast_map_erase(Z3_context c, Z3_ast_map m, Z3_ast k);

    /**
    \brief Remove all keys from the given map.

    def_API('Z3_ast_map_reset', VOID, (_in(CONTEXT), _in(AST_MAP)))
    */
    void Z3_API Z3_ast_map_reset(Z3_context c, Z3_ast_map m);

    /**
    \brief Return the size of the given map.

    def_API('Z3_ast_map_size', UINT, (_in(CONTEXT), _in(AST_MAP)))
    */
    unsigned Z3_API Z3_ast_map_size(Z3_context c, Z3_ast_map m);

    /**
    \brief Return the keys stored in the given map.

    def_API('Z3_ast_map_keys', AST_VECTOR, (_in(CONTEXT), _in(AST_MAP)))
    */
    Z3_ast_vector Z3_API Z3_ast_map_keys(Z3_context c, Z3_ast_map m);

    /**
    \brief Convert the given map into a string.

    def_API('Z3_ast_map_to_string', STRING, (_in(CONTEXT), _in(AST_MAP)))
    */
    Z3_string Z3_API Z3_ast_map_to_string(Z3_context c, Z3_ast_map m);
    /*@}*/
    /*@}*/

#ifdef __cplusplus
}
#endif // __cplusplus

#endif
