/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#ifndef SEQ_DECL_PLUGIN_H_
#define SEQ_DECL_PLUGIN_H_

#include "ast.h"


enum seq_sort_kind {
    SEQ_SORT,
    RE_SORT,
    STRING_SORT
};

enum seq_op_kind {
    OP_SEQ_UNIT,
    OP_SEQ_EMPTY,
    OP_SEQ_CONCAT,
    OP_SEQ_CONS,
    OP_SEQ_REV_CONS,
    OP_SEQ_HEAD,
    OP_SEQ_TAIL,
    OP_SEQ_LAST,
    OP_SEQ_FIRST,
    OP_SEQ_PREFIX_OF,
    OP_SEQ_SUFFIX_OF,
    OP_SEQ_SUBSEQ_OF,
    OP_SEQ_EXTRACT,
    OP_SEQ_NTH,
    OP_SEQ_LENGTH,

    OP_RE_PLUS,
    OP_RE_STAR,
    OP_RE_OPTION,
    OP_RE_RANGE,
    OP_RE_CONCAT,
    OP_RE_UNION,
    OP_RE_INTERSECT,
    OP_RE_COMPLEMENT,
    OP_RE_DIFFERENCE,
    OP_RE_LOOP,
    OP_RE_EMPTY_SET,
    OP_RE_FULL_SET,
    OP_RE_EMPTY_SEQ,
    OP_RE_OF_SEQ,
    OP_RE_OF_PRED,
    OP_RE_MEMBER,


    // string specific operators.
    OP_STRING_CONST,
    OP_STRING_CONCAT, 
    OP_STRING_LENGTH, 
    OP_STRING_SUBSTR, 
    OP_STRING_STRCTN, 
    OP_STRING_CHARAT, 
    OP_STRING_STRIDOF, 
    OP_STRING_STRREPL, 
    OP_STRING_PREFIX, 
    OP_STRING_SUFFIX, 
    OP_STRING_ITOS, 
    OP_STRING_STOI, 
    //OP_STRING_U16TOS, 
    //OP_STRING_STOU16, 
    //OP_STRING_U32TOS, 
    //OP_STRING_STOU32, 
    OP_STRING_IN_REGEXP, 
    OP_STRING_TO_REGEXP, 
    OP_REGEXP_CONCAT, 
    OP_REGEXP_UNION, 
    OP_REGEXP_INTER, 
    OP_REGEXP_STAR, 
    OP_REGEXP_PLUS, 
    OP_REGEXP_OPT, 
    OP_REGEXP_RANGE, 
    OP_REGEXP_LOOP, 
    
    LAST_SEQ_OP
};


    
class seq_decl_plugin : public decl_plugin {
    struct psig {
        symbol          m_name;
        unsigned        m_num_params;
        sort_ref_vector m_dom;
        sort_ref        m_range;
        psig(ast_manager& m, char const* name, unsigned n, unsigned dsz, sort* const* dom, sort* rng):
            m_name(name),
            m_num_params(n),
            m_dom(m),
            m_range(rng, m)
        {
            m_dom.append(dsz, dom);
        }
    };

    ptr_vector<psig> m_sigs;
    bool             m_init;
    symbol           m_stringc_sym;
    sort*            m_string;

    void match(psig& sig, unsigned dsz, sort* const* dom, sort* range, sort_ref& rng);

    bool match(ptr_vector<sort>& binding, sort* s, sort* sP);

    sort* apply_binding(ptr_vector<sort> const& binding, sort* s);

    bool is_sort_param(sort* s, unsigned& idx);

    void init();

    virtual void set_manager(ast_manager * m, family_id id);

public:
    seq_decl_plugin();

    virtual ~seq_decl_plugin() {}
    virtual void finalize();
    
    virtual decl_plugin * mk_fresh() { return alloc(seq_decl_plugin); }
    
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
    
    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
    
    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);
    
    virtual bool is_value(app * e) const;

    virtual bool is_unique_value(app * e) const { return is_value(e); }

    app* mk_string(symbol const& s);  
};

class seq_util {
    ast_manager& m;
    seq_decl_plugin& seq;
public:
    seq_util(ast_manager& m): 
        m(m), 
        seq(*static_cast<seq_decl_plugin*>(m.get_plugin(m.mk_family_id("seq")))) {        
    }
    ~seq_util() {}

    app* mk_string(symbol const& s);
};

#endif /* SEQ_DECL_PLUGIN_H_ */

