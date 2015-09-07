/*++
Module Name:

    str_decl_plugin.h

Abstract:

    <abstract>

Author:

    Murphy Berzish (mtrberzi) 2015-09-02.

Revision History:

--*/
#ifndef _STR_DECL_PLUGIN_H_
#define _STR_DECL_PLUGIN_H_

#include"ast.h"

enum str_sort_kind {
   STRING_SORT,
};

enum str_op_kind {
    OP_STR, /* string constants */
    //
    OP_STRCAT,
    LAST_STR_OP
};

class str_decl_plugin : public decl_plugin {
protected:
    symbol m_strv_sym;
    sort * m_str_decl;

    func_decl * m_concat_decl;

    virtual void set_manager(ast_manager * m, family_id id);

    func_decl * mk_func_decl(decl_kind k);
public:
    str_decl_plugin();
    virtual ~str_decl_plugin();
    virtual void finalize();

    virtual decl_plugin * mk_fresh();
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range);

    app * mk_string(const char * val);

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);

    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);
    // TODO
};

class str_recognizers {
    family_id m_afid;
public:
    str_recognizers(family_id fid):m_afid(fid) {}
    family_id get_fid() const { return m_afid; }
    family_id get_family_id() const { return get_fid(); }

    bool is_string(expr const * n, const char ** val) const;
    bool is_string(expr const * n) const;
    // TODO
};

class str_util : public str_recognizers {
    ast_manager & m_manager;
    str_decl_plugin * m_plugin;
public:
    str_util(ast_manager & m);
    ast_manager & get_manager() const { return m_manager; }
    str_decl_plugin & plugin() { return *m_plugin; }

    app * mk_string(const char * val) {
        return m_plugin->mk_string(val);
    }
    // TODO
};

#endif /* _STR_DECL_PLUGIN_H_ */
