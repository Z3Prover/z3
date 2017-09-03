/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datatype_decl_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09.

Revision History:

--*/
#ifndef DATATYPE_DECL_PLUGIN2_H_
#define DATATYPE_DECL_PLUGIN2_H_

#include "ast/ast.h"
#include "util/buffer.h"
#include "util/symbol_table.h"
#include "util/obj_hashtable.h"

namespace datatype {

    class util;
    class def;
    class accessor;
    class constructor;

    enum sort_kind {
        DATATYPE_SORT
    };
    
    enum op_kind {
        OP_DT_CONSTRUCTOR,
        OP_DT_RECOGNISER,
        OP_DT_ACCESSOR,
        OP_DT_UPDATE_FIELD,
        LAST_DT_OP
    };

    class accessor {
        ast_manager& m;
        symbol   m_name;
        sort_ref m_domain;
        sort_ref m_range;
        constructor* m_constructor;
    public:
        accessor(ast_manager& m, symbol const& n):
            m(m),
            m_name(n),
            m_domain(m),
            m_range(m)
        {}
        sort* range() const { return m_range; }
        symbol const& name() const { return m_name; }
        func_decl_ref instantiate(sort_ref_vector const& ps) const;
        func_decl_ref instantiate(sort* dt) const;
        void attach(constructor* d) { m_constructor = d; }
        constructor const& get_constructor() const { return *m_constructor; }
        def const& get_def() const;
        util& u() const;
    };

    class constructor {
        ast_manager&     m;
        symbol           m_name;
        vector<accessor> m_accessors;
        def*             m_def;
    public:
        constructor(ast_manager& m, symbol n): m(m), m_name(n) {}
        void add(accessor& a) { m_accessors.push_back(a); a.attach(this); }
        symbol const& name() const { return m_name; }
        vector<accessor> const& accessors() const { return m_accessors; }
        vector<accessor>::const_iterator begin() const { return m_accessors.begin(); }
        vector<accessor>::const_iterator end() const { return m_accessors.end(); }
        func_decl_ref instantiate(sort_ref_vector const& ps) const;
        func_decl_ref instantiate(sort* dt) const;
        void attach(def* d) { m_def = d; }
        def const& get_def() const { return *m_def; }
        util& u() const;
    };

    class def {
        ast_manager&        m;
        util&               m_util;
        symbol              m_name;
        unsigned            m_class_id;
        sort_ref_vector     m_params;
        mutable sort_ref    m_sort;
        vector<constructor> m_constructors;
    public:
        def(ast_manager& m, util& u, symbol const& n, unsigned class_id, unsigned num_params, sort * const* params):
            m(m),
            m_util(u),
            m_name(n),
            m_class_id(class_id),            
            m_params(m, num_params, params), 
            m_sort(m)
        {}
        void add(constructor& c) {
            m_constructors.push_back(c);
            c.attach(this);
        }
        symbol const& name() const { return m_name; }
        unsigned id() const { return m_class_id; }
        sort_ref instantiate(sort_ref_vector const& ps) const;
        vector<constructor> const& constructors() const { return m_constructors; }
        vector<constructor>::const_iterator begin() const { return m_constructors.begin(); }
        vector<constructor>::const_iterator end() const { return m_constructors.end(); }
        sort_ref_vector const& params() const { return m_params; }
        util& u() const { return m_util; }
    };

    namespace decl {

        class plugin : public decl_plugin {
            mutable scoped_ptr<util> m_util;
            map<symbol, def*, symbol_hash_proc, symbol_eq_proc> m_defs; 
            svector<symbol>          m_def_block;
            unsigned                 m_class_id;
            util & u() const;
        public:
            plugin(): m_class_id(0) {}
            virtual ~plugin();

            virtual void finalize();
        
            virtual decl_plugin * mk_fresh() { return alloc(plugin); }
        
            virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
        
            virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                             unsigned arity, sort * const * domain, sort * range);
                
            virtual expr * get_some_value(sort * s);
        
            virtual bool is_fully_interp(sort * s) const;
        
            virtual bool is_value(app* e) const;
        
            virtual bool is_unique_value(app * e) const { return is_value(e); }
        
            virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
                
            void begin_def_block() { m_class_id++; m_def_block.reset(); }

            void end_def_block();

            def& add(symbol const& name, unsigned n, sort * const * params);

            void del(symbol const& d);

            def const& get_def(sort* s) const { def* d = 0; VERIFY(m_defs.find(datatype_name(s), d)); return *d; }

        private:
            bool is_value_visit(expr * arg, ptr_buffer<app> & todo) const;
        
            func_decl * mk_update_field(
                unsigned num_parameters, parameter const * parameters, 
                unsigned arity, sort * const * domain, sort * range);

            func_decl * mk_constructor(
                unsigned num_parameters, parameter const * parameters, 
                unsigned arity, sort * const * domain, sort * range);

            func_decl * mk_accessor(
                unsigned num_parameters, parameter const * parameters, 
                unsigned arity, sort * const * domain, sort * range);

            func_decl * mk_recognizer(
                unsigned num_parameters, parameter const * parameters, 
                unsigned arity, sort * const * domain, sort * range);

            symbol datatype_name(sort * s) const {
                //SASSERT(u().is_datatype(s));
                return s->get_parameter(0).get_symbol();
            }
            
        };
    }

    class util {
        ast_manager & m;
        family_id     m_family_id;
        mutable decl::plugin* m_plugin;

        
        func_decl * get_constructor(sort * ty, unsigned c_id) const;
        
        obj_map<sort, ptr_vector<func_decl> *>      m_datatype2constructors;
        obj_map<sort, func_decl *>                  m_datatype2nonrec_constructor;
        obj_map<func_decl, ptr_vector<func_decl> *> m_constructor2accessors;
        obj_map<func_decl, func_decl *>             m_constructor2recognizer;
        obj_map<func_decl, func_decl *>             m_recognizer2constructor;
        obj_map<func_decl, func_decl *>             m_accessor2constructor;
        obj_map<sort, bool>                         m_is_recursive;
        obj_map<sort, bool>                         m_is_enum;
        mutable obj_map<sort, bool>                         m_is_fully_interp;
        mutable ast_ref_vector                      m_asts;
        ptr_vector<ptr_vector<func_decl> >          m_vectors;
        unsigned                                    m_start;
        mutable ptr_vector<sort>                            m_fully_interp_trail;
        
        func_decl * get_non_rec_constructor_core(sort * ty, ptr_vector<sort> & forbidden_set);
        func_decl * get_constructor(sort * ty, unsigned c_id);

        friend class decl::plugin;

        bool is_recursive_core(sort * s) const;
        sort_size get_datatype_size(sort* s0);
        bool is_well_founded(unsigned num_types, sort* const* sorts);
        def const& get_def(sort* s) const;
        void get_subsorts(sort* s, ptr_vector<sort>& sorts) const;        

    public:
        util(ast_manager & m);
        ~util();
        ast_manager & get_manager() const { return m; }
        bool is_datatype(sort const* s) const { return is_sort_of(s, m_family_id, DATATYPE_SORT); }
        bool is_enum_sort(sort* s);
        bool is_recursive(sort * ty);
        bool is_constructor(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_CONSTRUCTOR); }
        bool is_recognizer(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_RECOGNISER); }
        bool is_accessor(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_ACCESSOR); }
        bool is_update_field(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_UPDATE_FIELD); }
        bool is_constructor(app * f) const { return is_app_of(f, m_family_id, OP_DT_CONSTRUCTOR); }
        bool is_recognizer(app * f) const { return is_app_of(f, m_family_id, OP_DT_RECOGNISER); }
        bool is_accessor(app * f) const { return is_app_of(f, m_family_id, OP_DT_ACCESSOR); }
        bool is_update_field(app * f) const { return is_app_of(f, m_family_id, OP_DT_UPDATE_FIELD); }
        ptr_vector<func_decl> const & get_datatype_constructors(sort * ty);
        unsigned get_datatype_num_constructors(sort * ty);
        unsigned get_datatype_num_parameter_sorts(sort * ty);
        sort*  get_datatype_parameter_sort(sort * ty, unsigned idx);
        func_decl * get_non_rec_constructor(sort * ty);
        func_decl * get_constructor_recognizer(func_decl * constructor);
        ptr_vector<func_decl> const & get_constructor_accessors(func_decl * constructor);
        func_decl * get_accessor_constructor(func_decl * accessor);
        func_decl * get_recognizer_constructor(func_decl * recognizer);
        family_id get_family_id() const { return m_family_id; }
        bool are_siblings(sort * s1, sort * s2);
        bool is_func_decl(op_kind k, unsigned num_params, parameter const* params, func_decl* f);
        bool is_constructor_of(unsigned num_params, parameter const* params, func_decl* f);
        void reset();
        void display_datatype(sort *s, std::ostream& strm);
        bool is_fully_interp(sort * s) const;
        sort_ref_vector datatype_params(sort * s) const;
    };

};

#endif /* DATATYPE_DECL_PLUGIN_H_ */

