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
        symbol   m_name;
        sort*    m_range;
        unsigned m_index;    // reference to recursive data-type may only get resolved after all mutually recursive data-types are procssed.
        constructor* m_constructor;
    public:
        accessor(symbol const& n, sort* range):
            m_name(n),
            m_range(range),
            m_index(UINT_MAX)
        {}
        accessor(symbol const& n, unsigned index):
            m_name(n),
            m_range(0),
            m_index(index)
        {}
        sort* range() const { return m_range; }
        void fix_range(sort_ref_vector const& dts);
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
        ptr_vector<accessor> m_accessors;
        def*             m_def;
    public:
        constructor(ast_manager& m, symbol n): m(m), m_name(n) {}
        ~constructor();
        void add(accessor* a) { m_accessors.push_back(a); a->attach(this); }
        symbol const& name() const { return m_name; }
        ptr_vector<accessor> const& accessors() const { return m_accessors; }
        ptr_vector<accessor>::const_iterator begin() const { return m_accessors.begin(); }
        ptr_vector<accessor>::const_iterator end() const { return m_accessors.end(); }
        ptr_vector<accessor>::iterator begin() { return m_accessors.begin(); }
        ptr_vector<accessor>::iterator end() { return m_accessors.end(); }
        func_decl_ref instantiate(sort_ref_vector const& ps) const;
        func_decl_ref instantiate(sort* dt) const;
        void attach(def* d) { m_def = d; }
        def const& get_def() const { return *m_def; }
        util& u() const;
    };

    namespace param_size {
        class size {
            unsigned m_ref;
        public:
            size(): m_ref(0) {}
            virtual ~size() {}
            void inc_ref() { ++m_ref; }
            void dec_ref() { --m_ref; if (m_ref == 0) dealloc(this); }
            static size* mk_offset(sort_size const& s); 
            static size* mk_param(sort_ref& p); 
            static size* mk_plus(size* a1, size* a2); 
            static size* mk_times(size* a1, size* a2); 
            static size* mk_plus(ptr_vector<size>& szs);
            static size* mk_times(ptr_vector<size>& szs);
            static size* mk_power(size* a1, size* a2);
            
            virtual size* subst(obj_map<sort, size*>& S) = 0;
            virtual sort_size fold(obj_map<sort, sort_size> const& S) = 0;
            
        };
        struct offset : public size {
            sort_size m_offset;
            offset(sort_size const& s): m_offset(s) {}
            virtual ~offset() {}
            virtual size* subst(obj_map<sort,size*>& S) { return this; }
            virtual sort_size fold(obj_map<sort, sort_size> const& S) { return m_offset; }
        };
        struct plus : public size {
            size* m_arg1, *m_arg2;
            plus(size* a1, size* a2): m_arg1(a1), m_arg2(a2) { a1->inc_ref(); a2->inc_ref();}
            virtual ~plus() { m_arg1->dec_ref(); m_arg2->dec_ref(); }
            virtual size* subst(obj_map<sort,size*>& S) { return mk_plus(m_arg1->subst(S), m_arg2->subst(S)); }
            virtual sort_size fold(obj_map<sort, sort_size> const& S) { 
                sort_size s1 = m_arg1->fold(S);
                sort_size s2 = m_arg2->fold(S);
                if (s1.is_infinite()) return s1;
                if (s2.is_infinite()) return s2;
                if (s1.is_very_big()) return s1;
                if (s2.is_very_big()) return s2;
                rational r = rational(s1.size(), rational::ui64()) + rational(s2.size(), rational::ui64());
                return sort_size(r);
            }
        };
        struct times : public size {
            size* m_arg1, *m_arg2;
            times(size* a1, size* a2): m_arg1(a1), m_arg2(a2) { a1->inc_ref(); a2->inc_ref(); }
            virtual ~times() { m_arg1->dec_ref(); m_arg2->dec_ref(); }
            virtual size* subst(obj_map<sort,size*>& S) { return mk_times(m_arg1->subst(S), m_arg2->subst(S)); }
            virtual sort_size fold(obj_map<sort, sort_size> const& S) { 
                sort_size s1 = m_arg1->fold(S);
                sort_size s2 = m_arg2->fold(S);
                if (s1.is_infinite()) return s1;
                if (s2.is_infinite()) return s2;
                if (s1.is_very_big()) return s1;
                if (s2.is_very_big()) return s2;
                rational r = rational(s1.size(), rational::ui64()) * rational(s2.size(), rational::ui64());
                return sort_size(r);
            }
        };
        struct power : public size {
            size* m_arg1, *m_arg2;
            power(size* a1, size* a2): m_arg1(a1), m_arg2(a2) { a1->inc_ref(); a2->inc_ref(); }
            virtual ~power() { m_arg1->dec_ref(); m_arg2->dec_ref(); }
            virtual size* subst(obj_map<sort,size*>& S) { return mk_power(m_arg1->subst(S), m_arg2->subst(S)); }
            virtual sort_size fold(obj_map<sort, sort_size> const& S) { 
                sort_size s1 = m_arg1->fold(S);
                sort_size s2 = m_arg2->fold(S);
                // s1^s2
                if (s1.is_infinite()) return s1;
                if (s2.is_infinite()) return s2;
                if (s1.is_very_big()) return s1;
                if (s2.is_very_big()) return s2;
                if (s1.size() == 1) return s1;
                if (s2.size() == 1) return s1;
                if (s1.size() > (2 << 20) || s2.size() > 10) return sort_size::mk_very_big();
                rational r = ::power(rational(s1.size(), rational::ui64()), static_cast<unsigned>(s2.size()));
                return sort_size(r);
            }
        };
        struct sparam : public size {
            sort_ref m_param;
            sparam(sort_ref& p): m_param(p) {}
            virtual ~sparam() {}
            virtual size* subst(obj_map<sort,size*>& S) { return S[m_param]; }
            virtual sort_size fold(obj_map<sort, sort_size> const& S) { return S[m_param]; }
        };
    };

    class def {
        ast_manager&        m;
        util&               m_util;
        symbol              m_name;
        unsigned            m_class_id;
        param_size::size*   m_sort_size;
        sort_ref_vector     m_params;
        mutable sort_ref    m_sort;
        ptr_vector<constructor> m_constructors;
    public:
        def(ast_manager& m, util& u, symbol const& n, unsigned class_id, unsigned num_params, sort * const* params):
            m(m),
            m_util(u),
            m_name(n),
            m_class_id(class_id),            
            m_sort_size(0),
            m_params(m, num_params, params), 
            m_sort(m)
        {}
        ~def() {
            if (m_sort_size) m_sort_size->dec_ref();
        }
        void add(constructor* c) {
            m_constructors.push_back(c);
            c->attach(this);
        }
        symbol const& name() const { return m_name; }
        unsigned id() const { return m_class_id; }
        sort_ref instantiate(sort_ref_vector const& ps) const;
        ptr_vector<constructor> const& constructors() const { return m_constructors; }
        ptr_vector<constructor>::const_iterator begin() const { return m_constructors.begin(); }
        ptr_vector<constructor>::const_iterator end() const { return m_constructors.end(); }
        ptr_vector<constructor>::iterator begin() { return m_constructors.begin(); }
        ptr_vector<constructor>::iterator end() { return m_constructors.end(); }
        sort_ref_vector const& params() const { return m_params; }
        util& u() const { return m_util; }
        param_size::size* sort_size() { return m_sort_size; }
        void set_sort_size(param_size::size* p) { m_sort_size = p; p->inc_ref(); }
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

            def const& get_def(sort* s) const { return *(m_defs[datatype_name(s)]); }
            def& get_def(symbol const& s) { return *(m_defs[s]); }

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
        void compute_datatype_size_functions(svector<symbol> const& names);
        param_size::size* get_sort_size(sort_ref_vector const& params, sort* s);
        bool is_well_founded(unsigned num_types, sort* const* sorts);
        def const& get_def(sort* s) const;
        def& get_def(symbol const& s) { return m_plugin->get_def(s); }
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

