/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    datatype_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2017-9-1 

Revision History:

    rewritten to support SMTLIB-2.6 parameters from
     Leonardo de Moura (leonardo) 2008-01-09.

--*/
#ifndef DATATYPE_DECL_PLUGIN_H_
#define DATATYPE_DECL_PLUGIN_H_

#include "ast/ast.h"
#include "util/buffer.h"
#include "util/symbol_table.h"
#include "util/obj_hashtable.h"


enum sort_kind {
    DATATYPE_SORT
};

enum op_kind {
    OP_DT_CONSTRUCTOR,
    OP_DT_RECOGNISER,
    OP_DT_IS,
    OP_DT_ACCESSOR,        
    OP_DT_UPDATE_FIELD,
    LAST_DT_OP
};

namespace datatype {

    class util;
    class def;
    class accessor;
    class constructor;
 

    class accessor {
        symbol    m_name;
        sort_ref  m_range;
        unsigned m_index;    // reference to recursive data-type may only get resolved after all mutually recursive data-types are procssed.
        constructor* m_constructor;
    public:
        accessor(ast_manager& m, symbol const& n, sort* range):
            m_name(n),
            m_range(range, m),
            m_index(UINT_MAX)
        {}
        accessor(ast_manager& m, symbol const& n, unsigned index):
            m_name(n),
            m_range(m),
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
        accessor* translate(ast_translation& tr);
    };

    class constructor {
        symbol           m_name;
        symbol           m_recognizer;
        ptr_vector<accessor> m_accessors;
        def*             m_def;
    public:
        constructor(symbol n, symbol const& r): m_name(n), m_recognizer(r) {}
        ~constructor();
        void add(accessor* a) { m_accessors.push_back(a); a->attach(this); }
        symbol const& name() const { return m_name; }
        symbol const& recognizer() const { return m_recognizer; }
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
        constructor* translate(ast_translation& tr);
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
            virtual sort_size eval(obj_map<sort, sort_size> const& S) = 0;
            
        };
        struct offset : public size {
            sort_size m_offset;
            offset(sort_size const& s): m_offset(s) {}
            ~offset() override {}
            size* subst(obj_map<sort,size*>& S) override { return this; }
            sort_size eval(obj_map<sort, sort_size> const& S) override { return m_offset; }
        };
        struct plus : public size {
            size* m_arg1, *m_arg2;
            plus(size* a1, size* a2): m_arg1(a1), m_arg2(a2) { a1->inc_ref(); a2->inc_ref();}
            ~plus() override { m_arg1->dec_ref(); m_arg2->dec_ref(); }
            size* subst(obj_map<sort,size*>& S) override;
            sort_size eval(obj_map<sort, sort_size> const& S) override;
        };
        struct times : public size {
            size* m_arg1, *m_arg2;
            times(size* a1, size* a2): m_arg1(a1), m_arg2(a2) { a1->inc_ref(); a2->inc_ref(); }
            ~times() override { m_arg1->dec_ref(); m_arg2->dec_ref(); }
            size* subst(obj_map<sort,size*>& S) override;
            sort_size eval(obj_map<sort, sort_size> const& S) override;
        };
        struct power : public size {
            size* m_arg1, *m_arg2;
            power(size* a1, size* a2): m_arg1(a1), m_arg2(a2) { a1->inc_ref(); a2->inc_ref(); }
            ~power() override { m_arg1->dec_ref(); m_arg2->dec_ref(); }
            size* subst(obj_map<sort,size*>& S) override;
            sort_size eval(obj_map<sort, sort_size> const& S) override;
        };
        struct sparam : public size {
            sort_ref m_param;
            sparam(sort_ref& p): m_param(p) {}
            ~sparam() override {}
            size* subst(obj_map<sort, size*>& S) override;
            sort_size eval(obj_map<sort, sort_size> const& S) override { return S[m_param]; }
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
            m_sort_size(nullptr),
            m_params(m, num_params, params), 
            m_sort(m)
        {}
        ~def() {
            if (m_sort_size) m_sort_size->dec_ref();
            for (constructor* c : m_constructors) dealloc(c);
            m_constructors.reset();
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
        void set_sort_size(param_size::size* p) { m_sort_size = p; p->inc_ref(); m_sort = nullptr; }
        def* translate(ast_translation& tr, util& u);
    };

    namespace decl {

        class plugin : public decl_plugin {
            mutable scoped_ptr<util> m_util;
            map<symbol, def*, symbol_hash_proc, symbol_eq_proc> m_defs; 
            map<symbol, unsigned, symbol_hash_proc, symbol_eq_proc> m_axiom_bases;
            unsigned                 m_id_counter;
            svector<symbol>          m_def_block;
            unsigned                 m_class_id;

            void inherit(decl_plugin* other_p, ast_translation& tr) override;

            void log_axiom_definitions(symbol const& s, sort * new_sort);

        public:
            plugin(): m_id_counter(0), m_class_id(0) {}
            ~plugin() override;

            void finalize() override;
        
            decl_plugin * mk_fresh() override { return alloc(plugin); }
        
            sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
        
            func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;
                
            expr * get_some_value(sort * s) override;
        
            bool is_fully_interp(sort * s) const override;
        
            bool is_value(app* e) const override;
        
            bool is_unique_value(app * e) const override { return is_value(e); }
        
            void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
                
            void begin_def_block() { m_class_id++; m_def_block.reset(); }

            void end_def_block();

            def* mk(symbol const& name, unsigned n, sort * const * params);

            void remove(symbol const& d);

            bool mk_datatypes(unsigned num_datatypes, def * const * datatypes, unsigned num_params, sort* const* sort_params, sort_ref_vector & new_sorts);

            def const& get_def(sort* s) const { return *(m_defs[datatype_name(s)]); }
            def& get_def(symbol const& s) { return *(m_defs[s]); }
            bool is_declared(sort* s) const { return m_defs.contains(datatype_name(s)); }
            unsigned get_axiom_base_id(symbol const& s) { return m_axiom_bases[s]; }
            util & u() const;

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

            func_decl * mk_is(
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

                
        obj_map<sort, ptr_vector<func_decl> *>      m_datatype2constructors;
        obj_map<sort, func_decl *>                  m_datatype2nonrec_constructor;
        obj_map<func_decl, ptr_vector<func_decl> *> m_constructor2accessors;
        obj_map<func_decl, func_decl *>             m_constructor2recognizer;
        obj_map<func_decl, func_decl *>             m_recognizer2constructor;
        obj_map<func_decl, func_decl *>             m_accessor2constructor;
        obj_map<sort, bool>                         m_is_recursive;
        obj_map<sort, bool>                         m_is_enum;
        mutable obj_map<sort, bool>                 m_is_fully_interp;
        mutable ast_ref_vector                      m_asts;
        ptr_vector<ptr_vector<func_decl> >          m_vectors;
        unsigned                                    m_start;
        mutable ptr_vector<sort>                    m_fully_interp_trail;
        
        func_decl * get_non_rec_constructor_core(sort * ty, ptr_vector<sort> & forbidden_set);

        friend class decl::plugin;

        bool is_recursive_core(sort * s) const;
        sort_size get_datatype_size(sort* s0);
        void compute_datatype_size_functions(svector<symbol> const& names);
        param_size::size* get_sort_size(sort_ref_vector const& params, sort* s);
        bool is_well_founded(unsigned num_types, sort* const* sorts);
        bool is_covariant(unsigned num_types, sort* const* sorts) const;
        bool is_covariant(ast_mark& mark, ptr_vector<sort>& subsorts, sort* s) const;
        def& get_def(symbol const& s) { return m_plugin->get_def(s); }
        void get_subsorts(sort* s, ptr_vector<sort>& sorts) const;        

    public:
        util(ast_manager & m);
        ~util();
        ast_manager & get_manager() const { return m; }
        // sort * mk_datatype_sort(symbol const& name, unsigned n, sort* const* params); 
        bool is_datatype(sort const* s) const { return is_sort_of(s, m_family_id, DATATYPE_SORT); }
        bool is_enum_sort(sort* s);
        bool is_recursive(sort * ty);
        bool is_constructor(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_CONSTRUCTOR); }
        bool is_recognizer(func_decl * f) const { return is_recognizer0(f) || is_is(f); }
        bool is_recognizer0(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_RECOGNISER); }
        bool is_is(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_IS); }
        bool is_accessor(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_ACCESSOR); }
        bool is_update_field(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_UPDATE_FIELD); }
        bool is_constructor(app * f) const { return is_app_of(f, m_family_id, OP_DT_CONSTRUCTOR); }
        bool is_constructor(expr* e) const { return is_app(e) && is_constructor(to_app(e)); }
        bool is_recognizer0(app * f) const { return is_app_of(f, m_family_id, OP_DT_RECOGNISER);} 
        bool is_is(app * f) const { return is_app_of(f, m_family_id, OP_DT_IS);} 
        bool is_is(expr * e) const { return is_app(e) && is_is(to_app(e)); }
        bool is_recognizer(app * f) const { return is_recognizer0(f) || is_is(f); }
        bool is_accessor(app * f) const { return is_app_of(f, m_family_id, OP_DT_ACCESSOR); }
        bool is_update_field(app * f) const { return is_app_of(f, m_family_id, OP_DT_UPDATE_FIELD); }
        app* mk_is(func_decl * c, expr *f);
        ptr_vector<func_decl> const * get_datatype_constructors(sort * ty);
        unsigned get_datatype_num_constructors(sort * ty);
        unsigned get_datatype_num_parameter_sorts(sort * ty);
        sort*  get_datatype_parameter_sort(sort * ty, unsigned idx);
        func_decl * get_non_rec_constructor(sort * ty);
        func_decl * get_constructor_recognizer(func_decl * constructor);
        func_decl * get_constructor_is(func_decl * constructor);
        ptr_vector<func_decl> const * get_constructor_accessors(func_decl * constructor);
        func_decl * get_accessor_constructor(func_decl * accessor);
        func_decl * get_recognizer_constructor(func_decl * recognizer) const;
        func_decl * get_update_accessor(func_decl * update) const;
        family_id get_family_id() const { return m_family_id; }
        bool are_siblings(sort * s1, sort * s2);
        bool is_func_decl(op_kind k, unsigned num_params, parameter const* params, func_decl* f);
        bool is_constructor_of(unsigned num_params, parameter const* params, func_decl* f);
        void reset();
        bool is_declared(sort* s) const;
        void display_datatype(sort *s, std::ostream& strm);
        bool is_fully_interp(sort * s) const;
        sort_ref_vector datatype_params(sort * s) const;
        unsigned get_constructor_idx(func_decl * f) const;
        unsigned get_recognizer_constructor_idx(func_decl * f) const;
        decl::plugin* get_plugin() { return m_plugin; }
        void get_defs(sort* s, ptr_vector<def>& defs);
        def const& get_def(sort* s) const;
        sort_ref mk_list_datatype(sort* elem, symbol const& name,
                                  func_decl_ref& cons, func_decl_ref& is_cons, 
                                  func_decl_ref& hd, func_decl_ref& tl, 
                                  func_decl_ref& nil, func_decl_ref& is_nil);
        sort_ref mk_pair_datatype(sort* a, sort* b, func_decl_ref& fst, func_decl_ref& snd, func_decl_ref& pair);
        sort_ref mk_tuple_datatype(svector<std::pair<symbol, sort*>> const& elems, symbol const& name, symbol const& test, func_decl_ref& tup, func_decl_ref_vector& accs);
    };

};

typedef datatype::accessor accessor_decl;
typedef datatype::constructor constructor_decl;
typedef datatype::def datatype_decl;
typedef datatype::decl::plugin datatype_decl_plugin;
typedef datatype::util datatype_util;

class type_ref {
    void * m_data;
public:
    type_ref():m_data(TAG(void *, nullptr, 1)) {}
    type_ref(int idx):m_data(BOXINT(void *, idx)) {}
    type_ref(sort * s):m_data(TAG(void *, s, 1)) {}
    
    bool is_idx() const { return GET_TAG(m_data) == 0; }
    bool is_sort() const { return GET_TAG(m_data) == 1; }
    sort * get_sort() const { return UNTAG(sort *, m_data); }
    int get_idx() const { return UNBOXINT(m_data); }
};

inline accessor_decl * mk_accessor_decl(ast_manager& m, symbol const & n, type_ref const & t) {
    if (t.is_idx()) {
        return alloc(accessor_decl, m, n, t.get_idx());
    }
    else {
        return alloc(accessor_decl, m, n, t.get_sort());
    }
}

inline constructor_decl * mk_constructor_decl(symbol const & n, symbol const & r, unsigned num_accessors, accessor_decl * * acs) {
    constructor_decl* c = alloc(constructor_decl, n, r);
    for (unsigned i = 0; i < num_accessors; ++i) {
        c->add(acs[i]);
    }
    return c;
}



// Remark: the datatype becomes the owner of the constructor_decls
datatype_decl * mk_datatype_decl(datatype_util& u, symbol const & n, unsigned num_params, sort*const* params, unsigned num_constructors, constructor_decl * const * cs);
inline void del_datatype_decl(datatype_decl * d) {}
inline void del_datatype_decls(unsigned num, datatype_decl * const * ds) {}


#endif /* DATATYPE_DECL_PLUGIN_H_ */
