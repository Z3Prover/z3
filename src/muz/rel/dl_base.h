/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_base.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-23.

Revision History:

--*/
#ifndef DL_BASE_H_
#define DL_BASE_H_

#define DL_LEAK_HUNTING 0

#include<iosfwd>

#include"ast.h"
#include"map.h"
#include"vector.h"
#include"ref.h"
#include"dl_util.h"
#include"dl_context.h"

namespace datalog {

    class context;
    class relation_manager;

    template<typename T>
    class scoped_rel {
        T* m_t;
    public:
        scoped_rel(T* t) : m_t(t) {}
        ~scoped_rel() { if (m_t) { universal_delete(m_t); } }
        scoped_rel() : m_t(0) {}
        scoped_rel& operator=(T* t) { if (m_t && t != m_t) { universal_delete(m_t); } m_t = t;  return *this; }
        T* operator->() { return m_t; }
        const T* operator->() const { return m_t; }
        T& operator*() { return *m_t; }
        const T& operator*() const { return *m_t; }
        operator bool() const { return m_t!=0; }
        T* get() const { return m_t; }
        /**
           \brief Remove object from \c scoped_rel without deleting it.
        */
        T* release() {
            T* res = m_t;
            m_t = 0;
            return res;
        }
    };

    ast_manager & get_ast_manager_from_rel_manager(const relation_manager & rm);
    context & get_context_from_rel_manager(const relation_manager & rm);

    typedef func_decl_set decl_set;

#if DL_LEAK_HUNTING
    void leak_guard_check(const symbol & s);
#endif

    void universal_delete(relation_base* ptr);
    void universal_delete(table_base* ptr);
    void dealloc_ptr_vector_content(ptr_vector<relation_base> & v);


    /**
       Termplate class containing common infrastructure for relations and tables
    */
    template<class Traits>
    struct tr_infrastructure {

        typedef typename Traits::plugin plugin;
        typedef typename Traits::base_object base_object;
        typedef typename Traits::element element;
        typedef typename Traits::fact fact;
        typedef typename Traits::sort sort;
        typedef typename Traits::signature_base_base signature_base_base; //this must be a vector-like type
        typedef typename Traits::signature signature; //this must be a vector-like type

        /**
           The client submits an initial class to be used as a base for signature. Then we extend it by
           the common signature methods into a signature_base class which then the client inherits from
           to obtain the actual signature class.
        */
        class signature_base : public signature_base_base {
        public:
            bool operator==(const signature & o) const {
                unsigned n=signature_base_base::size();
                if(n!=o.size()) {
                    return false;
                }
                return memcmp(this->c_ptr(), o.c_ptr(), n*sizeof(sort))==0;
                /*for(unsigned i=0; i<n; i++) {
                    if((*this)[i]!=o[i]) {
                        return false;
                    }
                }
                return true;*/
            }

            /**
               \brief Into \c result assign signature of result of join of relations with signatures \c s1 
               and \c s2.
            */
            static void from_join(const signature & s1, const signature & s2, unsigned col_cnt, 
                    const unsigned * cols1, const unsigned * cols2, signature & result) {
                result.reset();

                unsigned s1sz=s1.size();
                for(unsigned i=0; i<s1sz; i++) {
                    result.push_back(s1[i]);
                }
                unsigned s2sz=s2.size();
                for(unsigned i=0; i<s2sz; i++) {
                    result.push_back(s2[i]);
                }
#if Z3DEBUG
                for(unsigned i=0; i<col_cnt; i++) {
                    SASSERT(cols1[i]<s1sz);
                    SASSERT(cols2[i]<s2sz);
                }
#endif
            }

            /**
               \brief Into \c result assign signature projected from \c src.

               The array of removed columns must be sorted in ascending order.
            */
            static void from_project(const signature & src, unsigned col_cnt, 
                    const unsigned * removed_cols, signature & result) {
                result = src;
                project_out_vector_columns(result, col_cnt, removed_cols);
            }

            static void from_join_project(const signature & s1, const signature & s2, unsigned joined_col_cnt, 
                    const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
                    const unsigned * removed_cols, signature & result) {
                signature aux(s1);
                from_join(s1, s2, joined_col_cnt, cols1, cols2, aux);
                from_project(aux, removed_col_cnt, removed_cols, result);
            }

            /**
               \brief Into \c result assign signature \c src with reordered columns.

               For description of the permutation format see \c relation_base::rename
            */
            static void from_rename(const signature & src, unsigned cycle_len, 
                    const unsigned * permutation_cycle, signature & result) {
                SASSERT(cycle_len>=2);
                result=src;

                permutate_by_cycle(result, cycle_len, permutation_cycle);
            }

            /**
               \brief Into \c result assign signature \c src with reordered columns.
            */
            static void from_permutation_rename(const signature & src, 
                    const unsigned * permutation, signature & result) {
                result.reset();
                unsigned n = src.size();
                for(unsigned i=0; i<n; i++) {
                    result.push_back(src[permutation[i]]);
                }
            }
        };

        class base_fn {
        public:
            base_fn() {}
            virtual ~base_fn() {}
        private:
            //private and undefined copy constructor and operator= to avoid copying
            base_fn(const base_fn &);
            base_fn& operator=(const base_fn &);
        };

        class join_fn : public base_fn {
        public:
            virtual base_object * operator()(const base_object & t1, const base_object & t2) = 0;
        };

        class transformer_fn : public base_fn {
        public:
            virtual base_object * operator()(const base_object & t) = 0;
        };

        class union_fn : public base_fn {
        public:
            virtual void operator()(base_object & tgt, const base_object & src, base_object * delta) = 0;

            void operator()(base_object & tgt, const base_object & src) {
                (*this)(tgt, src, static_cast<base_object *>(0));
            }
        };

        /**
           \brief Mutator for relations that propagate constraints as a consequence of
           combination.

           - supports_attachment
             is used to query the mutator if it allows communicating 
             constraints to relations of the kind of the relation.

           - attach 
             is used to associate downstream clients. 
             It assumes that the relation kind is supported (supports_kind returns true)
        */
        class mutator_fn : public base_fn {
        public:
            virtual void operator()(base_object & t) = 0;

            virtual bool supports_attachment(base_object& other) { return false; }

            virtual void attach(base_object& other) { UNREACHABLE(); }
        };

        class intersection_filter_fn : public base_fn {
        public:
            virtual void operator()(base_object & t, const base_object & intersected_obj) = 0;
        };

        class intersection_join_filter_fn : public base_fn {
        public:
            virtual void operator()(base_object & t, const base_object & inter1, const base_object& inter2) = 0;
        };

        class default_join_project_fn;

        /**
           \brief Plugin class providing factory functions for a table and operations on it.

           The functor factory functions (mk_*_fn) may return 0. It means that the plugin
           is unable to perform the operation on relations/tables of the particular kind.
        */
        class plugin_object {
            friend class relation_manager;
            friend class check_table_plugin;
            friend class check_relation_plugin;

            family_id m_kind;
            symbol    m_name;
            relation_manager & m_manager;
        protected:
            plugin_object(symbol const& name, relation_manager & manager) 
                : m_kind(null_family_id), m_name(name), m_manager(manager) {}

            /**
               \brief Check \c r is of the same kind as the plugin.
            */
            bool check_kind(base_object const& r) const { return &r.get_plugin()==this; }
        public:
            virtual ~plugin_object() {}

            virtual void initialize(family_id fid) { m_kind = fid; }

            family_id get_kind() const { return m_kind; }

            symbol const& get_name() const { return m_name; }

            relation_manager & get_manager() const { return m_manager; }
            ast_manager& get_ast_manager() const { return datalog::get_ast_manager_from_rel_manager(m_manager); }
            context& get_context() const { return datalog::get_context_from_rel_manager(m_manager); }

            virtual bool can_handle_signature(const signature & s) = 0;

            virtual bool can_handle_signature(const signature & s, family_id kind) {
                return can_handle_signature(s);
            }

            /**
               \brief Create empty table/relation with given signature and return pointer to it. 

               Precondition: can_handle_signature(s)==true
            */
            virtual base_object * mk_empty(const signature & s) = 0;

            /**
               \brief Create empty table/relation with signature \c s and kind \c kind.

               Precondition: &orig.get_plugin()==this
            */
            virtual base_object * mk_empty(const signature & s, family_id kind) {
                SASSERT(kind==get_kind()); //if plugin uses multiple kinds, this function needs to be overriden
                return mk_empty(s);
            }

            /**
               \brief Create empty table/relation of the same specification as \c orig and return pointer to it. 

               Precondition: &orig.get_plugin()==this
            */
            virtual base_object * mk_empty(const base_object & orig) {
                return mk_empty(orig.get_signature(), orig.get_kind());
            }

            /**
               \brief Create full table/relation with given signature and return pointer to it. 

               Precondition: can_handle_signature(s)==true
            */
            virtual base_object * mk_full(func_decl* p, const signature & s) {
                base_object * aux = mk_empty(s);
                base_object * res = aux->complement(p);
                aux->deallocate();
                return res;
            }

            virtual base_object * mk_full(func_decl* p, const signature & s, family_id kind) {
                if (kind == get_kind() || kind == null_family_id) {
                    return mk_full(p, s);
                }
                base_object * aux = mk_empty(s, kind);
                base_object * res = aux->complement(p);
                aux->deallocate();
                return res;
            }

        protected:
            //see \c relation_manager for documentation of the operations


            virtual join_fn * mk_join_fn(const base_object & t1, const base_object & t2,
                unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) { return 0; }

            virtual transformer_fn * mk_project_fn(const base_object & t, unsigned col_cnt, 
                const unsigned * removed_cols) { return 0; }

            virtual join_fn * mk_join_project_fn(const base_object & t1, const base_object & t2,
                    unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
                    unsigned removed_col_cnt, const unsigned * removed_cols) { return 0; }

            virtual transformer_fn * mk_rename_fn(const base_object & t, unsigned permutation_cycle_len, 
                const unsigned * permutation_cycle) { return 0; }

            virtual transformer_fn * mk_permutation_rename_fn(const base_object & t,
                const unsigned * permutation) { return 0; }

        public:
            virtual union_fn * mk_union_fn(const base_object & tgt, const base_object & src, 
                const base_object * delta) { return 0; }
        protected:

            virtual union_fn * mk_widen_fn(const base_object & tgt, const base_object & src, 
                const base_object * delta) { return 0; }

            virtual mutator_fn * mk_filter_identical_fn(const base_object & t, unsigned col_cnt, 
                const unsigned * identical_cols) { return 0; }

            virtual mutator_fn * mk_filter_equal_fn(const base_object & t, const element & value, 
                unsigned col) { return 0; }

            virtual mutator_fn * mk_filter_interpreted_fn(const base_object & t, app * condition)
            { return 0; }

            virtual transformer_fn * mk_filter_interpreted_and_project_fn(const base_object & t,
                app * condition, unsigned removed_col_cnt, const unsigned * removed_cols)
            { return 0; }

            virtual transformer_fn * mk_select_equal_and_project_fn(const base_object & t, 
                    const element & value, unsigned col) { return 0; }

            virtual intersection_filter_fn * mk_filter_by_intersection_fn(const base_object & t, 
                const base_object & src, unsigned joined_col_cnt, 
                const unsigned * t_cols, const unsigned * src_cols) 
            { return 0; }


            virtual intersection_filter_fn * mk_filter_by_negation_fn(const base_object & t, 
                const base_object & negated_obj, unsigned joined_col_cnt, 
                const unsigned * t_cols, const unsigned * negated_cols) 
            { return 0; }

            virtual intersection_join_filter_fn * mk_filter_by_negated_join_fn(
                const base_object & t, 
                const base_object & src1, 
                const base_object & src2, 
                unsigned_vector const& t_cols,
                unsigned_vector const& src_cols,
                unsigned_vector const& src1_cols,
                unsigned_vector const& src2_cols) 
            { return 0; }

        };

        class base_ancestor {
            plugin & m_plugin;
            signature m_signature;
            family_id m_kind;
#if DL_LEAK_HUNTING
            sort_ref m_leak_guard;
#endif
        protected:
            base_ancestor(plugin & p, const signature & s) 
                : m_plugin(p), m_signature(s), m_kind(p.get_kind()) 
#if DL_LEAK_HUNTING
                , m_leak_guard(p.get_ast_manager().mk_fresh_sort(p.get_name().bare_str()), p.get_ast_manager())
#endif
            {
#if DL_LEAK_HUNTING
                leak_guard_check(m_leak_guard->get_name());
#endif
            }

#if DL_LEAK_HUNTING
            base_ancestor(const base_ancestor & o) 
                    : m_plugin(o.m_plugin),
                    m_signature(o.m_signature),
                    m_kind(o.m_kind),
                    m_leak_guard(m_plugin.get_ast_manager().mk_fresh_sort(m_plugin.get_name().bare_str()), 
                        m_plugin.get_ast_manager()) {
                leak_guard_check(m_leak_guard->get_name());
            }
#endif

            virtual ~base_ancestor() {}

            void set_kind(family_id kind) { SASSERT(kind>=0); m_kind = kind; }

            /**
               Since the destructor is protected, we cannot use the \c dealloc macro.
            */
            void destroy() {
                SASSERT(this);
                this->~base_ancestor();
#if _DEBUG
                memory::deallocate(__FILE__, __LINE__, this);
#else
                memory::deallocate(this);
#endif
            }
        public:
            /**
               Deallocate the current object.

               Pointers and references to the current object become invalid after a call to this function.
            */
            virtual void deallocate() { 
                destroy();
            }
            /**
               It must hold that operations created for particular table/relation are able to operate on
               tables/relations of the same signature and kind. In most cases it is sufficient to use the kind
               of the plugin object.
               
               However, it there is some parameter that is not reflected in the signature, the plugin may need to 
               allocate different kind numbers to the tables is creates.
            */
            family_id get_kind() const { return m_kind; }
            const signature & get_signature() const { return m_signature; }
            plugin & get_plugin() const { return m_plugin; }
            relation_manager & get_manager() const { return get_plugin().get_manager(); }

            virtual bool empty() const = 0;
            /**
               \brief fast emptiness check. This may be partial.
               The requirement is that if fast_empty returns true 
               then the table or relation is in fact empty.
               It is allowed to return false even if the relation is empty.
            */
            virtual bool fast_empty() const { return empty(); }

            virtual void add_fact(const fact & f) = 0;
            /**
               \brief Like \c add_fact, only here the caller guarantees that the fact is not present in
               the table yet.
            */
            virtual void add_new_fact(const fact & f) {
                add_fact(f);
            }
            virtual bool contains_fact(const fact & f) const = 0;

            virtual void reset() = 0;

            /**
               \brief Return table/relation that contains the same data as the current one.
            */
            virtual base_object * clone() const = 0;

            virtual bool can_swap(const base_object & o) const { return false; }

            virtual void swap(base_object & o) { 
                std::swap(m_kind, o.m_kind);
#if DL_LEAK_HUNTING
                m_leak_guard = get_plugin().get_ast_manager().mk_fresh_sort(get_plugin().get_name().bare_str());
                o.m_leak_guard = get_plugin().get_ast_manager().mk_fresh_sort(get_plugin().get_name().bare_str());
                leak_guard_check(m_leak_guard->get_name());
                leak_guard_check(o.m_leak_guard->get_name());
#endif
            }

            virtual unsigned get_size_estimate_rows() const { return UINT_MAX; }
            virtual unsigned get_size_estimate_bytes() const { return UINT_MAX; }
            virtual bool knows_exact_size() const { return false; }
            unsigned num_columns() const { return get_signature().size(); }

            virtual void display(std::ostream & out) const = 0;
        };


        class convenient_join_fn : public join_fn {
            signature m_result_sig;
        protected:
            unsigned_vector m_cols1;
            unsigned_vector m_cols2;

            convenient_join_fn(const signature & o1_sig, const signature & o2_sig, unsigned col_cnt,
                const unsigned * cols1, const unsigned * cols2) 
                : m_cols1(col_cnt, cols1), 
                  m_cols2(col_cnt, cols2) {
                signature::from_join(o1_sig, o2_sig, col_cnt, cols1, cols2, m_result_sig);
            }

            const signature & get_result_signature() const { return m_result_sig; }
        };

        class convenient_join_project_fn : public join_fn {
            signature m_result_sig;
        protected:
            unsigned_vector m_cols1;
            unsigned_vector m_cols2;
            //it is non-const because it needs to be modified in sparse_table version of the join_project operator
            unsigned_vector m_removed_cols;

            convenient_join_project_fn(const signature & o1_sig, const signature & o2_sig, 
                    unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
                    unsigned removed_col_cnt, const unsigned * removed_cols) 
                    : m_cols1(joined_col_cnt, cols1), 
                    m_cols2(joined_col_cnt, cols2),
                    m_removed_cols(removed_col_cnt, removed_cols) {

                signature::from_join_project(o1_sig, o2_sig, joined_col_cnt, cols1, cols2, 
                    removed_col_cnt, removed_cols, m_result_sig);
            }

            const signature & get_result_signature() const { return m_result_sig; }
        };

        class convenient_transformer_fn : public transformer_fn {
            signature m_result_sig;
        protected:
            signature & get_result_signature() { return m_result_sig; }
            const signature & get_result_signature() const { return m_result_sig; }
        };

        class convenient_project_fn : public convenient_transformer_fn {
        protected:
            unsigned_vector m_removed_cols;

            convenient_project_fn(const signature & orig_sig, unsigned col_cnt, const unsigned * removed_cols) 
                    : m_removed_cols(col_cnt, removed_cols) {
                signature::from_project(orig_sig, col_cnt, removed_cols, 
                    convenient_transformer_fn::get_result_signature());
            }
        };

        class convenient_rename_fn : public convenient_transformer_fn {
        protected:
            const unsigned_vector m_cycle;

            convenient_rename_fn(const signature & orig_sig, unsigned cycle_len,
                const unsigned * permutation_cycle) 
                    : m_cycle(cycle_len, permutation_cycle) {
                signature::from_rename(orig_sig, cycle_len, permutation_cycle, 
                    convenient_transformer_fn::get_result_signature());
            }
        };

        class convenient_negation_filter_fn : public intersection_filter_fn {
        protected:
            unsigned m_joined_col_cnt;
            const unsigned_vector m_cols1;
            const unsigned_vector m_cols2;
            bool m_all_neg_bound; //all columns are bound at least once
            bool m_overlap; //one column in negated table is bound multiple times
            svector<bool> m_bound;

            convenient_negation_filter_fn(const base_object & tgt, const base_object & neg_t, 
                    unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols) 
                    : m_joined_col_cnt(joined_col_cnt), m_cols1(joined_col_cnt, t_cols), 
                    m_cols2(joined_col_cnt, negated_cols) {
                unsigned neg_sig_size = neg_t.get_signature().size();
                m_overlap = false;
                m_bound.resize(neg_sig_size, false);
                for(unsigned i=0; i<joined_col_cnt; i++) {
                    if(m_bound[negated_cols[i]]) {
                        m_overlap = true;
                    }
                    m_bound[negated_cols[i]]=true;
                }
                m_all_neg_bound = neg_sig_size<=joined_col_cnt && 
                    std::find(m_bound.begin(), m_bound.end(), false)== m_bound.end();
            }

            /**
               \brief Assign values in src to corresponding columns in tgt_neg. If one column should 
               be assigned two different values, return false; otherwise return true.

               Each negative column must correspond to exactly column in the first table.
            */
            template<typename T, typename U>
            void make_neg_bindings(T & tgt_neg, const U & src) const {
                SASSERT(m_all_neg_bound);
                SASSERT(!m_overlap);
                for(unsigned i=0; i<m_joined_col_cnt; i++) {
                    tgt_neg[m_cols2[i]]=src[m_cols1[i]];
                }
            }
            template<typename T, typename U>
            bool bindings_match(const T & tgt_neg, const U & src) const {
                for(unsigned i=0; i<m_joined_col_cnt; i++) {
                    if(tgt_neg[m_cols2[i]]!=src[m_cols1[i]]) {
                        return false;
                    }
                }
                return true;
            }
        };

        class identity_transformer_fn : public transformer_fn {
        public:
            virtual base_object * operator()(const base_object & t) {
                return t.clone();
            }
        };

        class identity_mutator_fn : public mutator_fn {
        public:
            virtual void operator()(base_object & t) {};
        };

        class identity_intersection_filter_fn : public intersection_filter_fn {
        public:
            virtual void operator()(base_object & t, const base_object & neg) {};
        };

        class default_permutation_rename_fn : public transformer_fn {
            typedef ptr_vector<transformer_fn> renamer_vector;

            unsigned_vector m_permutation; //this is valid only before m_renamers_initialized becomes true
            bool m_renamers_initialized;
            renamer_vector m_renamers;
        public:
            default_permutation_rename_fn(const base_object & o, const unsigned * permutation) 
                : m_permutation(o.get_signature().size(), permutation),
                m_renamers_initialized(false) {}

            ~default_permutation_rename_fn() {
                dealloc_ptr_vector_content(m_renamers);
            }

            base_object * operator()(const base_object & o) {
                const base_object * res = &o;
                scoped_rel<base_object> res_scoped;
                if(m_renamers_initialized) {
                    typename renamer_vector::iterator rit = m_renamers.begin();
                    typename renamer_vector::iterator rend = m_renamers.end();
                    for(; rit!=rend; ++rit) {
                        res_scoped = (**rit)(*res);
                        res = res_scoped.get();
                    }
                }
                else {
                    SASSERT(m_renamers.empty());
                    unsigned_vector cycle;
                    while(try_remove_cycle_from_permutation(m_permutation, cycle)) {
                        transformer_fn * renamer = o.get_manager().mk_rename_fn(*res, cycle);
                        SASSERT(renamer);
                        m_renamers.push_back(renamer);
                        cycle.reset();

                        res_scoped = (*renamer)(*res);
                        res = res_scoped.get();
                    }
                    m_renamers_initialized = true;
                }
                if(res_scoped) {
                    SASSERT(res==res_scoped.get());
                    //we don't want to delete the last one since we'll be returning it
                    return res_scoped.release();
                }
                else {
                    SASSERT(res==&o);
                    return res->clone();
                }
            }

        };


    };


    // -----------------------------------
    //
    // relation_base
    //
    // -----------------------------------

    class relation_signature;
    class relation_plugin;
    class relation_base;

    typedef ptr_vector<sort> relation_signature_base0;
    typedef ptr_hash<sort> relation_sort_hash;


    struct relation_traits {
        typedef relation_plugin plugin;
        typedef relation_base base_object;
        typedef relation_element element;
        typedef relation_fact fact;
        typedef relation_sort sort;
        typedef relation_signature_base0 signature_base_base;
        typedef relation_signature signature;
    };

    typedef tr_infrastructure<relation_traits> relation_infrastructure;

    typedef relation_infrastructure::base_fn base_relation_fn;
    typedef relation_infrastructure::join_fn relation_join_fn;
    typedef relation_infrastructure::transformer_fn relation_transformer_fn;
    typedef relation_infrastructure::union_fn relation_union_fn;
    typedef relation_infrastructure::mutator_fn relation_mutator_fn;
    typedef relation_infrastructure::intersection_filter_fn relation_intersection_filter_fn;
    typedef relation_infrastructure::intersection_join_filter_fn relation_intersection_join_filter_fn;

    typedef relation_infrastructure::convenient_join_fn convenient_relation_join_fn;
    typedef relation_infrastructure::convenient_join_project_fn convenient_relation_join_project_fn;
    typedef relation_infrastructure::convenient_transformer_fn convenient_relation_transformer_fn;
    typedef relation_infrastructure::convenient_project_fn convenient_relation_project_fn;
    typedef relation_infrastructure::convenient_rename_fn convenient_relation_rename_fn;
    typedef relation_infrastructure::convenient_negation_filter_fn convenient_relation_negation_filter_fn;
    typedef relation_infrastructure::identity_transformer_fn identity_relation_transformer_fn;
    typedef relation_infrastructure::identity_mutator_fn identity_relation_mutator_fn;
    typedef relation_infrastructure::identity_intersection_filter_fn identity_relation_intersection_filter_fn;
    typedef relation_infrastructure::default_permutation_rename_fn default_relation_permutation_rename_fn;

    class relation_signature : public relation_infrastructure::signature_base {
    public:
        bool operator!=(const relation_signature & o) const {
            return !(*this==o);
        }

        void output(ast_manager & m, std::ostream & out) const;

        struct hash {
            unsigned operator()(relation_signature const& s) const { 
                return obj_vector_hash<relation_signature>(s);
            }
        };

        struct eq {
            bool operator()(relation_signature const& s1, relation_signature const& s2) const {
                return s1 == s2;
            }
        };
    };

    class relation_plugin : public relation_infrastructure::plugin_object {
    protected:
        enum special_relation_type {
            ST_ORDINARY,
            ST_TABLE_RELATION,
            ST_FINITE_PRODUCT_RELATION,
            ST_PRODUCT_RELATION,
            ST_SIEVE_RELATION
        };
    private:
        special_relation_type m_special_type;
    protected:
        relation_plugin(symbol const& name, relation_manager & manager, 
                special_relation_type special_type = ST_ORDINARY) 
            : plugin_object(name, manager),
            m_special_type(special_type) {}
    public:
        bool from_table() const { return m_special_type==ST_TABLE_RELATION; }
        bool is_finite_product_relation() const { return m_special_type==ST_FINITE_PRODUCT_RELATION; }
        bool is_product_relation() const { return m_special_type==ST_PRODUCT_RELATION; }
        bool is_sieve_relation() const { return m_special_type==ST_SIEVE_RELATION; }

        /**
           \brief If true, the relation can contain only one or zero elements.

           Having this zero allows the finite_product_relation to perform some operations in a simpler way.
           (KH: I started implementing finite_product_relation::inner_singleton_union_fn that takes advantage of
           it, but it's not finished.)
        */
        virtual bool is_singleton_relation() const { return false; }
    };

    class relation_base : public relation_infrastructure::base_ancestor {
    protected:
        relation_base(relation_plugin & plugin, const relation_signature & s) 
            : base_ancestor(plugin, s) {}
        virtual ~relation_base() {}
    public:
        virtual relation_base * complement(func_decl* p) const = 0;

        virtual void reset();

        virtual void display_tuples(func_decl & pred, std::ostream & out) const {
            out << "Tuples in " << pred.get_name() << ": \n";
            display(out);
        }

        virtual void to_formula(expr_ref& fml) const = 0;

        bool from_table() const { return get_plugin().from_table(); }
        virtual bool is_precise() const { return true; }
    };

    typedef ptr_vector<relation_base> relation_vector;

    // -----------------------------------
    //
    // table_base
    //
    // -----------------------------------
    
    class table_signature;
    class table_plugin;
    class table_base;

    typedef uint64 table_sort;
    typedef svector<table_sort> table_signature_base0;
    typedef uint64_hash table_sort_hash;

    typedef uint64_hash table_element_hash;

    struct table_traits {
        typedef table_plugin plugin;
        typedef table_base base_object;
        typedef table_element element;
        typedef table_fact fact;
        typedef table_sort sort;
        typedef table_signature_base0 signature_base_base;
        typedef table_signature signature;
    };

    typedef tr_infrastructure<table_traits> table_infrastructure;

    typedef table_infrastructure::base_fn base_table_fn;
    typedef table_infrastructure::join_fn table_join_fn;
    typedef table_infrastructure::transformer_fn table_transformer_fn;
    typedef table_infrastructure::union_fn table_union_fn;
    typedef table_infrastructure::mutator_fn table_mutator_fn;
    typedef table_infrastructure::intersection_filter_fn table_intersection_filter_fn;
    typedef table_infrastructure::intersection_join_filter_fn table_intersection_join_filter_fn;

    typedef table_infrastructure::convenient_join_fn convenient_table_join_fn;
    typedef table_infrastructure::convenient_join_project_fn convenient_table_join_project_fn;
    typedef table_infrastructure::convenient_transformer_fn convenient_table_transformer_fn;
    typedef table_infrastructure::convenient_project_fn convenient_table_project_fn;
    typedef table_infrastructure::convenient_rename_fn convenient_table_rename_fn;
    typedef table_infrastructure::convenient_negation_filter_fn convenient_table_negation_filter_fn;
    typedef table_infrastructure::identity_transformer_fn identity_table_transformer_fn;
    typedef table_infrastructure::identity_mutator_fn identity_table_mutator_fn;
    typedef table_infrastructure::identity_intersection_filter_fn identity_table_intersection_filter_fn;
    typedef table_infrastructure::default_permutation_rename_fn default_table_permutation_rename_fn;

    class table_row_mutator_fn {
    public:
        /**
            \brief The function is called for a particular table row. The \c func_columns contains 
            a pointer to an array of functional column values that can be modified. If the function 
            returns true, the modification will appear in the table; otherwise the row will be deleted.

            It is possible that one call to the function stands for multiple table rows that share 
            the same functional column values.
            */
        virtual bool operator()(table_element * func_columns) = 0;
    };

    class table_row_pair_reduce_fn {
    public:
        /**
            \brief The function is called for pair of table rows that became duplicit due to projection.
            The values that are in the first array after return from the function will be used for the 
            resulting row.

            It is assumed that the function is idempotent: when the two functional sub-tuples are equal,
            the result is assumed to be equal to them as well, so the function may not be evaluated for them.
            */
        virtual void operator()(table_element * func_columns, const table_element * merged_func_columns) = 0;
    };


    class table_signature : public table_infrastructure::signature_base {
    public:
        struct hash {
            unsigned operator()(table_signature const& s) const { 
                return svector_hash<table_sort_hash>()(s);
            }
        };

        struct eq {
            bool operator()(table_signature const& s1, table_signature const& s2) const {
                return s1 == s2;
            }
        };
    private:
        unsigned m_functional_columns;
    public:
        table_signature() : m_functional_columns(0) {}
        
        void swap(table_signature & s) {
            signature_base::swap(s);
            std::swap(m_functional_columns, s.m_functional_columns);
        }

        /**
           \brief The returned value is the number of last columns that are functional.

           The uniqueness is enforced on non-functional columns. When projection causes two
           facts to have equal non-functional parts, it is not defined which one of them is retained.
         */
        unsigned functional_columns() const { return m_functional_columns; }
        void set_functional_columns(unsigned val) { SASSERT(size()>=val); m_functional_columns = val; }

        /**
           \brief Return index of the first functional column, or the size of the signature if there 
           are no functional columns.
         */
        unsigned first_functional() const { return size()-m_functional_columns; }

        bool operator==(const table_signature & o) const {
            return signature_base::operator==(o) && m_functional_columns==o.m_functional_columns;
        }
        bool operator!=(const table_signature & o) const {
            return !(*this==o);
        }

        /**
           \brief return true iof the two signatures are equal when we ignore which columns are functional.
        */
        bool equal_up_to_fn_mark(const table_signature & o) const {
            return signature_base::operator==(o);
        }


        /**
            \brief Into \c result assign signature of result of join of relations with signatures \c s1 
            and \c s2. The result is 
            
            (non-functional of s1)(non-functional of s2)(functional of s1)(functional of s2)
        */
        static void from_join(const table_signature & s1, const table_signature & s2, unsigned col_cnt, 
                const unsigned * cols1, const unsigned * cols2, table_signature & result);

        static void from_join_project(const table_signature & s1, const table_signature & s2, 
                unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
                const unsigned * removed_cols, table_signature & result);


        /**
            \brief Into \c result assign signature projected from \c src.

            The array of removed columns must be sorted in ascending order.

            If we remove at least one non-functional column, all the columns in the result are non-functional.
        */
        static void from_project(const table_signature & src, unsigned col_cnt, 
                const unsigned * removed_cols, table_signature & result);

        static void from_project_with_reduce(const table_signature & src, unsigned col_cnt, 
                const unsigned * removed_cols, table_signature & result);

        /**
            \brief Into \c result assign signature \c src with reordered columns.

            Permutations between functional and nonfunctional columns are not allowed.
        */
        static void from_rename(const table_signature & src, unsigned cycle_len, 
                const unsigned * permutation_cycle, table_signature & result) {
            signature_base::from_rename(src, cycle_len, permutation_cycle, result);
            result.set_functional_columns(src.functional_columns());
#if Z3DEBUG
            unsigned first_src_fun = src.size()-src.functional_columns();
            bool in_func = permutation_cycle[0]>=first_src_fun;
            for(unsigned i=1;i<cycle_len;i++) {
                SASSERT(in_func == (permutation_cycle[i]>=first_src_fun));
            }
#endif
        }

        /**
            \brief Into \c result assign signature \c src with reordered columns.
    
            Permutations mixing functional and nonfunctional columns are not allowed.
        */
        static void from_permutation_rename(const table_signature & src, 
                const unsigned * permutation, table_signature & result) {
            signature_base::from_permutation_rename(src, permutation, result);
            result.set_functional_columns(src.functional_columns());
#if Z3DEBUG
            unsigned sz = src.size();
            unsigned first_src_fun = sz-src.functional_columns();
            for(unsigned i=first_src_fun;i<sz;i++) {
                SASSERT(permutation[i]>=first_src_fun);
            }
#endif
        }

    };

    class table_plugin : public table_infrastructure::plugin_object {
        friend class relation_manager;
    protected:
        table_plugin(symbol const& n, relation_manager & manager) : plugin_object(n, manager) {}
    public:

        virtual bool can_handle_signature(const table_signature & s) { return s.functional_columns()==0; }

    protected:
        /**
           If the returned value is non-zero, the returned object must take ownership of \c mapper.
           Otherwise \c mapper must remain unmodified.
        */
        virtual table_mutator_fn * mk_map_fn(const table_base & t, table_row_mutator_fn * mapper) { return 0; }

        /**
           If the returned value is non-zero, the returned object must take ownership of \c reducer.
           Otherwise \c reducer must remain unmodified.
        */
        virtual table_transformer_fn * mk_project_with_reduce_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols, table_row_pair_reduce_fn * reducer) { return 0; }

    };

    class table_base : public table_infrastructure::base_ancestor {
    protected:
        table_base(table_plugin & plugin, const table_signature & s) 
            : base_ancestor(plugin, s) {}
        virtual ~table_base() {}
    public:
        virtual table_base * clone() const;
        virtual table_base * complement(func_decl* p, const table_element * func_columns = 0) const;
        virtual bool empty() const;

        /**
           \brief Return true if table contains fact that corresponds to \c f in all non-functional
           columns.
         */
        virtual bool contains_fact(const table_fact & f) const;

        /**
           \brief If \c f (i.e. its non-functional part) is not present in the table, 
           add it and return true. Otherwise update \c f, so that the values of functional 
           columns correspond to the ones present in the table.
         */
        virtual bool suggest_fact(table_fact & f);

        /**
           \brief If \c f (i.e. its non-functional part) is not present in the table, 
           return false. Otherwise update \c f, so that the values of functional 
           columns correspond to the ones present in the table and return true.
         */
        virtual bool fetch_fact(table_fact & f) const;

        /**
           \brief Ensure fact \c f is present in the table (including the values of its functional columns).
        */
        virtual void ensure_fact(const table_fact & f);

        virtual void remove_fact(const table_fact & fact) { 
            SASSERT(fact.size() == get_signature().size());
            remove_fact(fact.c_ptr()); }

        virtual void remove_fact(table_element const* fact) = 0;
        virtual void remove_facts(unsigned fact_cnt, const table_fact * facts);
        virtual void remove_facts(unsigned fact_cnt, const table_element * facts);
        virtual void reset();

        class row_interface;

        virtual void display(std::ostream & out) const;

        /**
           \brief Convert table to a formula that encodes the table.
           The columns correspond to bound variables indexed as
           0, .., sig.size()-1
         */
        virtual void to_formula(relation_signature const& sig, expr_ref& fml) const;

    protected:


        class iterator_core {
            unsigned m_ref_cnt;
        public:
            iterator_core() : m_ref_cnt(0) {}
            virtual ~iterator_core() {}

            void inc_ref() { m_ref_cnt++; }
            void dec_ref() { 
                SASSERT(m_ref_cnt>0);
                m_ref_cnt--;
                if(m_ref_cnt==0) {
                    dealloc(this);
                }
            }

            virtual bool is_finished() const = 0;

            virtual row_interface & operator*() = 0;
            virtual void operator++() = 0;
            virtual bool operator==(const iterator_core & it) {
                //we worry about the equality operator only because of checking 
                //the equality with the end() iterator
                if(is_finished() && it.is_finished()) {
                    return true;
                }
                return false;
            }
        private:
            //private and undefined copy constructor and assignment operator
            iterator_core(const iterator_core &);
            iterator_core & operator=(const iterator_core &);
        };

        struct row_iterator_core {
            unsigned m_ref_cnt;
        public:
            row_iterator_core() : m_ref_cnt(0) {}
            virtual ~row_iterator_core() {}

            void inc_ref() { m_ref_cnt++; }
            void dec_ref() { 
                SASSERT(m_ref_cnt>0);
                m_ref_cnt--;
                if(m_ref_cnt==0) {
                    dealloc(this);
                }
            }

            virtual bool is_finished() const = 0;

            virtual table_element operator*() = 0;
            virtual void operator++() = 0;
            virtual bool operator==(const row_iterator_core & it) {
                //we worry about the equality operator only because of checking 
                //the equality with the end() iterator
                if(is_finished() && it.is_finished()) {
                    return true;
                }
                return false;
            }
        private:
            //private and undefined copy constructor and assignment operator
            row_iterator_core(const row_iterator_core &);
            row_iterator_core & operator=(const row_iterator_core &);
        };

    public:
        class iterator {
            friend class table_base;

            ref<iterator_core> m_core;

            iterator(iterator_core * core) : m_core(core) {}
        public:
            /**
               \brief Return reference to a row_interface object for the current row.

               The reference is valid only until the \c operator++() is called or
               until the iterator is invalidated.
            */
            row_interface & operator*()
            { return *(*m_core); }
            row_interface * operator->()
            { return &(*(*m_core)); }
            iterator & operator++()
            { ++(*m_core); return *this; }
            bool operator==(const iterator & it)
            { return (*m_core)==(*it.m_core); }
            bool operator!=(const iterator & it)
            { return !operator==(it); }
        };

        class row_iterator {
            friend class table_base;
            friend class row_interface;

            ref<row_iterator_core> m_core;

            row_iterator(row_iterator_core * core) : m_core(core) {}
        public:
            table_element operator*()
            { return *(*m_core); }
            row_iterator & operator++()
            { ++(*m_core); return *this; }
            bool operator==(const row_iterator & it)
            { return (*m_core)==(*it.m_core); }
            bool operator!=(const row_iterator & it)
            { return !operator==(it); }
        };

        virtual iterator begin() const = 0;
        virtual iterator end() const = 0;

        class row_interface {
            class fact_row_iterator;

            const table_base & m_parent_table;
        public:
            typedef row_iterator iterator;
            typedef row_iterator const_iterator;

            row_interface(const table_base & parent_table) : m_parent_table(parent_table) {}
            virtual ~row_interface() {}

            virtual table_element operator[](unsigned col) const = 0;

            unsigned size() const { return m_parent_table.get_signature().size(); }
            virtual void get_fact(table_fact & result) const;
            virtual row_iterator begin() const;
            virtual row_iterator end() const;
            virtual void display(std::ostream & out) const;
        };

    protected:

        class caching_row_interface : public row_interface {
            mutable table_fact m_current;

            bool populated() const { return !m_current.empty(); }
            void ensure_populated() const { 
                if(!populated()) { 
                    get_fact(m_current);
                }
            }
        public:
            caching_row_interface(const table_base & parent) : row_interface(parent) {}

            virtual void get_fact(table_fact & result) const = 0;

            virtual table_element operator[](unsigned col) const { 
                ensure_populated();
                return m_current[col];
            }
            /**
               \brief Resets the cache of the row object.

               Must be called when the row object begins to represent a different row in the table.
            */
            void reset() { m_current.reset(); }
        };

        //This function is here to create iterator instances in classes that derive from table_base.
        //We do not want to make the constructor of the iterator class public, and being private, the 
        //inheritor classes cannot see it directly.
        static iterator mk_iterator(iterator_core * core) {
            return iterator(core);
        }
    };

    /**
       \brief Populate vector \c renaming_args so that it can be used as an argument to \c var_subst.
         The renaming we want is one that transforms variables with numbers of indexes of \c map into the
         values of at those indexes. If a value if \c UINT_MAX, it means we do not transform the index 
         corresponding to it.
    */
    void get_renaming_args(const unsigned_vector & map, const relation_signature & orig_sig, 
            expr_ref_vector & renaming_arg);


};

#endif /* DL_BASE_H_ */

