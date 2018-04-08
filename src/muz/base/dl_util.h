/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_util.h

Abstract:

    Datalog utility function and structures.

Author:

    Krystof Hoder 2010

Revision History:

--*/
#ifndef DL_UTIL_H_
#define DL_UTIL_H_

#include<vector>
#include "ast/ast.h"
#include "util/hashtable.h"
#include "util/obj_hashtable.h"
#include "util/uint_set.h"
#include "tactic/horn_subsume_model_converter.h"
#include "tactic/replace_proof_converter.h"
#include "ast/substitution/substitution.h"
#include "ast/rewriter/ast_counter.h"
#include "util/statistics.h"
#include "util/stopwatch.h"
#include "util/lbool.h"
#include "util/container_util.h"

namespace datalog {

    class context;
    class rule;
    class relation_base;
    class relation_manager;
    class table_base;
    class pentagon_relation;
    class relation_fact;
    class relation_signature;
    class rule_manager;

    class verbose_action {
        unsigned  m_lvl;
        class stopwatch* m_sw;
    public:
        verbose_action(char const* msg, unsigned lvl = 11);
        ~verbose_action();
    };

    typedef ref_vector<rule, rule_manager> rule_ref_vector;
    enum PDR_CACHE_MODE {
        NO_CACHE,
        HASH_CACHE,
        CONSTRAINT_CACHE,
        LAST_CACHE_MODE
    };

    struct std_string_hash_proc { 
        unsigned operator()(const std::string & s) const 
        { return string_hash(s.c_str(), static_cast<unsigned>(s.length()), 17); } 
    };

    // typedef int_hashtable<int_hash, default_eq<int> > idx_set;
    typedef uint_set idx_set;
    typedef idx_set var_idx_set;
    typedef u_map<var *> varidx2var_map;
    typedef obj_hashtable<func_decl> func_decl_set; //!< Rule dependencies.
    typedef std::vector<std::string> string_vector;
    
    bool contains_var(expr * trm, unsigned var_idx);

    /**
       \brief Return number of arguments of \c pred that are variables
    */
    unsigned count_variable_arguments(app * pred);


    template<typename T>
    void copy_nonvariables(app * src, T& tgt)
    {
        unsigned n = src->get_num_args();
        for (unsigned i = 0; i < n; i++) {
            expr * arg = src->get_arg(i);
            if (!is_var(arg)) {
                tgt[i]=arg;
            }
        }
    }

    /**
       \brief Auxiliary function used to create a tail based on \c pred for a new rule.
       The variables in \c pred are re-assigned using \c next_idx and \c varidx2var.
       A variable is considered non-local to the rule if it is in the set \c non_local_vars.
       Non-local variables are coppied to new_rule_args, and their sorts to \c new_rule_domain.
       The new predicate is stored in \c new_pred.
    */
    void mk_new_rule_tail(ast_manager & m, app * pred, 
                          var_idx_set const & non_local_vars, 
                          unsigned & next_idx, varidx2var_map & varidx2var, 
                          sort_ref_buffer & new_rule_domain, expr_ref_buffer & new_rule_args, 
                          app_ref & new_pred);

    /**
       \brief Simpler version of the previous function. Initializes next_idx with 0, and 
       an empty varid2var
    */
    inline void mk_new_rule_tail(ast_manager & m, app * pred, 
                                 var_idx_set const & non_local_vars, 
                                 sort_ref_buffer & new_rule_domain, expr_ref_buffer & new_rule_args, 
                                 app_ref & new_pred) {
        unsigned next_idx = 0;
        varidx2var_map varidx2var;
        mk_new_rule_tail(m, pred, non_local_vars, next_idx, varidx2var, new_rule_domain, new_rule_args, new_pred);
    }
     
    /**
       \brief Print a predicate \c f to the stream \c out.
    */
    void display_predicate(context & ctx, app * f, std::ostream & out);

    /**
       \brief Like \c display_predicate, just without the final '\n' character.
    */
    void output_predicate(context & ctx, app * f, std::ostream & out);

    /**
       \brief Print a fact \c f to the stream \c out in a format conforming to Bddbddb.
    */
    void display_fact(context & ctx, app * f, std::ostream & out);

    

    class variable_intersection
    {
        bool values_match(const expr * v1, const expr * v2);

        unsigned_vector m_args1;
        unsigned_vector m_args2;

        unsigned_vector m_const_indexes;
        app_ref_vector   m_consts;

        static unsigned expr_cont_get_size(app * a) { return a->get_num_args(); }
        static expr * expr_cont_get(app * a, unsigned i) { return a->get_arg(i); }
        static unsigned expr_cont_get_size(const ptr_vector<expr> & v) { return v.size(); }
        static unsigned expr_cont_get_size(const expr_ref_vector & v) { return v.size(); }
        static expr * expr_cont_get(const ptr_vector<expr> & v, unsigned i) { return v[i]; }
        static expr * expr_cont_get(const expr_ref_vector & v, unsigned i) { return v[i]; }
    public:
        variable_intersection(ast_manager & m) : m_consts(m) {}

        unsigned size() const {
            return m_args1.size();
        }

        const unsigned * get_cols1() const {
            return m_args1.c_ptr();
        }

        const unsigned * get_cols2() const {
            return m_args2.c_ptr();
        }

        bool empty() const {
            return size()==0;
        }

        void get(unsigned i, unsigned & index1, unsigned & index2) const {
            index1=m_args1[i];
            index2=m_args2[i];
        }

        void reset() {
            m_args1.reset();
            m_args2.reset();
            m_const_indexes.reset();
            m_consts.reset();
        }

        bool args_match(const app * f1, const app * f2); 
        bool args_self_match(const app * f);

        /**
           \brief Fill arguments of \c f1 into corresponding positions in
             \c tgt using its \c operator[].
        */
        template<typename T>
        void fill_into_second(const app * f1, T & tgt) const {
            unsigned n=size();
            for(unsigned i=0; i<n; i++) {
                unsigned f1_index, tgt_index;
                get(i, f1_index, tgt_index);
                tgt[tgt_index]=f1->get_arg(f1_index);
            }
        }

        void add_pair(unsigned idx1, unsigned idx2) {
            m_args1.push_back(idx1);
            m_args2.push_back(idx2);
        }

        /**
           Find pairs of indexes of arguments of \c a1 and \c a2 that correspond to the same 
           variable. Here we do not detect the constant arguments in \c a1 and \c a2.
        */
        template<typename T1, typename T2>
        void populate(const T1 & a1, const T2 & a2)
        {
            //TODO: optimize quadratic complexity
            //TODO: optimize number of checks when variable occurs multiple times
            unsigned a1num = expr_cont_get_size(a1);
            unsigned a2num = expr_cont_get_size(a2);
            for(unsigned i1=0; i1<a1num; i1++) {
                expr * e1=expr_cont_get(a1,i1);
                if(!is_var(e1)) {
                    continue;
                }
                var* v1=to_var(e1);
                for(unsigned i2=0; i2<a2num; i2++) {
                    expr * e2=expr_cont_get(a2,i2);
                    if(!is_var(e2)) {
                        continue;
                    }
                    var* v2=to_var(e2);
                    if(v1->get_idx()==v2->get_idx()) {
                        add_pair(i1, i2);
                    }
                }
            }
        }

        /**
           Find pairs of indexes of arguments of \c a that correspond to the same variable
           and indexes that correspond to a constant.
        */
        void populate_self(const app * a);
    };

    template<class T>
    void project_out_vector_columns(T & container, unsigned removed_col_cnt, const unsigned * removed_cols) {
        if(removed_col_cnt==0) {
            return;
        }
        unsigned n = container.size();
        unsigned ofs = 1;
        unsigned r_i = 1;
        for(unsigned i=removed_cols[0]+1; i<n; i++) {
            if(r_i!=removed_col_cnt && removed_cols[r_i]==i) {
                r_i++;
                ofs++;
                continue;
            }
            container[i-ofs] = container[i];
        }
        if (r_i != removed_col_cnt) {
            for (unsigned i = 0; i < removed_col_cnt; ++i) {
                std::cout << removed_cols[i] << " ";
            }
            std::cout << " container size: " << n << "\n";
        }
        SASSERT(r_i==removed_col_cnt);
        container.resize(n-removed_col_cnt);
    }

    template<class T, class M>
    void project_out_vector_columns(ref_vector<T,M> & container, unsigned removed_col_cnt, 
            const unsigned * removed_cols) {
        if(removed_col_cnt==0) {
            return;
        }
        unsigned n = container.size();
        unsigned ofs = 1;
        int r_i = 1;
        for(unsigned i=removed_cols[0]+1; i<n; i++) {
            if(r_i!=removed_col_cnt && removed_cols[r_i]==i) {
                r_i++;
                ofs++;
                continue;
            }
            container.set(i-ofs, container.get(i));
        }
        SASSERT(r_i==removed_col_cnt);
        container.resize(n-removed_col_cnt);
    }

    template<class T>
    void project_out_vector_columns(T & container, const unsigned_vector & removed_cols) {
        project_out_vector_columns(container, removed_cols.size(), removed_cols.c_ptr());
    }



    /**
        \brief Take a single cycle permutation and store it in the form of a cycle.

        The function modifies the \c permutation vector
    */
    void cycle_from_permutation(unsigned_vector & permutation, unsigned_vector & cycle);


    /**
       \brief If \c permutation is an identity, return false. Otherwise remove one cycle from the
       permutation, store it in the form of a cycle in \c cycle and return true.

       Using this function one can retrieve all cycles in a permutation.

       \c cycle must be empty before calling the function.
    */
    bool try_remove_cycle_from_permutation(unsigned_vector & permutation, unsigned_vector & cycle);

    void collect_sub_permutation(const unsigned_vector & permutation, const unsigned_vector & translation,
        unsigned_vector & res, bool & identity);

    template<class T>
    void permutate_by_cycle(T & container, unsigned cycle_len, const unsigned * permutation_cycle) {
        if(cycle_len<2) {
            return;
        }
        typename T::data aux = container[permutation_cycle[0]];
        for(unsigned i=1; i<cycle_len; i++) {
            container[permutation_cycle[i-1]]=container[permutation_cycle[i]];
        }
        container[permutation_cycle[cycle_len-1]]=aux;
    }

    template<class T, class M>
    void permutate_by_cycle(ref_vector<T,M> & container, unsigned cycle_len, const unsigned * permutation_cycle) {
        if(cycle_len<2) {
            return;
        }
        T * aux = container.get(permutation_cycle[0]);
        for(unsigned i=1; i<cycle_len; i++) {
            container.set(permutation_cycle[i-1], container.get(permutation_cycle[i]));
        }
        container.set(permutation_cycle[cycle_len-1], aux);
    }

    template<class T>
    void permutate_by_cycle(T & container, const unsigned_vector & permutation_cycle) {
        permutate_by_cycle(container, permutation_cycle.size(), permutation_cycle.c_ptr());
    }


    class rule_counter : public var_counter {        
    public:
        rule_counter(){}
        void count_rule_vars(const rule * r, int coef = 1);
        unsigned get_max_rule_var(const rule& r);
    };

    void del_rule(horn_subsume_model_converter* mc, rule& r, bool unreachable);

    void resolve_rule(rule_manager& rm,
                      replace_proof_converter* pc, rule const& r1, rule const& r2, unsigned idx, 
                      expr_ref_vector const& s1, expr_ref_vector const& s2, rule const& res);

    void resolve_rule(rule_manager& rm, 
                      rule const& r1, rule const& r2, unsigned idx, 
                      expr_ref_vector const& s1, expr_ref_vector const& s2, rule& res);

    model_converter* mk_skip_model_converter();

    proof_converter* mk_skip_proof_converter();


    void reverse_renaming(ast_manager & m, const expr_ref_vector & src, expr_ref_vector & tgt);


    void print_renaming(const expr_ref_vector & cont, std::ostream & out);

    /**
       \brief Update tgt with effect of applying substitution from 'sub' to it.
       tgt is extended by variables that are substituted by 'sub'.
       We use the convention that the entry at index 'i' corresponds to variable
       with de-Bruijn index 'i'.
    */
    void apply_subst(expr_ref_vector& tgt, expr_ref_vector const& sub);


    template<class T, class U>
    bool vectors_equal(const T & c1, const U & c2) {
        if(c1.size()!=c2.size()) {
            return false;
        }
        typename T::data * it1 = c1.c_ptr();
        typename T::data * end1 = c1.c_ptr()+c1.size();
        typename U::data * it2 = c2.c_ptr();
        for(; it1!=end1; ++it1, ++it2) {
            if(*it1!=*it2) { 
                return false;
            }
        }
        return true;
    }

    void idx_set_union(idx_set & tgt, const idx_set & src);

    template<class T>
    struct default_obj_chash {
        unsigned operator()(T const& cont, unsigned i) const {
            return cont[i]->hash();
        }
    };
    template<class T>
    unsigned obj_vector_hash(const T & cont) {
        return get_composite_hash(cont, cont.size(),default_kind_hash_proc<T>(), default_obj_chash<T>());
    }

    template<class T>
    struct obj_vector_hash_proc { 
        unsigned operator()(const T & cont) const {
            return obj_vector_hash(cont);
        } 
    };

    template<class T>
    struct svector_hash_proc { 
        unsigned operator()(const svector<typename T::data> & cont) const {
            return svector_hash<T>()(cont);
        } 
    };


    template<class T>
    struct vector_eq_proc { 
        bool operator()(const T & c1, const T & c2) const { return vectors_equal(c1, c2); }
    };

    template<class T>
    void dealloc_ptr_vector_content(ptr_vector<T> & v) {
        typename ptr_vector<T>::iterator it = v.begin();
        typename ptr_vector<T>::iterator end = v.end();
        for(; it!=end; ++it) {
            dealloc(*it);
        }
    }

    /**
       \brief Add elements from an iterable object \c src into the vector \c vector.
     */
    template<class VectType, class U>
    void push_into_vector(VectType & vector, const U & src) {
        typename U::iterator it = src.begin();
        typename U::iterator end = src.end();
        for(; it!=end; ++it) {
            vector.push_back(*it);
        }
    }

    template<class VectType, class U, class M>
    void push_into_vector(VectType & vector, const ref_vector<U,M> & src) {
        U * const * it = src.begin();
        U * const * end = src.end();
        for(; it!=end; ++it) {
            vector.push_back(*it);
        }
    }

    template<class SetType, class U>
    void insert_into_set(SetType & tgt, const U & src) {
        typename U::const_iterator it = src.begin();
        typename U::const_iterator end = src.end();
        for(; it!=end; ++it) {
            tgt.insert(*it);
        }
    }


    /**
       \brief Remove the first occurrence of \c el from \c v and return \c true. If
       \c el is not present in \c v, return \c false. The order of elements in \c v
       is not preserved.
     */
    template<class T>
    bool remove_from_vector(T & v, const typename T::data & el) {
        unsigned sz = v.size();
        for(unsigned i=0; i<sz; i++) {
            if(v[i]==el) {
                std::swap(v[i], v.back());
                v.pop_back();
                return true;
            }
        }
        return false;
    }


    /**
   \brief Reset and deallocate the values stored in a mapping of the form obj_map<Key, Value*>
    */
    template<typename Key, typename Value, typename Hash, typename Eq>
    void reset_dealloc_values(map<Key, Value*, Hash, Eq> & m) {
        typename map<Key, Value*, Hash, Eq>::iterator it  = m.begin();
        typename map<Key, Value*, Hash, Eq>::iterator end = m.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m.reset();
    }

    template<class T>
    struct aux__index_comparator {
        T* m_keys;
        aux__index_comparator(T* keys) : m_keys(keys) {}
        bool operator()(unsigned a, unsigned b) {
            return m_keys[a]<m_keys[b];
        }
    };

    template<class T, class U>
    void sort_two_arrays(unsigned len, T* keys, U* vals) {
        if(len<2) {
            return;
        }
        if(len==2) {
            if(keys[0]>keys[1]) {
                std::swap(keys[0], keys[1]);
                std::swap(vals[0], vals[1]);
            }
            return;
        }
        unsigned_vector numbers;
        for(unsigned i=0; i<len; i++) {
            numbers.push_back(i);
        }
        aux__index_comparator<T> cmp(keys);
        std::sort(numbers.begin(), numbers.end(), cmp);
        for(unsigned i=0; i<len; i++) {
            unsigned prev_i = i;
            for(;;) {
                unsigned src_i = numbers[prev_i];
                numbers[prev_i]=prev_i;
                if(src_i==i) {
                    break;
                }
                std::swap(keys[prev_i], keys[src_i]);
                std::swap(vals[prev_i], vals[src_i]);
                prev_i = src_i;
            }
        }
    }


    /**
       \brief Consider \c translation as a map from indexes to values. Iterate through \c src and store 
       transformed values of elements into \c res unless they are equal to \c UINT_MAX.
    */
    void collect_and_transform(const unsigned_vector & src, const unsigned_vector & translation, 
        unsigned_vector & res);

    /**
       \brief Insert into \c res values of \c src transformed by \c map (understood as a function
       from its indexes to the values stored in it).
    */
    void transform_set(const unsigned_vector & map, const idx_set & src, idx_set & result);

    void add_sequence(unsigned start, unsigned count, unsigned_vector & v);

    template<class Container>
    void add_sequence_without_set(unsigned start, unsigned count, const Container & complement, unsigned_vector & v) {
        unsigned after_last = start+count;
        for(unsigned i=start; i<after_last; i++) {
            if(!complement.contains(i)) {
                v.push_back(i);
            }
        }
    }

    // -----------------------------------
    //
    // filesystem functions
    //
    // -----------------------------------

    void get_file_names(std::string directory, const std::string & extension, bool traverse_subdirs, 
        string_vector & res);

    bool file_exists(const std::string & name);
    bool is_directory(const std::string & name);

    std::string get_file_name_without_extension(const std::string & name);

    // -----------------------------------
    //
    // misc
    //
    // -----------------------------------

    template<class T>
    void universal_delete(T* ptr) {
        dealloc(ptr);
    }


    /**
       \brief If it is possible to convert the beginning of \c s to uint64,
       store the result of conversion and return true; otherwise return false.
     */
    bool string_to_uint64(const char * s, uint64_t & res);
    std::string to_string(uint64_t num);
    /**
       \brief Read the sequence of decimal digits starting at \c s and interpret it as
       uint64. If successful, \c res will contain the read number and \c s will point 
       to the first non-digit character, and true is returned. If the first character 
       is not a digit, no parameter is modified and false is returned. If the uint64
       overflows, \c points to the character which caused the overflow and false is 
       returned.
     */
    bool read_uint64(const char * & s, uint64_t & res);
};

#endif /* DL_UTIL_H_ */

