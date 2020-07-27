/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_vector_relation.h

Abstract:

    Basic relation with equivalences.

Author:

    Nikolaj Bjorner (nbjorner) 2010-2-11

Revision History:

--*/
#pragma once

#include "ast/ast_pp.h"
#include "muz/base/dl_context.h"
#include "util/union_find.h"

namespace datalog {
   
    typedef std::pair<unsigned, unsigned> u_pair;

    template<typename T>
    class vector_relation_helper {
    public:
        static void mk_project_t(T& t, unsigned_vector const& renaming) {}
    };

    template<typename T, typename Helper = vector_relation_helper<T> > 
    class vector_relation : public relation_base {       
    protected:
        T                  m_default;
        vector<T>*         m_elems;
        bool               m_empty;
        union_find_default_ctx m_ctx;
        union_find<>*      m_eqs;

    public:
        vector_relation(relation_plugin& p, relation_signature const& s, bool is_empty, T const& t = T()):
            relation_base(p, s),
            m_default(t),
            m_elems(alloc(vector<T>)),
            m_empty(is_empty), 
            m_eqs(alloc(union_find<>, m_ctx)) {
            m_elems->resize(s.size(), t);
            for (unsigned i = 0; i < s.size(); ++i) {
                m_eqs->mk_var();
            }
        }

        ~vector_relation() override {
            dealloc(m_eqs);
            dealloc(m_elems);
        }

        void swap(relation_base& other) override {
            vector_relation& o = dynamic_cast<vector_relation&>(other);
            if (&o == this) return;
            std::swap(o.m_eqs, m_eqs);
            std::swap(o.m_empty, m_empty);
            std::swap(o.m_elems, m_elems);
        }

        void copy(vector_relation const& other) {
            SASSERT(get_signature() == other.get_signature());
            if (other.empty()) {
                set_empty();
                return;
            }
            m_empty = false;
            for (unsigned i = 0; i < m_elems->size(); ++i) {
                (*this)[i] = other[i];            
                SASSERT(find(i) == i);
            }
            for (unsigned i = 0; i < m_elems->size(); ++i) {
                merge(i, find(i));
            }        
        }


        bool empty() const override { return m_empty; }

        T& operator[](unsigned i) { return (*m_elems)[find(i)]; }

        T const& operator[](unsigned i) const { return (*m_elems)[find(i)]; }

        virtual void display_index(unsigned i, T const& t, std::ostream& out) const = 0;

        void display(std::ostream & out) const override {
            if (empty()) {
                out << "empty\n";
                return;
            }
            for (unsigned i = 0; i < m_elems->size(); ++i) {
                if (i == find(i)) {
                    display_index(i, (*m_elems)[i], out);
                }
                else {
                    out << i << " = " << find(i) << " ";
                }
            }
            out << "\n";
        }


        bool is_subset_of(vector_relation const& other) const {
            if (empty()) return true;
            if (other.empty()) return false;
            for (unsigned i = 0; i < get_signature().size(); ++i) {
                if (!is_subset_of((*this)[i], other[i])) {
                    return false;
                }
            }
            return true;
        }

        void set_empty() { 
            unsigned sz = m_elems->size();
            m_empty = true; 
            m_elems->reset();
            m_elems->resize(sz, m_default);
            dealloc(m_eqs);
            m_eqs = alloc(union_find<>,m_ctx);
            for (unsigned i = 0; i < sz; ++i) {
                m_eqs->mk_var();
            }
        }


        virtual T mk_intersect(T const& t1, T const& t2, bool& is_empty) const = 0;

        virtual T mk_widen(T const& t1, T const& t2) const = 0;

        virtual T mk_unite(T const& t1, T const& t2) const = 0;

        virtual bool is_subset_of(T const& t1, T const& t2) const = 0;

        virtual bool is_full(T const& t) const = 0;

        virtual bool is_empty(unsigned i, T const& t) const = 0;

        virtual void mk_rename_elem(T& t, unsigned col_cnt, unsigned const* cycle) = 0;

        virtual T mk_eq(union_find<> const& old_eqs, union_find<> const& neq_eqs, T const& t) const { return t; }

        void equate(unsigned i, unsigned j) {
            SASSERT(i < get_signature().size());
            SASSERT(j < get_signature().size());
            if (!empty() && find(i) != find(j)) {
                bool isempty;
                T r = mk_intersect((*this)[i], (*this)[j], isempty);
                if (isempty || is_empty(find(i),r)) {
                    m_empty = true;
                }
                else {
                    merge(i, j);
                    (*this)[i] = r;
                }
            }
        }

        bool is_full() const { 
            for (unsigned i = 0; i < m_elems->size(); ++i) {
                if (!is_full((*this)[i])) {
                    return false;
                }
            }
            return true;
        }

        void mk_join(vector_relation const& r1, vector_relation const& r2,
                     unsigned num_cols, unsigned const* cols1, unsigned const* cols2) {
            SASSERT(is_full());
            bool is_empty = r1.empty() || r2.empty();          
            if (is_empty) {
                m_empty = true;               
                return;
            }
            unsigned sz1 = r1.get_signature().size();
            unsigned sz2 = r2.get_signature().size();  
            for (unsigned i = 0; i < sz1; ++i) {
                (*this)[i] = r1[i];
            }
            for (unsigned i = 0; i < sz2; ++i) {
                (*this)[sz1+i] = r2[i];
            }
            for (unsigned i = 0; i < num_cols; ++i) {
                unsigned col1 = cols1[i];
                unsigned col2 = cols2[i];                
                equate(col1, sz1 + col2);
            }

            TRACE("dl_relation",                   
                  r1.display(tout << "r1:\n");
                  r2.display(tout << "r2:\n");
                  display(tout << "dst:\n");
                  );
        }

        void mk_project(vector_relation const& r, unsigned col_cnt, unsigned const* removed_cols) {
            SASSERT(is_full());
            unsigned_vector classRep, repNode;
            unsigned result_size = get_signature().size();
            unsigned input_size = r.get_signature().size();
            repNode.resize(input_size, UINT_MAX);

            // initialize vector entries and set class representatives.
            for (unsigned i = 0, j = 0, c = 0; i < input_size; ++i) {
                if (c < col_cnt && removed_cols[c] == i) {
                    ++c;
                }
                else {
                    (*this)[j] = r[i];
                    classRep.push_back(r.find(i));
                    ++j;
                }
            }

            // merge remaining equivalence classes.
            for (unsigned i = 0; i < result_size; ++i) {
                unsigned rep = classRep[i];
                if (repNode[rep] == UINT_MAX) {
                    repNode[rep] = i;
                }
                else {
                    merge(repNode[rep], i);
                }
            }

            // rename columns in image of vector relation.
            unsigned_vector renaming;
            for (unsigned i = 0, j = 0, c = 0; i < input_size; ++i) {
                if (c < col_cnt && removed_cols[c] == i) {
                    renaming.push_back(UINT_MAX);
                    ++c;
                }
                else {
                    renaming.push_back(find(j));
                    ++j;
                }
            }
            for (unsigned k = 0; k < result_size; ++k) {
                Helper::mk_project_t((*this)[k], renaming);
            }


            TRACE("dl_relation",
                  ast_manager& m = r.get_plugin().get_ast_manager();
                  tout << "Signature: ";
                  for (unsigned i = 0; i < r.get_signature().size(); ++i) {
                      tout << mk_pp(r.get_signature()[i], m) << " ";
                  }
                  tout << "Remove: ";
                  for (unsigned i = 0; i < col_cnt; ++i) {
                      tout << removed_cols[i] << " ";
                  }
                  tout << "\n";
                  r.display(tout);
                  tout << " --> \n";
                  display(tout););
        }

        void mk_rename(vector_relation const& r, unsigned col_cnt, unsigned const* cycle) {
            unsigned col1, col2;
            SASSERT(is_full());
           
            // roundabout way of creating permuted relation.
            unsigned_vector classRep, repNode;
            for (unsigned i = 0; i < r.m_elems->size(); ++i) {
                classRep.push_back(r.find(i));
                repNode.push_back(UINT_MAX);
                (*this)[i] = r[i];
            }            
            for (unsigned i = 0; i + 1 < col_cnt; ++i) {
                col1 = cycle[i];
                col2 = cycle[i+1];
                (*this)[col2] = (*r.m_elems)[col1];
                classRep[col2] = r.find(col1);
            }
            col1 = cycle[col_cnt-1];
            col2 = cycle[0];
            (*this)[col2] = (*r.m_elems)[col1];
            classRep[col2] = r.find(col1);

            for (unsigned i = 0; i < r.m_elems->size(); ++i) {
                unsigned rep = classRep[i];
                if (repNode[rep] == UINT_MAX) {
                    repNode[rep] = i;
                }
                else {
                    merge(repNode[rep], i);
                }
            }

            for (unsigned i = 0; i < r.m_elems->size(); ++i) {
                mk_rename_elem((*m_elems)[i], col_cnt, cycle);
            }            

            TRACE("dl_relation", 
                  ast_manager& m = r.get_plugin().get_ast_manager();
                  tout << "cycle: ";
                  for (unsigned i = 0; i < col_cnt; ++i) {
                      tout << cycle[i] << " ";
                  }
                  tout << "\nold_sig: ";
                  for (unsigned i = 0; i < r.get_signature().size(); ++i) {
                      tout << mk_pp(r.get_signature()[i], m) << " ";
                  }            
                  tout << "\nnew_sig: ";
                  for (unsigned i = 0; i < get_signature().size(); ++i) {
                        tout << mk_pp(get_signature()[i], m) << " ";
                  }                    
                  tout << "\n";
                  r.display(tout << "src:\n");
                  );         
        }

        void mk_union(vector_relation const& src, vector_relation* delta, bool is_widen) {
            TRACE("dl_relation", display(tout << "dst:\n"); src.display(tout  << "src:\n"););

            if (src.empty()) {
                if (delta) {
                    delta->copy(src);
                }
                return;
            }

            if (empty()) {
                copy(src);
                if (delta) {
                    delta->copy(src);
                }
                return;
            }

            // find coarsest equivalence class containing joint equalities
            union_find<>* uf = alloc(union_find<>, m_ctx);
            unsigned size = get_signature().size();
            map<u_pair, unsigned, pair_hash<unsigned_hash, unsigned_hash>, default_eq<u_pair> > mp;
            bool change = false;
            bit_vector finds;
            finds.resize(size, false);
            for (unsigned i = 0; i < size; ++i) {
                uf->mk_var();
                unsigned w;
                u_pair p(std::make_pair(find(i), src.find(i)));
                if (mp.find(p, w)) {
                    uf->merge(i, w);
                }
                else {
                    mp.insert(p, i);  
                    // detect change
                    if (finds.get(find(i))) {
                        change = true;
                    }
                    else {
                        finds.set(find(i), true);
                    }
                }
            }
            vector<T>* elems = alloc(vector<T>);
            for (unsigned i = 0; i < size; ++i) {                
                T t1 = mk_eq(*m_eqs, *uf, (*this)[i]);
                T t2 = mk_eq(*src.m_eqs, *uf, src[i]);
                if (is_widen) {
                    elems->push_back(mk_widen(t1, t2));
                }
                else {
                    elems->push_back(mk_unite(t1, t2));
                }
                TRACE("dl_relation", tout << t1 << " u " << t2 << " = " << elems->back() << "\n";);
                change = delta && (change || !((*elems)[i] == (*this)[i]));
            }
            dealloc(m_eqs);
            dealloc(m_elems);
            m_eqs = uf;
            m_elems = elems;
            if (delta && change) {
                delta->copy(*this);
            }
            TRACE("dl_relation", display(tout << "dst':\n"););
        }

        unsigned find(unsigned i) const { 
            return m_eqs->find(i);
        }

        void merge(unsigned i, unsigned j) { 
            m_eqs->merge(i, j);
        }

    };
        
};


