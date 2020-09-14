/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_constraint.h

Abstract:
 
    Interface for Boolean constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

Revision History:

--*/

#pragma once 
#include "sat/smt/ba_solver_interface.h"

namespace ba {

    enum class tag_t {
        card_t,
        pb_t,
        xr_t
    };

    class card;
    class pb;
    class xr;
    class pb_base;

    inline lbool value(sat::model const& m, literal l) { return l.sign() ? ~m[l.var()] : m[l.var()]; }
    
    class constraint {
    protected:
        tag_t          m_tag;
        bool           m_removed;
        literal        m_lit;
        literal        m_watch;
        unsigned       m_glue;
        unsigned       m_psm;
        unsigned       m_size;
        size_t         m_obj_size;
        bool           m_learned;
        unsigned       m_id;
        bool           m_pure;        // is the constraint pure (only positive occurrences)

        void display_lit(std::ostream& out, solver_interface const& s, literal lit, unsigned sz, bool values) const;
    public:
        constraint(tag_t t, unsigned id, literal l, unsigned sz, size_t osz): 
            m_tag(t), m_removed(false), m_lit(l), m_watch(sat::null_literal), m_glue(0), m_psm(0), m_size(sz), m_obj_size(osz), m_learned(false), m_id(id), m_pure(false) {
        }
        sat::ext_constraint_idx cindex() const { return sat::constraint_base::mem2base(this); }
        void deallocate(small_object_allocator& a) { a.deallocate(obj_size(), sat::constraint_base::mem2base_ptr(this)); }
        unsigned id() const { return m_id; }
        tag_t tag() const { return m_tag; }
        literal lit() const { return m_lit; }
        unsigned size() const { return m_size; }
        void set_size(unsigned sz) { SASSERT(sz <= m_size); m_size = sz; }
        void update_literal(literal l) { m_lit = l; }
        bool was_removed() const { return m_removed; }
        void set_removed() { m_removed = true; }
        void nullify_literal() { m_lit = sat::null_literal; }
        unsigned glue() const { return m_glue; }
        void set_glue(unsigned g) { m_glue = g; }          
        unsigned psm() const { return m_psm; }
        void set_psm(unsigned p) { m_psm = p; }
        void set_learned(bool f) { m_learned = f; }
        bool learned() const { return m_learned; }            
        bool is_watched() const { return m_watch == m_lit && m_lit != sat::null_literal; }
        void set_watch() { m_watch = m_lit; }
        void reset_watch() { m_watch = sat::null_literal; }
        bool is_clear() const { return m_watch == sat::null_literal && m_lit != sat::null_literal; }
        bool is_pure() const { return m_pure; }
        void set_pure() { m_pure = true; }
        unsigned fold_max_var(unsigned w) const;
        
        size_t obj_size() const { return m_obj_size; }
        card& to_card();
        pb&  to_pb();
        xr& to_xr();
        card const& to_card() const;
        pb const&  to_pb() const;
        xr const& to_xr() const;
        pb_base const& to_pb_base() const; 
        bool is_card() const { return m_tag == tag_t::card_t; }
        bool is_pb() const { return m_tag == tag_t::pb_t; }
        bool is_xr() const { return m_tag == tag_t::xr_t; }

        bool is_watched(solver_interface const& s, literal lit) const;
        void unwatch_literal(solver_interface& s, literal lit);
        void nullify_tracking_literal(solver_interface& s);
        void watch_literal(solver_interface& s, literal lit);
        virtual void clear_watch(solver_interface& s) = 0;
        virtual bool init_watch(solver_interface& s) = 0;
        virtual lbool eval(sat::model const& m) const = 0;
        virtual lbool eval(solver_interface const& s) const = 0;
        virtual bool is_blocked(sat::simplifier& s, literal lit) const = 0;

        virtual bool validate_unit_propagation(solver_interface const& s, literal alit) const = 0;
        
        virtual bool is_watching(literal l) const { UNREACHABLE(); return false; };
        virtual literal_vector literals() const { UNREACHABLE(); return literal_vector(); }
        virtual void swap(unsigned i, unsigned j) { UNREACHABLE(); }
        virtual literal get_lit(unsigned i) const { UNREACHABLE(); return sat::null_literal; }
        virtual void set_lit(unsigned i, literal l) { UNREACHABLE(); }
        virtual bool well_formed() const { return true; }
        virtual void negate() { UNREACHABLE(); }
        virtual bool is_extended_binary(literal_vector& r) const { return false; }
        
        virtual double get_reward(solver_interface const& s, sat::literal_occs_fun& occs) const { return 0; }
        virtual std::ostream& display(std::ostream& out) const = 0;
        virtual std::ostream& display(std::ostream& out, solver_interface const& s, bool values) const = 0;
        virtual void init_use_list(sat::ext_use_list& ul) const = 0;
        
        class iterator {
            constraint const& c;
            unsigned idx;
        public:
            iterator(constraint const& c, unsigned idx) : c(c), idx(idx) {}
            literal operator*() { return c.get_lit(idx); }
            iterator& operator++() { ++idx; return *this; }
            bool operator==(iterator const& other) const { SASSERT(&c == &other.c); return idx == other.idx; }
            bool operator!=(iterator const& other) const { SASSERT(&c == &other.c); return idx != other.idx; }
        };
        
        class literal_iterator {
            constraint const& c;
        public:
            literal_iterator(constraint const& c):c(c) {}
            iterator begin() const { return iterator(c, 0); }
            iterator end() const { return iterator(c, c.size()); }
        };
    };

    std::ostream& operator<<(std::ostream& out, constraint const& c);


}
