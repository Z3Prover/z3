/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mus.h

Abstract:
   
    Faster MUS extraction based on Belov et.al. HYB (Algorithm 3, 4)

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/
#pragma once

namespace sat {
    class mus {
        solver& s;
        literal_vector m_core;
        literal_vector m_mus;
        bool           m_is_active;
        model          m_model;       // model obtained during minimal unsat core
        unsigned       m_max_num_restarts;


    public:
        mus(solver& s);
        ~mus();        
        lbool operator()();
        bool is_active() const { return m_is_active; }
        model const& get_model() const { return m_model; }
    private:
        lbool mus1();
        lbool mus2();
        lbool qx(literal_set& assignment, literal_set& support, bool has_support);
        void reset();
        void set_core();
        void update_model();
        literal_vector & get_core();
        void verify_core(literal_vector const& lits);
        void split(literal_set& src, literal_set& dst);
        void intersect(literal_set& dst, literal_set const& src);
        void unsplit(literal_set& A, literal_set& B);
        class scoped_append {
            unsigned m_size;
            literal_vector& m_lits;
        public:
            scoped_append(literal_vector& lits, literal_vector const& other):
                m_size(lits.size()),
                m_lits(lits) {
                m_lits.append(other);
            }
            ~scoped_append() {
                m_lits.resize(m_size);
            }
                
        };
    };

};

