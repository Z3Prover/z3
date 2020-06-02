/*
  Copyright (c) 2017 Microsoft Corporation
  Author:
  Nickolaj Bjorner (nbjorner)
  Lev Nachmanson   (levnach)
*/
#pragma once
#include "math/lp/lp_settings.h"
namespace lp {
template <typename T>
class lp_bound_propagator {

    // defining a graph on columns x, y such that there is a row x - y = c, where c is a constant    
    struct vertex {        
        unsigned           m_row; 
        unsigned           m_index; // in the row
        bool               m_sign; // true if the vertex plays the role of y
        vector<unsigned>   m_adjacent_edges; // points to the
        vertex(unsigned row, unsigned index) : m_row(row), m_index(index) {}
    };

    // an edge can be between columns in the same row or between two different rows in the same column
    struct edge { 
        unsigned  m_a;
        unsigned  m_b;
        impq      m_offset;
    };
    vector<vertex> m_vertices;
    vector<edge>   m_edges;
    
    std::unordered_map<unsigned, unsigned> m_improved_lower_bounds; // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned> m_improved_upper_bounds;
    T& m_imp;
public:
    vector<implied_bound> m_ibounds;
    lp_bound_propagator(T& imp): m_imp(imp) {}
    const lar_solver& lp() const { return m_imp.lp(); }
    column_type get_column_type(unsigned j) const {
        return m_imp.lp().get_column_type(j);
    }
    
    const impq & get_lower_bound(unsigned j) const {
        return m_imp.lp().get_lower_bound(j);
    }

    const impq & get_upper_bound(unsigned j) const {
        return m_imp.lp().get_upper_bound(j);
    }
    
    void try_add_bound(mpq const& v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict) {
        j = m_imp.lp().adjust_column_index_to_term_index(j);    

        lconstraint_kind kind = is_low? GE : LE;
        if (strict)
            kind = static_cast<lconstraint_kind>(kind / 2);
    
        if (!m_imp.bound_is_interesting(j, kind, v))
            return;
        unsigned k; // index to ibounds
        if (is_low) {
            if (try_get_value(m_improved_lower_bounds, j, k)) {
                auto & found_bound = m_ibounds[k];
                if (v > found_bound.m_bound || (v == found_bound.m_bound && found_bound.m_strict == false && strict)) {
                    found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                    TRACE("try_add_bound", m_imp.lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_lower_bounds[j] = m_ibounds.size();
                m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
                TRACE("try_add_bound", m_imp.lp().print_implied_bound(m_ibounds.back(), tout););
            }
        } else { // the upper bound case
            if (try_get_value(m_improved_upper_bounds, j, k)) {
                auto & found_bound = m_ibounds[k];
                if (v < found_bound.m_bound || (v == found_bound.m_bound && found_bound.m_strict == false && strict)) {
                    found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                    TRACE("try_add_bound", m_imp.lp().print_implied_bound(found_bound, tout););
                }
            } else {
                m_improved_upper_bounds[j] = m_ibounds.size();
                m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
                TRACE("try_add_bound", m_imp.lp().print_implied_bound(m_ibounds.back(), tout););
            }
        }
    }

    void consume(const mpq& a, constraint_index ci) {
        m_imp.consume(a, ci);
    }

    void create_initial_xy(unsigned x, unsigned y, unsigned row_index) {
        impq value;
        const auto& row =  lp().get_row(row_index);
        for (unsigned k = 0; k < row.size(); k++) {
            if (k == x || k == y)
                continue;
            const auto& c = row[k];
            value += c.coeff() * lp().get_lower_bound(c.var());
        }
        vertex xv(row_index, x);
        m_vertices.push_back(xv);
        vertex yv(row_index, y);
        m_vertices.push_back(yv);
        
        NOT_IMPLEMENTED_YET();
    }
    
    void try_create_eq(unsigned x, unsigned y, unsigned row_index) {
        m_vertices.clear();
        m_edges.clear();
        create_initial_xy(x, y, row_index);
        NOT_IMPLEMENTED_YET();
        
    }
};
}
