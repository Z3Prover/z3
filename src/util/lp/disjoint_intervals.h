/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include <map>
namespace lp {
// represents the set of disjoint intervals of integer number
struct disjoint_intervals {
    std::map<int, short> m_endpoints; // 0 means start, 1 means end, 2 means both - for a point interval
    bool m_empty;
    // constructors create an interval containing all integer numbers or an empty interval
    disjoint_intervals() : m_empty(false) {}
    disjoint_intervals(bool is_empty) : m_empty(is_empty) {}

    bool is_start(short x) const { return x == 0 || x == 2; }
    bool is_start(const std::map<int, short>::iterator & it) const {
        return is_start(it->second);
    }
    bool is_start(const std::map<int, short>::reverse_iterator & it) const {
        return is_start(it->second);
    }
    bool is_end(short x) const { return x == 1 || x == 2; }
    bool is_end(const std::map<int, short>::iterator & it) const {
        return is_end(it->second);
    }
    bool is_end(const std::map<int, short>::reverse_iterator & it) const {
        return is_end(it->second);
    }

    int pos(const std::map<int, short>::iterator & it) const {
        return it->first;
    }
    int pos(const std::map<int, short>::reverse_iterator & it) const {
        return it->first;
    }

    int bound_kind(const std::map<int, short>::iterator & it) const {
        return it->second;
    }

    int bound_kind(const std::map<int, short>::reverse_iterator & it) const {
        return it->second;
    }

    bool is_proper_start(short x) const { return x == 0; }
    bool is_proper_end(short x) const { return x == 1; }
    bool is_proper_end(const std::map<int, short>::iterator & it) const {
        return is_proper_end(it->second);
    }
    bool is_proper_end(const std::map<int, short>::reverse_iterator & it) const {
        return is_proper_end(it->second);
    }

    bool is_one_point_interval(short x) const { return x == 2; }
    bool is_one_point_interval(const std::map<int, short>::iterator & it) const {
        return is_one_point_interval(it->second);
    }
    bool is_one_point_interval(const std::map<int, short>::reverse_iterator & it) const {
        return is_one_point_interval(it->second);
    }


    void erase(int x) {
        m_endpoints.erase(x);
    }
    
    void set_one_point_segment(int x) {
        m_endpoints[x] = 2;
    }

    void set_start(int x) {
        m_endpoints[x] = 0;
    }

    void set_end(int x) {
        m_endpoints[x] = 1;
    }

    void remove_all_endpoints_below(int x) {
        while (m_endpoints.begin() != m_endpoints.end() && m_endpoints.begin()->first < x)
            m_endpoints.erase(m_endpoints.begin());
    }
    // we intersect the existing set with the half open to the right interval
    void intersect_with_lower_bound(int x) {
        if (m_empty)
            return;
        if (m_endpoints.empty()) {
            set_start(x);
            return;
        }
        bool pos_inf = has_pos_inf();
        auto it = m_endpoints.begin();
        while (it != m_endpoints.end() && pos(it) < x) {
            m_endpoints.erase(it);
            it = m_endpoints.begin();
        }
        if (m_endpoints.empty()) {
            if (!pos_inf) {
                m_empty = true;
                return;
            } 
            set_start(x);
            return;
        }
        lp_assert(pos(it) >= x);
        if (pos(it) == x) {
            if (is_proper_end(it))
                set_one_point_segment(x);			
        }
        else { // x(it) > x
            if (is_proper_end(it)) {
                set_start(x);
            }
        }

        lp_assert(is_correct());
    }

    // we intersect the existing set with the half open interval
    void intersect_with_upper_bound(int x) {
        if (m_empty)
            return;
        if (m_endpoints.empty()) {
            set_end(x);
            return;
        }
        bool neg_inf = has_neg_inf();
        auto it = m_endpoints.rbegin();

        while (!m_endpoints.empty() && pos(it) > x) {
            m_endpoints.erase(std::prev(m_endpoints.end()));
            it = m_endpoints.rbegin();
        }
        if (m_endpoints.empty()) {
            if (!neg_inf) {
                m_empty = true;
                return;
            }
            set_end(x);
        }
        lp_assert(pos(it) <= x);
        if (pos(it) == x) {
            if (is_one_point_interval(it)) {} 
            else if (is_proper_end(it)) {}
            else {// is_proper_start(it->second)
                set_one_point_segment(x);
            }
        }
        else { // pos(it) < x} 
            if (is_start(it))
                set_end(x);
        }
        lp_assert(is_correct());
    }

    bool has_pos_inf() const {
        if (m_empty)
            return false;

        if (m_endpoints.empty())
            return true;
        
        lp_assert(m_endpoints.rbegin() != m_endpoints.rend());
        return m_endpoints.rbegin()->second == 0;
    }

    bool has_neg_inf() const {
        if (m_empty)
            return false;

        if (m_endpoints.empty())
            return true;
        auto it = m_endpoints.begin();
        return is_proper_end(it->second);//m_endpoints.begin());
    }

    // we are intersecting
    void intersect_with_interval(int x, int y) {
        if (m_empty)
            return;
        lp_assert(x <= y);
        intersect_with_lower_bound(x);
        intersect_with_upper_bound(y);
    }

    // add an intervar [x, inf]
    void unite_with_interval_x_pos_inf(int x) {
        if (m_empty) {
            set_start(x);
            m_empty = false;
            return;
        }

        while (!m_endpoints.empty() && pos(m_endpoints.rbegin()) > x) {
            m_endpoints.erase(std::prev(m_endpoints.end()));
        }
        
        if (m_endpoints.empty()) {
            set_start(x);
            return;
        }
        auto it = m_endpoints.rbegin();
        lp_assert(pos(it) <= x);
        if (pos(it) == x) {
            if (is_end(it)) {
                m_endpoints.erase(x);
            } else {
                set_start(x);
            }
        } else if (pos(it) == x - 1 && is_end(it)) {
            m_endpoints.erase(x - 1); // closing the gap
        } else {
            if (!has_pos_inf())
                set_start(x);
        }
    }

    // add an interval [-inf, x]
    void unite_with_interval_neg_inf_x(int x) {
        if (m_empty) {
            set_end(x);
            m_empty = false;
            return;
        }
        auto it = m_endpoints.upper_bound(x);
        
        if (it == m_endpoints.end()) {
            bool pos_inf = has_pos_inf();
            m_endpoints.clear();
            // it could be the case where x is inside of the last infinite interval with pos inf
            if (!pos_inf)
                set_end(x);
            return;
        }
        lp_assert(pos(it) > x);
        if (is_one_point_interval(pos(it))) {
            set_end(it->second);
        } else {
            if (is_start(it->second)) {
                set_end(x);
            }
        }
        
        while (!m_endpoints.empty() && m_endpoints.begin()->first < x) {
            m_endpoints.erase(m_endpoints.begin());
        }
        lp_assert(is_correct());
    }

    void unite_with_interval(int x, int y) {
        lp_assert(false); // not implemented
    }

    bool is_correct() const {
        if (m_empty) {
            if (m_endpoints.size() > 0) {
                std::cout << "is empty is true but m_endpoints.size() = " << m_endpoints.size() << std::endl;
                return false;
            }
            return true;
        }
        bool expect_end;
        bool prev = false;
        int prev_x;
        for (auto t : m_endpoints) {
            if (prev && (expect_end != t.second > 0)) {
                std::cout << "x = " << t.first << "\n";
                if (expect_end) {
                    std::cout << "expecting an interval end\n";
                } else {
                    std::cout << "expecting an interval start\n";
                }
                return false;
            }

            if (t.second == 2) {
                expect_end = false; // swallow a point interval
            } else {
                if (prev)
                    expect_end = !expect_end;
                else
                    expect_end = is_start(t.second);
            }
            if (prev) {
                if (t.first - prev_x <= 1) {
                    std::cout << "the sequence is not increasing or the gap is too small: " << prev_x << ", " << t.first << std::endl;
                    return false;
                }
            } 
            prev = true;
            prev_x = t.first;
        }
            
        return true;
    }

    void print(std::ostream & out) const {
        if (m_empty) {
            out << "empty\n";
            return;
        }
        if (m_endpoints.empty()){
            out << "[-oo,oo]\n";
            return;
        }
        bool first = true;
        for (auto t : m_endpoints) {
            if (first) {
                if (t.second == 1) {
                    out << "[-oo," << t.first << "]";
                }
                else if (t.second == 0)
                    out << "[" << t.first << ",";
                else if (t.second == 2)
                    out << "[" << t.first << "]";
                first = false;
            } else {
                if (t.second==0)
                    out << "[" << t.first << ",";
                else if (t.second == 1)
                    out << t.first << "]";
                else if (t.second == 2)
                    out << "[" << t.first << "]";
            }
        }
        if (has_pos_inf())
            out << "oo]";
        out << "\n";
    }
    
    
};
}
