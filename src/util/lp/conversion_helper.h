/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
namespace lp {
template <typename V>
struct conversion_helper {
    static V get_lower_bound(const column_info<mpq> & ci) {
        return V(ci.get_lower_bound(), ci.lower_bound_is_strict()? 1 : 0);
    }

    static V get_upper_bound(const column_info<mpq> & ci) {
        return V(ci.get_upper_bound(), ci.upper_bound_is_strict()? -1 : 0);
    }
};

template<>
struct conversion_helper <double> {
    static double get_upper_bound(const column_info<mpq> & ci) {
        if (!ci.upper_bound_is_strict())
            return ci.get_upper_bound().get_double();
        double eps = 0.00001;
        if (!ci.lower_bound_is_set())
            return ci.get_upper_bound().get_double() - eps;
        eps = std::min((ci.get_upper_bound() - ci.get_lower_bound()).get_double() / 1000, eps);
        return ci.get_upper_bound().get_double() - eps;
    }

    static double get_lower_bound(const column_info<mpq> & ci) {
        if (!ci.lower_bound_is_strict())
            return ci.get_lower_bound().get_double();
        double eps = 0.00001;
        if (!ci.upper_bound_is_set())
            return ci.get_lower_bound().get_double() + eps;
        eps = std::min((ci.get_upper_bound() - ci.get_lower_bound()).get_double() / 1000, eps);
        return ci.get_lower_bound().get_double() + eps;
    }

};

}
