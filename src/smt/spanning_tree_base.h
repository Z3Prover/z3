/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    spanning_tree_base.h

Abstract:

    Represent spanning trees with needed operations for Network Simplex

Author:

    Anh-Dung Phan (t-anphan) 2013-11-06

Notes:
   
--*/

#ifndef _SPANNING_TREE_BASE_H_
#define _SPANNING_TREE_BASE_H_

#include "util.h"
#include "vector.h"

namespace smt {
    template<typename TV>
    inline std::string pp_vector(std::string const & label, TV v, bool has_header = false) {
        std::ostringstream oss;
        if (has_header) {
            oss << "Index ";
            for (unsigned i = 0; i < v.size(); ++i) {
                oss << i << " ";
            }
            oss << std::endl;
        }
        oss << label << " ";
        for (unsigned i = 0; i < v.size(); ++i) {
            oss << v[i] << " ";
        }
        oss << std::endl;
        return oss.str();
    }

    class spanning_tree_base { 
    private:
        typedef int node;

    public:
        virtual void initialize(svector<bool> const & upwards) {};
        virtual void get_descendants(node start, svector<node> & descendants) {};
        
        virtual void update(edge_id enter_id, edge_id leave_id, bool & is_swap_enter, bool & is_swap_leave) {};
        virtual bool check_well_formed() {UNREACHABLE(); return false;};
        virtual void get_path(node start, node end, svector<edge_id> & path, svector<bool> & against) {};
        virtual bool is_forward_edge(edge_id e_id) const {UNREACHABLE(); return false;};
        virtual bool is_ancestor_of(node ancestor, node child) {UNREACHABLE(); return false;};
    };
}

#endif