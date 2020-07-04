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

#pragma once

#include "util/util.h"
#include "util/vector.h"

namespace smt {
    template<typename TV>
    inline std::string pp_vector(std::string const & label, TV v) {
        std::ostringstream oss;
        oss << label << " ";
        for (unsigned i = 0; i < v.size(); ++i) {
            oss << v[i] << " ";
        }
        oss << std::endl;
        return oss.str();
    }

    class spanning_tree_base { 
    public:
        typedef int node_id;
        typedef int edge_id;
        virtual void initialize(svector<edge_id> const & tree) = 0;
        virtual void get_descendants(node_id start, svector<node_id> & descendants) = 0;
        
        virtual void update(edge_id enter_id, edge_id leave_id) = 0;
        virtual void get_path(node_id start, node_id end, svector<edge_id> & path, bool_vector & against) = 0;
        virtual bool in_subtree_t2(node_id child) = 0;

        virtual bool check_well_formed() = 0;
    };
}

