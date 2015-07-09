/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_quantifier_instances.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-26.

Revision History:

--*/
#ifndef SMT_QUANTIFIER_INSTANCES_H_
#define SMT_QUANTIFIER_INSTANCES_H_

namespace smt {

    class quantifier_instances;

    class quantifier_instance {
        quantifier * m_quantifier;
        double       m_cost;
        enode *      m_enodes[0];
        quantifier_instance(quantifier * q, enode * const * enodes);
        friend class quantifier_instances;
    public:
        quantifier * get_quantifier() const { return m_quantifier; }
        unsigned get_num_decls() const { return m_quantifier->get_num_decls(); }
        double get_cost() const { return m_cost; }
        enode * const * get_enodes() const { return m_enodes; }
        bool operator==(quantifier_instance const & other) const;
        unsigned hash() const;
    };


    class quantifier_instances {
        struct instance_lt {
            ptr_vector<quantifier_instance> const & m_stack;
            instance_lt(ptr_vector<quantifier_instance> const & s):
                m_stack(s) {
            }
            bool operator()(int i1, int i2) const {
                return m_stack[i1]->get_cost() < m_stack[i2]->get_cost();
            }
        };

        context &                          m_context;
        ast_manager &                      m_manager;
        obj_hashtable<quantifier_instance> m_instances;  //!< Set of instances.
        ptr_vector<quantifier_instance>    m_stack;      //!< Stack for backtracking.
        heap<instance_lt>                  m_queue;      //!< Instantiation priority queue.
        unsigned_vector                    m_scopes;
        
        
    };

};

#endif /* SMT_QUANTIFIER_INSTANCES_H_ */

