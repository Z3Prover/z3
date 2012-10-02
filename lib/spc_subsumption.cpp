/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_subsumption.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-13.

Revision History:

--*/
#include"spc_subsumption.h"
#include"fvi_def.h"
#include"ast_pp.h"

namespace spc {

    /**
       \brief Return true if literal l2 is an instance of l1.
       
       When ResetSubst == true, m_subst is reset before trying to match l1 and l2.

       When ResetSubst == false, it is assumed that m_subst.push_scope was invoked
       before invoking match_literal. 
    */
    template<bool ResetSubst>
    bool subsumption::match_literal(literal const & l1, literal const & l2) {
        if (l1.sign() == l2.sign()) {
            expr * atom1 = l1.atom();
            expr * atom2 = l2.atom();
            bool is_eq1  = m_manager.is_eq(atom1);
            bool is_eq2  = m_manager.is_eq(atom2);
            if (is_eq1 && is_eq2) {
                expr * lhs1 = to_app(atom1)->get_arg(0);
                expr * rhs1 = to_app(atom1)->get_arg(1);
                expr * lhs2 = to_app(atom2)->get_arg(0);
                expr * rhs2 = to_app(atom2)->get_arg(1);
                if (ResetSubst) 
                    m_subst.reset_subst();
                
                if (m_matcher(lhs1, lhs2, m_subst) && m_matcher(rhs1, rhs2, m_subst))
                    return true;

                if (ResetSubst)
                    m_subst.reset_subst();
                else {
                    // I'm assuming push_scope was invoked before executing match_literal
                    // So, pop_scope is equivalent to a local reset.
                    m_subst.pop_scope();
                    m_subst.push_scope();
                }

                return (m_matcher(lhs1, rhs2, m_subst) && m_matcher(rhs1, lhs2, m_subst));
            }
            else if (!is_eq1 && !is_eq2) {
                if (ResetSubst) 
                    m_subst.reset_subst();
                return m_matcher(atom1, atom2, m_subst);
            }
        }
        return false;
    }
    
    /**
       \brief Return true if for every literal l1 in lits1 there is a
       literal l2 in lits2 such that l2 is an instance of l1.
    */
    bool subsumption::can_subsume(unsigned num_lits1, literal * lits1, unsigned num_lits2, literal * lits2) {
        for (unsigned i = 0; i < num_lits1; i++) {
            literal const & l1 = lits1[i];
            unsigned j = 0;
            for (; j < num_lits2; j++) {
                literal const & l2 = lits2[j];
                if (match_literal<true>(l1, l2))
                    break;
            }
            if (j == num_lits2)
                return false;
        }
        return true;
    }

    /**
       \brief Return true if cls1 can subsume cls2. It performs a series of quick checks.
    */
    bool subsumption::quick_check(clause * cls1, clause * cls2) {
        return 
            cls1->get_symbol_count() <= cls2->get_symbol_count() &&
            cls1->get_const_count() <= cls2->get_const_count() &&
            cls1->get_depth() <= cls2->get_depth() &&
            cls1->get_num_pos_literals() <= cls2->get_num_pos_literals() &&
            cls1->get_num_neg_literals() <= cls2->get_num_neg_literals() &&
            (!cls1->is_ground() || cls2->is_ground());
    }
    
    /**
       \brief Return true if the set of literals lits1 subsumes the set of literals lits2.
    */
    bool subsumption::subsumes_core(unsigned num_lits1, literal * lits1, unsigned num_lits2, literal * lits2) {
        enum state {
            INVOKE, DECIDE, BACKTRACK, RETURN
        };

        if (num_lits1 == 0)
            return true;
        
        m_stack.reset();
        m_subst.reset();

        m_stack.push_back(assoc(0, 0));
        state st = DECIDE;

        unsigned i;
        assoc * top;
        unsigned counter = 0;
#ifdef _TRACE
        unsigned opt  = 0;
        unsigned nopt = 0;
#endif
        while (true && counter < 5000000) {
            counter++;
            switch (st) {
            case INVOKE:
                SASSERT(!m_stack.empty());
                i = m_stack.back().first + 1;
                if (i >= num_lits1) {
                    TRACE("subsumption", tout << "subsumption result: YES.\n";);
                    TRACE_CODE({
                        if (counter > 10000) {
                            TRACE("subsumption_perf", 
                                  tout << "subsumption succeeded: " << counter << " " << opt << " " << nopt << "\n";
                                  tout << "literals1:\n"; display(tout, num_lits1, lits1, m_manager); tout << "\n";
                                  tout << "literals2:\n"; display(tout, num_lits2, lits2, m_manager); tout << "\n";);
                        }
                    });
                    return true;
                }
                else {
                    m_stack.push_back(assoc(i, 0));
                    st = DECIDE;
                }
                break;
            case DECIDE:
                top = &(m_stack.back());
                m_subst.push_scope();
                if (match_literal<false>(lits1[top->first], lits2[top->second]))
                    st = INVOKE;
                else
                    st = BACKTRACK;
                break;
            case BACKTRACK: 
                top = &(m_stack.back());
                top->second++;
                m_subst.pop_scope();
                if (top->second >= num_lits2) 
                    st = RETURN;
                else
                    st = DECIDE;
                break;
            case RETURN:
                top = &(m_stack.back());
                m_stack.pop_back();
                if (m_stack.empty()) {
                    // no more alternatives
                    TRACE("subsumption", tout << "subsumption result: NO\n";);
                    TRACE_CODE({
                        if (counter > 10000) {
                            TRACE("subsumption_perf",
                                  tout << "subsumption failed: " << counter << " " << opt << " " << nopt << "\n";
                                  tout << "literals1:\n"; display(tout, num_lits1, lits1, m_manager); tout << "\n";
                                  tout << "literals2:\n"; display(tout, num_lits2, lits2, m_manager); tout << "\n";);
                        }
                    });
                    return false;
                }
                if (m_subst.top_scope_has_bindings()) {
                    TRACE_CODE(nopt++;);
                    st  = BACKTRACK;
                }
                else {
                    TRACE_CODE(opt++;);
#ifdef Z3DEBUG
                    unsigned num_bindings = m_subst.get_num_bindings();
#endif
                    m_subst.pop_scope();
                    SASSERT(num_bindings == m_subst.get_num_bindings());
                    st = RETURN;
                }
                break;
            }
        }
        return false;
    }

    /**
       \brief Return true if the set of ground literals lits1 subsumes the set of ground literals lits2.
    */
    bool subsumption::ground_subsumes_core(unsigned num_lits1, literal * lits1, unsigned num_lits2, literal * lits2) {
        for (unsigned i = 0; i < num_lits1; i++) {
            literal const & l1 = lits1[i];
            unsigned j = 0;
            for (; j < num_lits2; j++) {
                literal const & l2 = lits2[j];
                if (l1 == l2)
                    break;
            }
            if (j == num_lits2)
                return false;
        }
        return true;
    }

    /**
       \brief Return true if the literal l1 subsumes the set of literals lits2.
    */
    bool subsumption::subsumes_core(literal const & l1, unsigned num_lits2, literal * lits2) {
        for (unsigned i = 0; i < num_lits2; i++) {
            if (match_literal<true>(l1, lits2[i]))
                return true;
        }
        return false;
    }

    subsumption::subsumption(ast_manager & m, asserted_literals & al, spc_params & params):
        m_manager(m),
        m_params(params),
        m_asserted_literals(al),
        m_subst(m),
        m_matcher(m),
        m_found_decls(m), 
        m_index(0),
        m_num_processed_clauses(0),
        m_opt_threshold(params.m_initial_subsumption_index_opt) {

        m_subst.reserve_offsets(1);
        
        init_indexes();
    }

    subsumption::~subsumption() {
        if (m_index) 
            dealloc(m_index);
    }

    /**
       \brief Return true if cls1 subsumes cls2
    */
    bool subsumption::operator()(clause * cls1, clause * cls2) {
        TRACE("subsumption_detail", tout << "checking if:\n"; cls1->display(tout, m_manager); tout << "\nsubsumes\n";
              cls2->display(tout, m_manager); tout << "\n";);
        if (!quick_check(cls1, cls2)) {
            TRACE("subsumption_detail", tout << "failed quick check\n";);
            return false;
        }
       
        m_subst.reserve_vars(std::max(cls1->get_num_vars(), cls2->get_num_vars()));
        unsigned num_lits1 = cls1->get_num_literals();
        unsigned num_lits2 = cls2->get_num_literals();
        literal * lits1    = cls1->get_literals();
        literal * lits2    = cls2->get_literals();
        if (cls1->is_ground() && cls2->is_ground())
            return ground_subsumes_core(num_lits1, lits1, num_lits2, lits2);
        if (num_lits1 == 1)
            return subsumes_core(lits1[0], num_lits2, lits2);
        // TODO: REMOVE true below... using it for debugging purposes.
        if (true || cls1->get_num_neg_literals() >= 3 || cls1->get_num_pos_literals() >= 3)
            if (!can_subsume(num_lits1, lits1, num_lits2, lits2)) {
                TRACE("subsumption_detail", tout << "failed can_subsume\n";);
                return false;
            }
        return subsumes_core(num_lits1, lits1, num_lits2, lits2);
    }

    /**
       \brief Update the set of function symbols found in the clause being inserted into the index,
       and the set of clauses found since the index started to be built.
       
       Return true if the function symbol should be tracked.
    */
    bool subsumption::mark_func_decl(func_decl * f) {
        if (m_refining_index) {
            if (!m_cls_found_decl_set.contains(f)) {
                // update set of func_decls in the curr clause
                m_cls_found_decl_set.insert(f);
                m_cls_found_decls.push_back(f);
                // update global set of founf func_decls
                unsigned id = f->get_decl_id();
                m_found_decl_set.reserve(id+1);
                if (!m_found_decl_set.get(id)) {
                    m_found_decl_set.set(id);
                    m_found_decls.push_back(f);
                }
            }
            return true;
        }
        else {
            unsigned id = f->get_decl_id();
            // if func_decl was not found yet, then ignore it.
            if (id < m_found_decl_set.size() && m_found_decl_set.get(id)) {
                if (!m_cls_found_decl_set.contains(f)) {
                    // update set of func_decls in the curr clause
                    m_cls_found_decl_set.insert(f);
                    m_cls_found_decls.push_back(f);
                }
                return true;
            }
            return false;
        }
    }

    /**
       \brief Increment the number of occurrences of a function symbol in the clause being
       inserted into the index.
    */
    void subsumption::inc_f_count(func_decl * f, bool neg) {
        decl2nat & f_count = m_f_count[static_cast<unsigned>(neg)];
        unsigned val;
        if (f_count.find(f, val)) {
            f_count.insert(f, val + 1);
        }
        else {
            f_count.insert(f, 1);
        }
    }

    /**
       \brief Update the min/max num. of occurrences of func symbol in a clause.
    */
    void subsumption::update_min_max(func_decl * f) {
        for (unsigned is_neg = 0; is_neg < 1; is_neg++) {
            decl2nat & f_count = m_f_count[is_neg];
            decl2nat & f_min   = m_f_min[is_neg];
            decl2nat & f_max   = m_f_max[is_neg];
            unsigned count;
            if (f_count.find(f, count)) {
                unsigned old_count;
                if (!f_min.find(f, old_count) || old_count > count) {
                    f_min.insert(f, count);
                }
                if (!f_max.find(f, old_count) || old_count < count) {
                    f_max.insert(f, count);
                }
            }
        }
    }

    /**
       \brief Compute the number of occurences of function symbols in
       a clause.
    */
    void subsumption::update_neg_pos_func_counts(clause * cls) {
        m_f_count[0].reset();
        m_f_count[1].reset();
        m_cls_found_decl_set.reset();
        m_cls_found_decls.reset();
        ptr_buffer<expr> todo;
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = cls->get_literal(i);
            bool is_neg       = l.sign();
            expr * n          = l.atom();
            todo.push_back(n);
            while (!todo.empty()) {
                n = todo.back();
                todo.pop_back();
                if (is_app(n)) {
                    func_decl * f = to_app(n)->get_decl();
                    if (fvi_candidate(f) && mark_func_decl(f)) 
                        inc_f_count(f, is_neg);
                    unsigned num = to_app(n)->get_num_args();
                    for (unsigned i = 0; i < num; i++) 
                        todo.push_back(to_app(n)->get_arg(i));
                }
            }
        }
        
        if (m_refining_index) {
            ptr_vector<func_decl>::iterator it  = m_cls_found_decls.begin();
            ptr_vector<func_decl>::iterator end = m_cls_found_decls.end();
            for (; it != end; ++it) {
                func_decl * f = *it;
                update_min_max(f);
                unsigned val;
                if (m_f_freq.find(f, val))
                    m_f_freq.insert(f, val + 1);
                else
                    m_f_freq.insert(f, 1);
            }
        }
    }

    /**
       \brief Store in m_feature_vector the value for the features of cls.
    */
    void subsumption::compute_features(clause * cls, unsigned * fvector) {
        unsigned num = m_features.size();
        for (unsigned i = 0; i < num; i++) {
            feature & f = m_features[i];
            switch (f.m_kind) {
            case F_GROUND:
                fvector[i] = cls->is_ground();
                break;
            case F_NUM_POS_LITS:
                fvector[i] = cls->get_num_pos_literals();
                break;
            case F_NUM_NEG_LITS:
                fvector[i] = cls->get_num_neg_literals();
                break;
            case F_DEPTH:
                fvector[i] = cls->get_depth();
                break;
            case F_CONST_COUNT:
                fvector[i] = cls->get_const_count();
                break;
            case F_SYM_COUNT:
                fvector[i] = cls->get_symbol_count();
                break;
            case F_NUM_NEG_FUNCS: {
                unsigned val;
                if (m_f_count[1].find(f.m_decl, val)) 
                    fvector[i] = val;
                else
                    fvector[i] = 0;
                break;
            }
            case F_NUM_POS_FUNCS: {
                unsigned val;
                if (m_f_count[0].find(f.m_decl, val)) 
                    fvector[i] = val;
                else
                    fvector[i] = 0;
                break;
            }
            default:
                UNREACHABLE();
            }
        }
        TRACE("subsumption_features",
              tout << "features of: "; cls->display(tout, m_manager); tout << "\n";
              for (unsigned i = 0; i < num; i++) {
                  tout << fvector[i] << " ";
              }
              tout << "\n";);
    }

    /**
       \brief Initialise indexes for forward/backward subsumption.
    */
    void subsumption::init_indexes() {
        // index for forward/backward subsumption
        // start with simple set of features
        m_features.push_back(feature(F_GROUND));
        m_features.push_back(feature(F_NUM_POS_LITS));
        m_features.push_back(feature(F_NUM_NEG_LITS));
        m_features.push_back(feature(F_DEPTH));
        m_features.push_back(feature(F_CONST_COUNT));
        m_features.push_back(feature(F_SYM_COUNT));
        m_index = alloc(index, m_features.size(), to_feature_vector(*this));
    }

    unsigned subsumption::get_value_range(func_decl * f, bool neg) const {
        unsigned i = static_cast<unsigned>(neg);
        unsigned min;
        unsigned max;
        if (!m_f_min[i].find(f, min))
            min = 0;
        if (!m_f_max[i].find(f, max))
            max = 0;
        SASSERT(min <= max);
        return max - min;
    }

    inline unsigned subsumption::get_value_range(func_decl * f) const {
        return std::max(get_value_range(f, false), get_value_range(f, true));
    }

    bool subsumption::f_lt::operator()(func_decl * f1, func_decl * f2) const {
        unsigned vrange1 = m_owner.get_value_range(f1);
        unsigned vrange2 = m_owner.get_value_range(f2);
        if (vrange1 < vrange2)
            return true;
        if (vrange1 == vrange2)
            return f1->get_id() < f2->get_id();
        return false;
    }

    /**
       \brief Optimize the index for (non unit) forward subsumption and 
       backward subsumption.
    */
    void subsumption::optimize_feature_index() {
        ptr_vector<clause> clauses;
        m_index->collect(clauses);

        dealloc(m_index);
        m_features.reset();

        ptr_vector<func_decl> targets;
        unsigned sz = m_found_decls.size();
        for (unsigned i = 0; i < sz; i++) {
            func_decl * f = m_found_decls.get(i);
            unsigned val;
            if (m_f_freq.find(f, val) && val > m_params.m_min_func_freq_subsumption_index && get_value_range(f) > 0) 
                targets.push_back(f);
        }

        
        f_lt lt(*this);
        std::sort(targets.begin(), targets.end(), lt);
        
        m_features.push_back(feature(F_GROUND));
        m_features.push_back(feature(F_NUM_POS_LITS));
        m_features.push_back(feature(F_NUM_NEG_LITS));
        m_features.push_back(feature(F_DEPTH));
       
        ptr_vector<func_decl>::iterator it  = targets.begin();
        ptr_vector<func_decl>::iterator end = targets.end();
        for (; it != end; ++it) {
            func_decl * f = *it;
            if (get_value_range(f, false) > 1)
                m_features.push_back(feature(f, false));
            if (get_value_range(f, true) > 1)
                m_features.push_back(feature(f, true));
            if (m_features.size() > m_params.m_max_subsumption_index_features)
                break;
        }
        
        m_features.push_back(feature(F_CONST_COUNT));
        m_features.push_back(feature(F_SYM_COUNT));
        m_index = alloc(index, m_features.size(), to_feature_vector(*this));
        m_num_processed_clauses = 0;
        unsigned new_threshold = static_cast<unsigned>(m_opt_threshold * m_params.m_factor_subsumption_index_opt);
        if (new_threshold > m_opt_threshold)
            m_opt_threshold = new_threshold;
    }
    
    /**
       \brief Insert cls into the indexes used for forward/backward subsumption.
    */
    void subsumption::insert(clause * cls) {
        TRACE("subsumption", tout << "adding clause to subsumption index: " << cls << "\n"; cls->display(tout, m_manager); tout << "\n";);
        unsigned num_lits = cls->get_num_literals();
        if (num_lits > 1 || m_params.m_backward_subsumption) {
            m_index->insert(cls);
            SASSERT(m_index->contains(cls));
            m_num_processed_clauses++;
            if (m_num_processed_clauses > m_opt_threshold)
                optimize_feature_index();
        }
    }

    /**
       \brief Remove cls from the indexes used for forward/backward subsumption.
    */
    void subsumption::erase(clause * cls) {
        TRACE("subsumption", tout << "removing clause from subsumption index:" << cls << "\n"; cls->display(tout, m_manager); tout << "\n";
              tout << "num lits.: " << cls->get_num_literals() << ", backward_sub: " << m_params.m_backward_subsumption << "\n";);
        unsigned num_lits = cls->get_num_literals();
        if (num_lits > 1 || m_params.m_backward_subsumption)
            m_index->erase(cls);
    }

    /**
       \brief Reset the indexes used for forward/backward subsumption.
    */
    void subsumption::reset() {
        if (m_index)
            m_index->reset();
        m_num_processed_clauses = 0;
        m_opt_threshold = m_params.m_initial_subsumption_index_opt;
    }

    /**
       \brief Return an unit clause C in the index that subsumes cls.
       Return 0 if such clause does not exist.
    */
    clause * subsumption::unit_forward(clause * cls) {
        if (!m_asserted_literals.has_literals())
            return 0;
        m_asserted_literals.reserve_vars(cls->get_num_vars());
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = cls->get_literal(i);
            clause * subsumer = m_asserted_literals.gen(l);
            if (subsumer)
                return subsumer;
        }
        return 0;
    }

    struct non_unit_subsumption_visitor {
        subsumption & m_owner;
        clause *      m_new_clause;
        clause *      m_subsumer;
        non_unit_subsumption_visitor(subsumption & owner, clause * new_clause):
            m_owner(owner),
            m_new_clause(new_clause),
            m_subsumer(0) {
        }
        bool operator()(clause * candidate) {
            TRACE("subsumption_index", tout << "considering candidate:\n"; candidate->display(tout, m_owner.get_manager()); tout << "\n";);
            if (candidate->get_num_literals() > 1 && m_owner(candidate, m_new_clause)) {
                m_subsumer = candidate;
                return false; // stop subsumer was found
            }
            return true; // continue;
        }
    };

    /**
       \brief Return a non unit clause C in the index that subsumes cls.
       Return 0 if such clause does not exist.
    */
    clause * subsumption::non_unit_forward(clause * cls) {
        non_unit_subsumption_visitor visitor(*this, cls);
        m_index->visit(cls, visitor, true);
        return visitor.m_subsumer;
    }

    /**
       \brief Return a unit equality clause (= s t) that (eq) subsumes cls.
       That is, cls contains a literal (= u[s'] u[t']) and there is 
       a substitution sigma s.t. sigma(s) = s' and sigma(t) = t'.
       Return 0 if such clause does not exist.
    */
    clause * subsumption::eq_subsumption(clause * cls) {
        if (!m_asserted_literals.has_pos_literals())
            return 0;
        m_asserted_literals.reserve_vars(cls->get_num_vars());
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = cls->get_literal(i);
            expr * atom = l.atom();
            if (!l.sign() && m_manager.is_eq(atom)) {
                expr * lhs = to_app(atom)->get_arg(0);
                expr * rhs = to_app(atom)->get_arg(1);
                clause * subsumer = m_asserted_literals.subsumes(lhs, rhs);
                if (subsumer) {
                    TRACE("eq_subsumption", tout << "equality subsumption:\n"; cls->display(tout, m_manager); 
                          tout << "\nis subsumed by:\n"; subsumer->display(tout, m_manager); tout << "\n";);
                    return subsumer;
                }
            }
        }
        return 0;
    }

    /**
       \brief Return a clause C in the index (i.e., insert(C) was invoked) that subsumes cls.
       Return 0 if such clause does not exist.
    */
    clause * subsumption::forward(clause * cls) {
        TRACE("subsumption", tout << "trying forward subsumption:\n"; cls->display(tout, m_manager); tout << "\n";);
        clause * subsumer = unit_forward(cls);
        if (subsumer)
            return subsumer;
        subsumer = non_unit_forward(cls);
        if (subsumer)
            return subsumer;
        if (m_params.m_equality_subsumption) 
            return eq_subsumption(cls);
        return 0;
    }

    struct backward_subsumption_visitor {
        subsumption &        m_owner;
        clause *             m_new_clause;
        ptr_buffer<clause> & m_result;
        backward_subsumption_visitor(subsumption & owner, clause * new_clause, ptr_buffer<clause> & result):
            m_owner(owner),
            m_new_clause(new_clause),
            m_result(result) {
        }
        
        bool operator()(clause * candidate) {
            if (m_owner(m_new_clause, candidate))
                m_result.push_back(candidate); 
            return true; // always continue in backward subsumption
        }
    };

    /**
       \brief Store in result the set of clauses in the index that are subsumes by cls.
    */
    void subsumption::backward(clause * cls, ptr_buffer<clause> & result) {
        if (m_params.m_backward_subsumption) {
            backward_subsumption_visitor visitor(*this, cls, result);
            m_index->visit(cls, visitor, false);
        }
    }
};
