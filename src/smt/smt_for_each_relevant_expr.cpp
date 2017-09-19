/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_for_each_relevant_expr.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-05.

Revision History:

--*/
#include "smt/smt_context.h"
#include "smt/smt_for_each_relevant_expr.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

namespace smt {

    bool check_at_labels::check(expr* n) {
        m_first = true;
        return count_at_labels_pos(n) <= 1;
    }

    unsigned check_at_labels::count_at_labels_lit(expr* n, bool polarity) {
        unsigned count = 0;
        buffer<symbol> lbls;
        bool pos;
        if (m_manager.is_label_lit(n, lbls) || (m_manager.is_label(n, pos, lbls) && pos == polarity)) {
            buffer<symbol>::const_iterator it  = lbls.begin();
            buffer<symbol>::const_iterator end = lbls.end();
            for (; it != end; ++it) {
                symbol const & s = *it;
                if (s.contains('@')) {
                    TRACE("for_each_relevant_expr", tout << "@ label: " << mk_pp(n, m_manager) << "\n";);
                    count += 1;
                }
            }
        }
        return count;
    }


    unsigned check_at_labels::count_at_labels_neg(expr* n) {
        if (!is_app(n)) {
            return 0;
        }
        app* a = to_app(n);
        unsigned sz = a->get_num_args();
        unsigned count = count_at_labels_lit(n, false);

        if (m_manager.is_or(n)) {
            for (unsigned i = 0; i < sz; ++i) {
                count += count_at_labels_neg(a->get_arg(i));
            }
        }
        else if (m_manager.is_not(n)) {
            count = count_at_labels_pos(a->get_arg(0));
        }
        else if (m_manager.is_implies(n)) {
            count += count_at_labels_pos(a->get_arg(0));
            count += count_at_labels_neg(a->get_arg(1));
        }
        else if (m_manager.is_and(n)) {
            for (unsigned i = 0; i < sz; ++i) {
                count = std::max(count, count_at_labels_neg(a->get_arg(i)));
            }
        }

        if (count > 1 && m_first) {
            TRACE("for_each_relevant_expr", tout << mk_pp(n, m_manager) << "\n";);
            m_first = false;
        }

        return count;
    }


    unsigned check_at_labels::count_at_labels_pos(expr* n) {
        if (!is_app(n)) {
            return 0;
        }
        app* a = to_app(n);
        unsigned sz = a->get_num_args();
        unsigned count = count_at_labels_lit(n, true);
        if (m_manager.is_and(n)) {
            for (unsigned i = 0; i < sz; ++i) {
                count += count_at_labels_pos(a->get_arg(i));
            }       
        }
        else if (m_manager.is_not(n)) {
            count = count_at_labels_neg(a->get_arg(0));
        }
        else if (m_manager.is_implies(n)) {
            count = std::max(count, count_at_labels_neg(a->get_arg(0)));
            count = std::max(count, count_at_labels_pos(a->get_arg(1)));
        }
        else if (m_manager.is_or(n)) {
            for (unsigned i = 0; i < sz; ++i) {
                count = std::max(count, count_at_labels_pos(a->get_arg(i)));
            }
        }

        if (count > 1 && m_first) {
            TRACE("for_each_relevant_expr", tout << mk_pp(n, m_manager) << "\n";);
            m_first = false;
        }

        return count;
    }

    for_each_relevant_expr::for_each_relevant_expr(context & ctx):
        m_manager(ctx.get_manager()),
        m_context(ctx) {
    }

    void for_each_relevant_expr::operator()(expr * n) {
        TRACE("for_each_relevant_expr", tout << "#" << n->get_id() << "\n";);
    }

    void for_each_relevant_expr::reset() {
        m_todo.reset();
        m_cache.reset();
    }

    inline bool for_each_relevant_expr::is_relevant(expr * n) {        
        return m_context.is_relevant(n);
    }

    inline lbool for_each_relevant_expr::get_assignment(expr * n) {
        if (!m_context.lit_internalized(n))
            return l_true; // assume it is a top-level label
        return m_context.get_assignment(n);
    }
    
    void for_each_relevant_expr::process(expr * n) {
        TRACE("for_each_relevant_expr", tout << "processing:\n" << mk_bounded_pp(n, m_manager) << "\n";);
        TRACE("for_each_relevant_expr", tout << "processing:\n" << mk_pp(n, m_manager) << "\n";);
        if (m_cache.contains(n))
            return;
        m_todo.reset();
        m_todo.push_back(n);
        while (!m_todo.empty()) {
            expr * curr = m_todo.back();
            m_todo.pop_back();
            SASSERT(is_relevant(curr));
            if (m_cache.contains(curr))
                continue;
            operator()(curr);
            m_cache.insert(curr);
            if (!is_app(curr))
                continue;
            if (to_app(curr)->get_family_id() == m_manager.get_basic_family_id()) {
                switch (to_app(curr)->get_decl_kind()) {
                case OP_OR:
                    process_or(to_app(curr));
                    break;
                case OP_AND:
                    process_and(to_app(curr));
                    break;
                case OP_ITE:
                    process_ite(to_app(curr));
                    break;
                default:
                    process_app(to_app(curr));
                }
            }
            else {
                process_app(to_app(curr));
            }
        }
    }


    void for_each_relevant_expr::process_app(app * n) {
        unsigned sz = n->get_num_args();
        for (unsigned i = 0; i < sz; i++) {
            expr * arg = n->get_arg(i);
            if (m_cache.contains(arg))
                continue;
            SASSERT(is_relevant(arg));
            m_todo.push_back(arg);
        }
    }

    /**
       \brief Add a relevant child of n (that is assigned to val) to m_todo.

       \remark Give preference to a child that is already in the cache.
    */
    void for_each_relevant_expr::process_relevant_child(app * n, lbool val) {
        unsigned sz = n->get_num_args();
        TRACE("for_each_relevant_expr", tout << val << " " << mk_bounded_pp(n, m_manager) << "\n";);
        for (unsigned i = 0; i < sz; i++) {
            expr * arg = n->get_arg(i);
            if (!is_relevant(arg))
                continue;
            if (get_assignment(arg) != val)
                continue;
            if (m_cache.contains(arg)) {
                TRACE("for_each_relevant_expr", tout << "justified by: " << mk_bounded_pp(arg, m_manager) << "\n";);
                return; // the current child justifies n.
            }
        }
        for (unsigned i = 0; i < sz; i++) {
            expr * arg = n->get_arg(i);
            if (!is_relevant(arg))
                continue;
            if (get_assignment(arg) != val)
                continue;

            TRACE("for_each_relevant_expr", tout << "to_process: " << mk_bounded_pp(arg, m_manager) << "\n";);

            m_todo.push_back(arg);
            return;
        }
        UNREACHABLE();
    }

    void for_each_relevant_expr::process_and(app * n) {
        switch (get_assignment(n)) {
        case l_undef:
            UNREACHABLE();
            break;
        case l_false:
            process_relevant_child(n, l_false);
            break;
        case l_true:
            process_app(n);
            break;
        }
    }

    void for_each_relevant_expr::process_or(app * n) {
        switch (get_assignment(n)) {
        case l_undef:
            UNREACHABLE();
            break;
        case l_false:
            process_app(n);
            break;
        case l_true:
            process_relevant_child(n, l_true);
            break;
        }
    }

    void for_each_relevant_expr::process_ite(app * n) {
        if (!m_cache.contains(n->get_arg(0)))
            m_todo.push_back(n->get_arg(0));
        switch (get_assignment(n->get_arg(0))) {
        case l_false:
            if (!m_cache.contains(n->get_arg(2)))
                m_todo.push_back(n->get_arg(2));
            break;
        case l_undef:
            UNREACHABLE();
            break;
        case l_true:
            if (!m_cache.contains(n->get_arg(1)))
                m_todo.push_back(n->get_arg(1));
            break;
        }
    }


    void collect_relevant_label_lits::operator()(expr * n) {
        TRACE("for_each_relevant_expr", 
              tout << "label: " << m_manager.is_label_lit(n) << " " << " " << get_assignment(n) 
              << " " << mk_bounded_pp(n, m_manager) << "\n";);
        if (!m_manager.is_label_lit(n))
            return;
        if (get_assignment(n) != l_true)
            return;
        m_manager.is_label_lit(n, m_buffer); // copy symbols to buffer
    }

    void collect_relevant_labels::operator()(expr * n) {
        bool pos;
        TRACE("for_each_relevant_expr", 
              tout << "label: " << m_manager.is_label(n) << " " << get_assignment(n) 
              << " " << mk_bounded_pp(n, m_manager) << "\n";);
        if (!m_manager.is_label(n, pos))
            return;
        if (pos && (get_assignment(n) != l_true)) 
            return;
        if (!pos && (get_assignment(n) != l_false)) 
            return;
        m_manager.is_label(n, pos, m_buffer); // copy symbols to buffer
    }

};
