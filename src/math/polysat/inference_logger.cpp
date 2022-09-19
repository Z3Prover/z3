/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat inference logging

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

--*/

#include "math/polysat/inference_logger.h"
#include "math/polysat/solver.h"
#include "math/polysat/log.h"
#include "math/polysat/log_helper.h"
#include <fstream>


namespace polysat {

    file_inference_logger::file_inference_logger(solver& s)
        : s(s) {
    }

    std::ostream& file_inference_logger::out() {
        SASSERT(m_out);
        return *m_out;
    }

    std::ostream& file_inference_logger::out_indent() {
        return out() << "    ";
    }

    std::string file_inference_logger::hline() const {
        return std::string(70, '-');
    }

    void file_inference_logger::begin_conflict(char const* text) {
        ++m_num_conflicts;
        if (text)
            LOG("Begin CONFLICT #" << m_num_conflicts << " (" << text << ")");
        else
            LOG("Begin CONFLICT #" << m_num_conflicts);
        m_used_constraints.reset();
        m_used_vars.reset();
        if (!m_out)
            m_out = alloc(std::ofstream, "conflicts.txt");
        else
            out() << "\n\n\n\n\n\n\n\n\n\n\n\n";
        out() << "CONFLICT #" << m_num_conflicts;
        if (text)
            out() << " (" << text << ")";
        out() << "\n";
        // log initial conflict state
        out() << hline() << "\n";
        log_conflict_state();
    }

    void file_inference_logger::log_conflict_state() {
        out() << "TODO";
        /* TODO: update for new conflict
        conflict2 const& core = s.m_conflict2;
        for (auto const& c : core) {
            out_indent() << c.blit() << ": " << c << '\n';
            m_used_constraints.insert(c.blit().index());
            for (pvar v : c->vars())
                m_used_vars.insert(v);
        }
        for (auto v : core.vars()) {
            out_indent() << assignment_pp(core.s, v, core.s.get_value(v)) << "\n";
            m_used_vars.insert(v);
        }
        for (auto v : core.bail_vars()) {
            out_indent() << assignment_pp(core.s, v, core.s.get_value(v)) << " (bail)\n";
            m_used_vars.insert(v);
        }
        if (core.is_bailout())
            out_indent() << "(bailout)\n";
        */
        out().flush();
    }

    void file_inference_logger::log(inference const& inf) {
        out() << hline() << "\n";
        out() << inf << "\n";
        log_conflict_state();
    }

    void file_inference_logger::log_var(pvar v) {
        m_used_vars.insert(v);
    }

    void file_inference_logger::log_lemma(clause_builder const& cb) {
        out() << hline() << "\nLemma:";
        for (auto const& lit : cb)
            out() << " " << lit;
        out() << "\n";
        for (auto const& lit : cb)
            out_indent() << lit_pp(s, lit) << "\n";
            // out_indent() << lit << ": " << s.lit2cnstr(lit) << "\n";
        out().flush();
    }

    void file_inference_logger::end_conflict() {
        // search_state const& search, viable const& v
        out() << "\n" << hline() << "\n\n";
        out() << "Search state (part):\n";
        for (auto const& item : s.m_search)
            if (is_relevant(item))
                out_indent() << search_item_pp(s.m_search, item, true) << "\n";
        out() << hline() << "\nViable (part):\n";
        for (pvar v : m_used_vars)
            out_indent() << "v" << std::setw(3) << std::left << v << ": " << viable::var_pp(s.m_viable, v) << "\n";
        out().flush();
        LOG("End CONFLICT #" << m_num_conflicts);
    }

    bool file_inference_logger::is_relevant(search_item const& item) const {
        switch (item.kind()) {
        case search_item_k::assignment:
            return m_used_vars.contains(item.var());
        case search_item_k::boolean:
            return m_used_constraints.contains(item.lit().index());
        }
        UNREACHABLE();
        return false;
    }

}
