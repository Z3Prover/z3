/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat inference logging

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

    Log derivations during conflict resolution for easier debugging

--*/
#pragma once
#include "math/polysat/constraint.h"
#include "util/util.h"
#include <ostream>

namespace polysat {

    class clause_builder;
    class search_item;
    class solver;

    class displayable {
    public:
        virtual ~displayable() {}
        virtual std::ostream& display(std::ostream& out) const = 0;
    };

    inline std::ostream& operator<<(std::ostream& out, displayable const& d) { return d.display(out); }

    class display_c_str : public displayable {
        char const* m_str;
    public:
        display_c_str(char const* str) : m_str(str) { }
        std::ostream& display(std::ostream& out) const override {
            if (m_str)
                out << m_str;
            return out;
        }
    };

    class inference : public displayable { };

    class inference_named : public inference {
        char const* m_name;
    public:
        inference_named(char const* name) : m_name(name) { SASSERT(name); }
        std::ostream& display(std::ostream& out) const override { return out << m_name; }
    };

    class inference_logger {
    public:
        virtual ~inference_logger() {}

        /// Begin next conflict
        void begin_conflict(char const* text = nullptr) { begin_conflict(display_c_str(text)); }
        virtual void begin_conflict(displayable const& header) = 0;
        /// Log inference and the current state.
        virtual void log(inference const& inf) = 0;
        virtual void log(char const* name) { log(inference_named(name)); }
        virtual void log_var(pvar v) = 0;
        /// Log relevant part of search state and viable.
        /// Call end_conflict before backjumping in the solver.
        virtual void end_conflict() = 0;

        /// Log current conflict state (implicitly done by log_inference)
        virtual void log_conflict_state() = 0;

        virtual void log_lemma(clause_builder const& cb) = 0;
    };

    class dummy_inference_logger : public inference_logger {
    public:
        virtual void begin_conflict(displayable const& header) override {}
        virtual void log(inference const& inf) override {}
        virtual void log_var(pvar v) override {}
        virtual void end_conflict() override {}
        virtual void log_conflict_state() override {}
        virtual void log_lemma(clause_builder const& cb) override {}
    };

    class file_inference_logger : public inference_logger {
        solver& s;
        uint_set m_used_constraints;
        uint_set m_used_vars;
        scoped_ptr<std::ostream> m_out = nullptr;
        unsigned m_num_conflicts = 0;

        std::ostream& out();
        std::ostream& out_indent();
        std::string hline() const;

        bool is_relevant(search_item const& item) const;

    public:
        file_inference_logger(solver& s);
        void begin_conflict(displayable const& header) override;
        void log(inference const& inf) override;
        void log_var(pvar v) override;
        void end_conflict() override;
        void log_conflict_state() override;
        void log_lemma(clause_builder const& cb) override;
    };

}
