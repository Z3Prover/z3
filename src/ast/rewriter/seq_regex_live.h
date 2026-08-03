/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_live.h

Abstract:

    Shared lazy live-state traversal for regular-expression derivatives.

--*/
#pragma once

#include "ast/rewriter/seq_derive.h"
#include "ast/ast.h"

class seq_rewriter;

namespace seq {

    class live_states {
        struct search;
        struct imp;

    public:
        enum class failure {
            none,
            state_cap,
            resource
        };

        class iterator {
            live_states* m_owner = nullptr;
            search* m_search = nullptr;
            unsigned m_index = 0;
            bool m_end = false;

        public:
            iterator(live_states* owner, search* s, unsigned index, bool end) :
                m_owner(owner), m_search(s), m_index(index), m_end(end) {}
            expr* operator*() const;
            iterator& operator++();
            bool operator!=(iterator const& other) const;
        };

        class reachable {
            live_states* m_owner = nullptr;
            search* m_search = nullptr;

        public:
            reachable(live_states* owner, search* s) :
                m_owner(owner), m_search(s) {}
            iterator begin() const;
            iterator end() const;
            bool failed() const;
            failure failure_reason() const;
            bool is_dead();
        };

    private:
        imp* m_imp;

        bool ensure(search* s, unsigned index);
        expr* get_live(search* s, unsigned index) const;
        failure get_failure(search* s) const;

    public:
        live_states(seq_rewriter& rw,
                    transition_mode mode = transition_mode::brzozowski_tm,
                    unsigned max_states = UINT_MAX);
        ~live_states();
        live_states(live_states const&) = delete;
        live_states& operator=(live_states const&) = delete;

        reachable reachable_live(expr* r);
        bool contains(expr* r) const;
        unsigned state_id(expr* r);
        void reset();
    };
}
