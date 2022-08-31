#include "ast/expr_functors.h"
#include "muz/spacer/spacer_context.h"

using namespace spacer;

namespace {

class contains_array_op_proc : public i_expr_pred {
    ast_manager &m;
    family_id m_array_fid;

  public:
    contains_array_op_proc(ast_manager &manager)
        : m(manager), m_array_fid(array_util(m).get_family_id()) {}
    bool operator()(expr *e) override {
        return is_app(e) && to_app(e)->get_family_id() == m_array_fid;
    }
};

class lemma_inductive_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned weaken_success;
        unsigned weaken_fail;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            count = 0;
            weaken_success = 0;
            weaken_fail = 0;
            watch.reset();
        }
    };

    ast_manager &m;
    expr_ref m_true;
    stats m_st;
    bool m_only_array_eligible;
    bool m_enable_litweak;

    contains_array_op_proc m_contains_array_op;
    check_pred m_contains_array_pred;

    expr_ref_vector m_pinned;
    lemma *m_lemma = nullptr;
    spacer::pred_transformer *m_pt = nullptr;
    unsigned m_weakness = 0;
    unsigned m_level = 0;
    ptr_vector<expr> m_cube;

    // temporary vector
    expr_ref_vector m_core;

  public:
    lemma_inductive_generalizer(spacer::context &ctx,
                                bool only_array_eligible = false,
                                bool enable_literal_weakening = true)
        : lemma_generalizer(ctx), m(ctx.get_ast_manager()),
          m_true(m.mk_true(), m), m_only_array_eligible(only_array_eligible),
          m_enable_litweak(enable_literal_weakening), m_contains_array_op(m),
          m_contains_array_pred(m_contains_array_op, m),

          m_pinned(m), m_core(m) {}

  private:
    // -- true if literal \p lit is eligible to be generalized
    bool is_eligible(expr *lit) {
        return !m_only_array_eligible || has_arrays(lit);
    }

    bool has_arrays(expr *lit) { return m_contains_array_op(lit); }

    void reset() {
        m_cube.reset();
        m_weakness = 0;
        m_level = 0;
        m_pt = nullptr;
        m_pinned.reset();
        m_core.reset();
    }

    void setup(lemma_ref &lemma) {
        // check that we start in uninitialized state
        SASSERT(m_pt == nullptr);
        m_lemma = lemma.get();
        m_pt = &lemma->get_pob()->pt();
        m_weakness = lemma->weakness();
        m_level = lemma->level();
        auto &cube = lemma->get_cube();
        m_cube.reset();
        for (auto *lit : cube) { m_cube.push_back(lit); }
    }

    // loads current generalization from m_cube to m_core
    void load_cube_to_core() {
        m_core.reset();
        for (unsigned i = 0, sz = m_cube.size(); i < sz; ++i) {
            auto *lit = m_cube.get(i);
            if (lit == m_true) continue;
            m_core.push_back(lit);
        }
    }

    // returns true if m_cube is inductive
    bool is_cube_inductive() {
        load_cube_to_core();
        if (m_core.empty()) return false;

        unsigned used_level;
        if (m_pt->check_inductive(m_level, m_core, used_level, m_weakness)) {
            m_level = std::max(m_level, used_level);
            return true;
        }
        return false;
    }

    // intersect m_cube with m_core
    unsigned update_cube_by_core(unsigned from = 0) {
        // generalize away all literals in m_cube that are not in m_core
        // do not assume anything about order of literals in m_core

        unsigned success = 0;
        // mark core
        ast_fast_mark2 marked_core;
        for (auto *v : m_core) { marked_core.mark(v); }

        // replace unmarked literals by m_true in m_cube
        for (unsigned i = from, sz = m_cube.size(); i < sz; ++i) {
            auto *lit = m_cube.get(i);
            if (lit == m_true) continue;
            if (!marked_core.is_marked(lit)) {
                m_cube[i] = m_true;
                success++;
            }
        }
        return success;
    }
    // generalizes m_core and removes from m_cube all generalized literals
    unsigned generalize_core(unsigned from = 0) {
        unsigned success = 0;
        unsigned used_level;

        // -- while it is possible that a single literal can be generalized to
        // false,
        // -- it is fairly unlikely. Thus, we give up generalizing in this case.
        if (m_core.empty()) return 0;

        // -- check whether candidate in m_core is inductive
        if (m_pt->check_inductive(m_level, m_core, used_level, m_weakness)) {
            success += update_cube_by_core(from);
            // update m_level to the largest level at which the the current
            // candidate in m_cube is inductive
            m_level = std::max(m_level, used_level);
        }

        return success;
    }

    // generalizes (i.e., drops) a specific literal of m_cube
    unsigned generalize1(unsigned lit_idx) {

        if (!is_eligible(m_cube.get(lit_idx))) return 0;

        // -- populate m_core with all literals except the one being generalized
        m_core.reset();
        for (unsigned i = 0, sz = m_cube.size(); i < sz; ++i) {
            auto *lit = m_cube.get(i);
            if (lit == m_true || i == lit_idx) continue;
            m_core.push_back(lit);
        }

        return generalize_core(lit_idx);
    }

    // generalizes all literals of m_cube in a given range
    unsigned generalize_range(unsigned from, unsigned to) {
        unsigned success = 0;
        for (unsigned i = from; i < to; ++i) { success += generalize1(i); }
        return success;
    }

    // weakens a given literal of m_cube
    // weakening replaces a literal by a weaker literal(s)
    // for example, x=y might get weakened into one of x<=y or y<=x
    unsigned weaken1(unsigned lit_idx) {
        if (!is_eligible(m_cube.get(lit_idx))) return 0;
        if (m_cube.get(lit_idx) == m_true) return 0;

        unsigned success = 0;
        unsigned cube_sz = m_cube.size();

        // -- save literal to be generalized, and replace it by true
        expr *saved_lit = m_cube.get(lit_idx);
        m_cube[lit_idx] = m_true;

        // -- add new weaker literals to end of m_cube and attempt to generalize
        expr_ref_vector weakening(m);
        weakening.push_back(saved_lit);
        expand_literals(m, weakening);
        if (weakening.get(0) != saved_lit) {
            for (auto *lit : weakening) {
                m_cube.push_back(lit);
                m_pinned.push_back(lit);
            }

            if (m_cube.size() - cube_sz >= 2) {
                // normal case: generalize new weakening
                success += generalize_range(cube_sz, m_cube.size());
            } else {
                // special case -- weaken literal by another literal, check that
                // cube is still inductive
                success += (is_cube_inductive() ? 1 : 0);
            }
        }

        // -- failed to generalize, restore removed literal and m_cube
        if (success == 0) {
            m_cube[lit_idx] = saved_lit;
            m_cube.shrink(cube_sz);
            m_st.weaken_fail++;
        } else {
            m_st.weaken_success++;
        }

        return success;
    }

    // weakens literals of m_cube in a given range
    unsigned weaken_range(unsigned from, unsigned to) {
        unsigned success = 0;
        for (unsigned i = from; i < to; ++i) { success += weaken1(i); }
        return success;
    }

  public:
    // entry point for generalization
    void operator()(lemma_ref &lemma) override {
        if (lemma->get_cube().empty()) return;

        m_st.count++;
        scoped_watch _w_(m_st.watch);

        setup(lemma);

        unsigned num_gens = 0;

        // -- first round -- generalize by dropping literals
        num_gens += generalize_range(0, m_cube.size());

        // -- if weakening is enabled, start next round
        if (m_enable_litweak) {
            unsigned cube_sz = m_cube.size();
            // -- second round -- weaken literals that cannot be dropped
            num_gens += weaken_range(0, cube_sz);

            // -- third round -- weaken literals produced in prev round
            if (cube_sz < m_cube.size())
                num_gens += weaken_range(cube_sz, m_cube.size());
        }

        // if there is at least one generalization, update lemma
        if (num_gens > 0) {
            TRACE("indgen",
                  tout << "Generalized " << num_gens << " literals\n";);

            // reuse m_core since it is not needed for anything else
            m_core.reset();
            for (auto *lit : m_cube) {
                if (lit != m_true) m_core.push_back(lit);
            }

            TRACE("indgen", tout << "Original: " << lemma->get_cube() << "\n"
                                 << "Generalized: " << m_core << "\n";);

            lemma->update_cube(lemma->get_pob(), m_core);
            lemma->set_level(m_level);
        }

        reset();

        return;
    }

    void collect_statistics(statistics &st) const override {
        st.update("time.spacer.solve.reach.gen.ind", m_st.watch.get_seconds());
        st.update("SPACER inductive gen", m_st.count);
        st.update("SPACER inductive gen weaken success", m_st.weaken_success);
        st.update("SPACER inductive gen weaken fail", m_st.weaken_fail);
    }
    void reset_statistics() override { m_st.reset(); }
};
} // namespace

namespace spacer {
lemma_generalizer *
alloc_lemma_inductive_generalizer(spacer::context &ctx,
                                  bool only_array_eligible,
                                  bool enable_literal_weakening) {
    return alloc(lemma_inductive_generalizer, ctx, only_array_eligible,
                 enable_literal_weakening);
}

} // namespace spacer
