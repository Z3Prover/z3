/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_ccc.cpp

Abstract:
   
    A variant of Concurrent Cube and Conquer

Author:

    Nikolaj Bjorner (nbjorner) 2017-4-17

Notes:

--*/

#include "sat_solver.h"
#include "sat_lookahead.h"
#include "sat_ccc.h"

using namespace sat;


std::ostream& ccc::decision::pp(std::ostream& out) const {
    return out << "(" << m_id << " " << m_last << " d:" << m_depth << ") ";
}

std::ostream& ccc::pp(std::ostream& out, svector<decision> const& v) {
    for (unsigned i = 0; i < v.size(); ++i) {
        v[i].pp(out);
    }
    return out;
}

lbool ccc::cube() {
    unsigned branch_id = 0;
    unsigned_vector id_trail;

    lookahead lh(s);
    lh.init_search();
    lh.m_model.reset();

    lookahead::scoped_level _sl(lh, lh.c_fixed_truth);
    literal_vector trail;
    svector<decision> decisions;
    lh.m_search_mode = lookahead_mode::searching;
    while (!m_cancel) {

        s.checkpoint();

        SASSERT(trail.size() <= decisions.size());
        while (trail.size() < decisions.size()) {
            check_non_model("lh inconsistent ", decisions);
            decisions.pop_back();
            id_trail.pop_back();
        }
        SASSERT(id_trail.size() == trail.size());
        SASSERT(id_trail.size() == decisions.size());

        TRACE("sat", lh.display(tout););

        if (lh.inconsistent()) {
            if (!lh.backtrack(trail)) return l_false;
            continue;
        }

        lh.inc_istamp();

        // check if CDCL solver got ahead.
        bool repeat = false;
        #pragma omp critical (ccc_solved)
        {
            if (!m_solved.empty()) {
                unsigned solved_id = m_solved.top();
                if (id_trail.contains(solved_id)) {
                    lh.set_conflict();
                }
                else {
                    m_solved.pop();
                }
                repeat = true;
            }
        }
        if (repeat) continue;


        literal l = lh.choose();
        if (lh.inconsistent()) {
            if (!lh.backtrack(trail)) return l_false;
            continue;
        }
        if (l == null_literal) {
            m_model = lh.get_model();
            return l_true;
        }

        // update trail and set of ids

        ++branch_id;
        ++lh.m_stats.m_decisions;
        unsigned parent_id = id_trail.empty() ? 0 : id_trail.back();
        decision d(branch_id, trail.size() + 1, l, parent_id);
        id_trail.push_back(branch_id);
        trail.push_back(l);
        decisions.push_back(d);
        SASSERT(id_trail.size() == trail.size());
        
        #pragma omp critical (ccc_log)                                  
        {                                                       
            IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(lh.m_prefix, lh.m_trail_lim.size()) << ": " << l << " " << lh.m_trail.size() << " " << trail << "\n";
                       pp(verbose_stream(), decisions) << "\n";
                       );
        }
        #pragma omp critical (ccc_decisions)
        {
            m_decisions.push(d);
        }
        TRACE("sat", tout << "choose: " << l << " " << trail << "\n";);
        lh.push(l, lh.c_fixed_truth);
        SASSERT(lh.inconsistent() || !lh.is_unsat());
    }
    return l_undef;
}

lbool ccc::conquer(solver& s) {
    try {
        if (s.inconsistent()) return l_false;
        s.init_search();
        s.propagate(false);
        if (s.inconsistent()) return l_false;
        s.cleanup();
        s.simplify_problem();
        if (s.inconsistent()) return l_false;

        svector<decision> decisions;
        
        while (true) {
            SASSERT(!s.inconsistent());
            
            lbool r = bounded_search(s, decisions);
            if (r != l_undef)
                return r;
                        
            s.restart();            
            s.simplify_problem();
            if (s.check_inconsistent()) return l_false;
            s.gc();     

        }
    }
    catch (solver::abort_solver) {
        return l_undef;
    }
}

void ccc::replay_decisions(solver& s, svector<decision>& decisions) {
    // replay decisions
    bool shortcut = false;
    s.propagate(true);
    for (unsigned i = s.scope_lvl(); !shortcut && !s.inconsistent() && i < decisions.size(); ++i) {
        decision d = decisions[i];
        literal lit = d.m_last;
        lbool val = s.value(lit);
        #pragma omp critical (ccc_log)                                  
        {                                                       
            IF_VERBOSE(1, verbose_stream() << "replay " << lit << " " << val << "\n";);
        }
        switch (val) {
        case l_false:
            #pragma omp critical (ccc_solved)
            {
                m_solved.push(d.m_id);
            }
            check_non_model("replay", decisions);
            decisions.resize(i);
            shortcut = true;
            break;
        case l_undef:
            s.push();
            s.assign(lit, justification());
            s.propagate(false);
            break;
        case l_true:
            s.push();
            break;                    
        }
    }
}

lbool ccc::bounded_search(solver& s, svector<decision>& decisions) {
    
    while (true) {
        s.checkpoint();
        bool done = false;
        while (!done) {
            replay_decisions(s, decisions);
            lbool is_sat = s.propagate_and_backjump_step(done); 
            if (is_sat != l_true) return is_sat;
        }

        s.gc();

        decision d;
        bool cube_decision = false;
        #pragma omp critical (ccc_decisions)
        {
            if (!m_decisions.empty()) {
                d = m_decisions.pop();
                cube_decision = true;
            }
        }

        if (cube_decision) {
            if (d.m_depth > 1 + decisions.size()) continue;
            while (!decisions.empty() && decisions.back().m_depth >= d.m_depth) {
                SASSERT(decisions.back().m_depth == decisions.size());
                check_non_model("cube decision", decisions);
                decisions.pop_back();
            }
            SASSERT(decisions.empty() || decisions.back().m_depth + 1 == d.m_depth);
            SASSERT(decisions.empty() || decisions.back().m_id == d.m_parent);
            decisions.push_back(d);
            s.pop_reinit(s.m_scope_lvl + 1 - d.m_depth); // TBD: check alignment of scopes
            literal lit = d.m_last;
            #pragma omp critical (ccc_log)                                  
            {                                                       
                IF_VERBOSE(1, pp(verbose_stream() << "push ", decisions) << " @ " << s.scope_lvl() << " " << s.value(lit) << "\n";
                           if (s.value(lit) == l_false) verbose_stream() << "level: " << s.lvl(lit) << "\n";);
            }
            switch (s.value(lit)) {
            case l_false:
                decisions.pop_back();
                #pragma omp critical (ccc_solved)
                {
                    m_solved.push(d.m_id);
                }
                break;
            case l_true:
            case l_undef:
                s.push();
                s.assign(lit, justification());
                break;
            }
        }
        else if (!s.decide()) {
            lbool is_sat = s.final_check();
            if (is_sat != l_undef) {
                return is_sat;
            }
        }
    }
}

void ccc::set_model() {
    push_model(1, false);
    push_model(2, false);
    push_model(3, false);
    push_model(4, false);
    push_model(5, false);
    push_model(6, false);
    push_model(7, false);
    push_model(8, false);
    push_model(9, true);
    push_model(10, true);
    push_model(11, true);
    push_model(12, true);
    push_model(13, true);
    push_model(14, true);
    push_model(15, true);
    push_model(16, true);
    push_model(17, true);
    push_model(18, true);
    push_model(19, true);
    push_model(20, true);
    push_model(21, true);
    push_model(22, true);
    push_model(23, true);
push_model(24, true);
push_model(25, true);
push_model(26, true);
push_model(27, true);
push_model(28, true);
push_model(29, true);
push_model(30, true);
push_model(31, true);
push_model(32, true);
push_model(33, true);
push_model(34, true);
push_model(35, true);
push_model(36, true);
push_model(37, true);
push_model(38, true);
push_model(39, true);
push_model(40, true);
push_model(41, false);
push_model(42, true);
push_model(43, true);
push_model(44, true);
push_model(45, true);
push_model(46, true);
push_model(47, true);
push_model(48, false);
push_model(49, true);
push_model(50, true);
push_model(51, true);
push_model(52, true);
push_model(53, true);
push_model(54, false);
push_model(55, true);
push_model(56, true);
push_model(57, true);
push_model(58, true);
push_model(59, true);
push_model(60, true);
push_model(61, true);
push_model(62, true);
push_model(63, true);
push_model(64, true);
push_model(65, true);
push_model(66, true);
push_model(67, true);
push_model(68, false);
push_model(69, true);
push_model(70, true);
push_model(71, false);
push_model(72, true);
push_model(73, true);
push_model(74, true);
push_model(75, true);
push_model(76, true);
push_model(77, true);
push_model(78, true);
push_model(79, true);
push_model(80, true);
push_model(81, true);
push_model(82, false);
push_model(83, true);
push_model(84, true);
push_model(85, true);
push_model(86, true);
push_model(87, true);
push_model(88, true);
push_model(89, true);
push_model(90, true);
push_model(91, false);
push_model(92, true);
push_model(93, true);
push_model(94, true);
push_model(95, true);
push_model(96, true);
push_model(97, true);
push_model(98, true);
push_model(99, false);
push_model(100, true);
push_model(101, true);
push_model(102, true);
push_model(103, true);
push_model(104, true);
push_model(105, true);
push_model(106, true);
push_model(107, true);
push_model(108, true);
push_model(109, true);
push_model(110, true);
push_model(111, true);
push_model(112, true);
push_model(113, false);
push_model(114, true);
push_model(115, true);
push_model(116, true);
push_model(117, true);
push_model(118, true);
push_model(119, true);
push_model(120, false);
push_model(121, true);
push_model(122, true);
push_model(123, true);
push_model(124, true);
push_model(125, true);
push_model(126, false);
push_model(127, true);
push_model(128, true);
push_model(129, true);
push_model(130, true);
push_model(131, true);
push_model(132, true);
push_model(133, true);
push_model(134, true);
push_model(135, true);
push_model(136, true);
push_model(137, true);
push_model(138, true);
push_model(139, false);
push_model(140, true);
push_model(141, true);
push_model(142, true);
push_model(143, false);
push_model(144, true);
push_model(145, true);
push_model(146, true);
push_model(147, true);
push_model(148, false);
push_model(149, true);
push_model(150, true);
push_model(151, true);
push_model(152, true);
push_model(153, true);
push_model(154, true);
push_model(155, true);
push_model(156, true);
push_model(157, true);
push_model(158, true);
push_model(159, true);
push_model(160, false);
push_model(161, true);
push_model(162, true);
push_model(163, true);
push_model(164, false);
push_model(165, true);
push_model(166, true);
push_model(167, true);
push_model(168, true);
push_model(169, true);
push_model(170, true);
push_model(171, true);
push_model(172, true);
push_model(173, true);
push_model(174, true);
push_model(175, true);
push_model(176, true);
push_model(177, true);
push_model(178, true);
push_model(179, true);
push_model(180, true);
push_model(181, true);
push_model(182, true);
push_model(183, true);
push_model(184, true);
push_model(185, false);
push_model(186, true);
push_model(187, true);
push_model(188, true);
push_model(189, true);
push_model(190, true);
push_model(191, true);
push_model(192, false);
push_model(193, true);
push_model(194, true);
push_model(195, true);
push_model(196, true);
push_model(197, true);
push_model(198, false);
push_model(199, true);
push_model(200, true);
push_model(201, true);
push_model(202, true);
push_model(203, true);
push_model(204, true);
push_model(205, true);
push_model(206, true);
push_model(207, true);
push_model(208, true);
push_model(209, true);
push_model(210, false);
push_model(211, false);
push_model(212, true);
push_model(213, true);
push_model(214, true);
push_model(215, true);
push_model(216, true);
push_model(217, true);
push_model(218, true);
push_model(219, true);
push_model(220, true);
push_model(221, true);
push_model(222, true);
push_model(223, true);
push_model(224, true);
push_model(225, false);
push_model(226, true);
push_model(227, true);
push_model(228, true);
push_model(229, true);
push_model(230, true);
push_model(231, false);
push_model(232, true);
push_model(233, true);
push_model(234, true);
push_model(235, false);
push_model(236, true);
push_model(237, true);
push_model(238, true);
push_model(239, true);
push_model(240, true);
push_model(241, true);
push_model(242, true);
push_model(243, true);
push_model(244, true);
push_model(245, true);
push_model(246, true);
push_model(247, true);
push_model(248, true);
push_model(249, false);
push_model(250, true);
push_model(251, true);
push_model(252, true);
push_model(253, true);
push_model(254, true);
push_model(255, true);
push_model(256, true);
push_model(257, true);
push_model(258, true);
push_model(259, true);
push_model(260, true);
push_model(261, true);
push_model(262, true);
push_model(263, false);
push_model(264, true);
push_model(265, true);
push_model(266, true);
push_model(267, true);
push_model(268, true);
push_model(269, false);
push_model(270, true);
push_model(271, true);
push_model(272, true);
push_model(273, false);
push_model(274, true);
push_model(275, true);
push_model(276, true);
push_model(277, true);
push_model(278, true);
push_model(279, true);
push_model(280, true);
push_model(281, true);
push_model(282, true);
push_model(283, true);
push_model(284, false);
push_model(285, true);
push_model(286, true);
push_model(287, true);
push_model(288, true);
push_model(289, true);
push_model(290, true);
push_model(291, true);
push_model(292, true);
push_model(293, true);
push_model(294, false);
push_model(295, true);
push_model(296, true);
push_model(297, true);
push_model(298, true);
push_model(299, true);
push_model(300, true);
push_model(301, false);
push_model(302, true);
push_model(303, true);
push_model(304, true);
push_model(305, false);
push_model(306, true);
push_model(307, true);
push_model(308, true);
push_model(309, true);
push_model(310, true);
push_model(311, true);
push_model(312, true);
push_model(313, true);
push_model(314, true);
push_model(315, true);
push_model(316, true);
push_model(317, true);
push_model(318, true);
push_model(319, false);
push_model(320, true);
push_model(321, true);
push_model(322, true);
push_model(323, true);
push_model(324, true);
push_model(325, true);
push_model(326, false);
push_model(327, true);
push_model(328, true);
push_model(329, true);
push_model(330, true);
push_model(331, true);
push_model(332, true);
push_model(333, true);
push_model(334, false);
push_model(335, true);
push_model(336, true);
push_model(337, true);
push_model(338, true);
push_model(339, true);
push_model(340, false);
push_model(341, true);
push_model(342, true);
push_model(343, true);
push_model(344, true);
push_model(345, true);
push_model(346, true);
push_model(347, true);
push_model(348, true);
push_model(349, true);
push_model(350, true);
push_model(351, true);
push_model(352, true);
push_model(353, false);
push_model(354, true);
push_model(355, true);
push_model(356, true);
push_model(357, true);
push_model(358, true);
push_model(359, true);
push_model(360, true);
push_model(361, true);
push_model(362, false);
push_model(363, false);
push_model(364, true);
push_model(365, true);
push_model(366, true);
push_model(367, true);
push_model(368, true);
push_model(369, true);
push_model(370, true);
push_model(371, true);
push_model(372, true);
push_model(373, true);
push_model(374, false);
push_model(375, true);
push_model(376, true);
push_model(377, true);
push_model(378, true);
push_model(379, true);
push_model(380, true);
push_model(381, true);
push_model(382, true);
push_model(383, true);
push_model(384, true);
push_model(385, true);
push_model(386, true);
push_model(387, true);
push_model(388, false);
push_model(389, true);
push_model(390, true);
push_model(391, true);
push_model(392, true);
push_model(393, true);
push_model(394, false);
push_model(395, true);
push_model(396, true);
push_model(397, true);
push_model(398, true);
push_model(399, true);
push_model(400, true);
push_model(401, false);
push_model(402, true);
push_model(403, true);
push_model(404, true);
push_model(405, true);
push_model(406, true);
push_model(407, true);
push_model(408, false);
push_model(409, true);
push_model(410, true);
push_model(411, true);
push_model(412, true);
push_model(413, true);
push_model(414, false);
push_model(415, true);
push_model(416, true);
push_model(417, true);
push_model(418, true);
push_model(419, true);
push_model(420, true);
push_model(421, true);
push_model(422, true);
push_model(423, true);
push_model(424, true);
push_model(425, true);
push_model(426, true);
push_model(427, true);
push_model(428, true);
push_model(429, false);
push_model(430, true);
push_model(431, false);
push_model(432, true);
push_model(433, true);
push_model(434, true);
push_model(435, true);
push_model(436, true);
push_model(437, true);
push_model(438, true);
push_model(439, true);
push_model(440, true);
push_model(441, true);
push_model(442, false);
push_model(443, true);
push_model(444, true);
push_model(445, true);
push_model(446, true);
push_model(447, true);
push_model(448, true);
push_model(449, true);
push_model(450, true);
push_model(451, true);
push_model(452, true);
push_model(453, false);
push_model(454, true);
push_model(455, true);
push_model(456, true);
push_model(457, true);
push_model(458, false);
push_model(459, true);
push_model(460, true);
push_model(461, true);
push_model(462, true);
push_model(463, true);
push_model(464, true);
push_model(465, true);
push_model(466, true);
push_model(467, false);
push_model(468, true);
push_model(469, true);
push_model(470, true);
push_model(471, true);
push_model(472, true);
push_model(473, true);
push_model(474, true);
push_model(475, true);
push_model(476, false);
push_model(477, true);
push_model(478, true);
push_model(479, true);
push_model(480, true);
push_model(481, true);
push_model(482, true);
push_model(483, true);
push_model(484, true);
push_model(485, false);
push_model(486, true);
push_model(487, true);
push_model(488, true);
push_model(489, true);
push_model(490, true);
push_model(491, true);
push_model(492, true);
push_model(493, true);
push_model(494, false);
push_model(495, true);
push_model(496, false);
push_model(497, true);
push_model(498, true);
push_model(499, true);
push_model(500, true);
push_model(501, true);
push_model(502, true);
push_model(503, true);
push_model(504, true);
push_model(505, false);
push_model(506, true);
push_model(507, true);
push_model(508, true);
push_model(509, true);
push_model(510, true);
push_model(511, true);
push_model(512, true);

}

void ccc::push_model(unsigned v, bool sign) {
    if (m_values.size() <= v) {
        m_values.resize(v + 1);
    }
    m_values[v] = sign;
}

void ccc::check_non_model(char const* fn, svector<decision> const& decisions) {
    for (unsigned i = 0; i < decisions.size(); ++i) {
        decision d = decisions[i];
        literal lit = d.m_last;
        if (m_values[lit.var()] != lit.sign()) return;
    }

    #pragma omp critical (ccc_log)                                  
    {                                                       
        pp(verbose_stream() << "backtracking from model " << fn << " ", decisions) << "\n";
    }
}

lbool ccc::search() {
    enum par_exception_kind {
        DEFAULT_EX,
        ERROR_EX
    };

    set_model();

    m_cancel = false;

    scoped_limits      scoped_rlimit(s.rlimit());
    vector<reslimit>   limits;
    ptr_vector<solver> solvers;
    int finished_id = -1;
    std::string        ex_msg;
    par_exception_kind ex_kind;
    unsigned error_code = 0;
    lbool result = l_undef;
    bool canceled = false;

    int num_threads = 2; // for ccc-infinity only two threads. s.m_config.m_num_threads + 1;
    for (int i = 1; i < num_threads; ++i) {
        limits.push_back(reslimit());
    }

    for (int i = 1; i < num_threads; ++i) {
        s.m_params.set_uint("random_seed", s.m_rand());
        solver* s1 = alloc(sat::solver, s.m_params, limits[i-1]);
        solvers.push_back(s1);
        s1->copy(s);
        scoped_rlimit.push_child(&s1->rlimit());            
    }

    #pragma omp parallel for
    for (int i = 0; i < num_threads; ++i) {
        try {                
            lbool r = l_undef;
            if (i == 0) {
                r = cube();
            }
            else {
                r = conquer(*solvers[i-1]);
            }
            bool first = false;
            #pragma omp critical (par_solver)
            {
                if (finished_id == -1) {
                    finished_id = i;
                    first = true;
                    result = r;
                }
            }
            if (first) {
                for (unsigned j = 0; j < solvers.size(); ++j) {
                    solvers[j]->rlimit().cancel();
                }
                // cancel lookahead solver:
                m_cancel = true;
            }
        }
        catch (z3_error & err) {
            error_code = err.error_code();
            ex_kind = ERROR_EX;                
        }
        catch (z3_exception & ex) {
            ex_msg = ex.msg();
            ex_kind = DEFAULT_EX;    
        }
    }

    if (finished_id > 0 && result == l_true) {
        // set model from auxiliary solver
        m_model = solvers[finished_id - 1]->get_model();
    }

    for (unsigned i = 0; i < solvers.size(); ++i) {            
        dealloc(solvers[i]);
    }
    
    if (finished_id == -1) {
        switch (ex_kind) {
        case ERROR_EX: throw z3_error(error_code);
        default: throw default_exception(ex_msg.c_str());
        }
    }

#if 0
    if (result == l_true) {
        for (unsigned i = 1; i < m_model.size(); ++i) {
            std::cout << "push_model(" << i << ", " << (m_model[i] > 0 ? "false" : "true") << ");\n";
        }
    }
#endif


    return result;
}

