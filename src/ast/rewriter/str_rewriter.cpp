/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    str_rewriter.cpp

Abstract:

    AST rewriting rules for string terms.

Author:

    Murphy Berzish

Notes:

--*/

#if 0

#include"str_rewriter.h"
#include"arith_decl_plugin.h"
#include"ast_pp.h"
#include"ast_util.h"
#include"well_sorted.h"
#include<map>
#include<set>
#include<deque>
#include<cctype>

// Convert a regular expression to an e-NFA using Thompson's construction
void nfa::convert_re(expr * e, unsigned & start, unsigned & end, str_util & m_strutil) {
    start = next_id();
    end = next_id();
    if (m_strutil.is_re_Str2Reg(e)) {
        app * a = to_app(e);
        expr * arg_str = a->get_arg(0);
        if (m_strutil.is_string(arg_str)) {
            std::string str = m_strutil.get_string_constant_value(arg_str);
            TRACE("t_str_rw", tout << "build NFA for '" << str << "'" << std::endl;);

            /*
             * For an n-character string, we make (n-1) intermediate states,
             * labelled i_(0) through i_(n-2).
             * Then we construct the following transitions:
             * start --str[0]--> i_(0) --str[1]--> i_(1) --...--> i_(n-2) --str[n-1]--> final
             */
            unsigned last = start;
            for (int i = 0; i <= ((int)str.length()) - 2; ++i) {
                unsigned i_state = next_id();
                make_transition(last, str.at(i), i_state);
                TRACE("t_str_rw", tout << "string transition " << last << "--" << str.at(i) << "--> " << i_state << std::endl;);
                last = i_state;
            }
            make_transition(last, str.at(str.length() - 1), end);
            TRACE("t_str_rw", tout << "string transition " << last << "--" << str.at(str.length() - 1) << "--> " << end << std::endl;);
            TRACE("t_str_rw", tout << "string NFA: start = " << start << ", end = " << end << std::endl;);
        } else {
            TRACE("t_str_rw", tout << "invalid string constant in Str2Reg" << std::endl;);
            m_valid = false;
            return;
        }
    } else if (m_strutil.is_re_RegexConcat(e)){
        app * a = to_app(e);
        expr * re1 = a->get_arg(0);
        expr * re2 = a->get_arg(1);
        unsigned start1, end1;
        convert_re(re1, start1, end1, m_strutil);
        unsigned start2, end2;
        convert_re(re2, start2, end2, m_strutil);
        // start --e--> start1 --...--> end1 --e--> start2 --...--> end2 --e--> end
        make_epsilon_move(start, start1);
        make_epsilon_move(end1, start2);
        make_epsilon_move(end2, end);
        TRACE("t_str_rw", tout << "concat NFA: start = " << start << ", end = " << end << std::endl;);
    } else if (m_strutil.is_re_RegexUnion(e)) {
        app * a = to_app(e);
        expr * re1 = a->get_arg(0);
        expr * re2 = a->get_arg(1);
        unsigned start1, end1;
        convert_re(re1, start1, end1, m_strutil);
        unsigned start2, end2;
        convert_re(re2, start2, end2, m_strutil);

        // start --e--> start1 ; start --e--> start2
        // end1 --e--> end ; end2 --e--> end
        make_epsilon_move(start, start1);
        make_epsilon_move(start, start2);
        make_epsilon_move(end1, end);
        make_epsilon_move(end2, end);
        TRACE("t_str_rw", tout << "union NFA: start = " << start << ", end = " << end << std::endl;);
    } else if (m_strutil.is_re_RegexStar(e)) {
        app * a = to_app(e);
        expr * subex = a->get_arg(0);
        unsigned start_subex, end_subex;
        convert_re(subex, start_subex, end_subex, m_strutil);
        // start --e--> start_subex, start --e--> end
        // end_subex --e--> start_subex, end_subex --e--> end
        make_epsilon_move(start, start_subex);
        make_epsilon_move(start, end);
        make_epsilon_move(end_subex, start_subex);
        make_epsilon_move(end_subex, end);
        TRACE("t_str_rw", tout << "star NFA: start = " << start << ", end = " << end << std::endl;);
    } else {
        TRACE("t_str_rw", tout << "invalid regular expression" << std::endl;);
        m_valid = false;
        return;
    }
}

void nfa::epsilon_closure(unsigned start, std::set<unsigned> & closure) {
    std::deque<unsigned> worklist;
    closure.insert(start);
    worklist.push_back(start);

    while(!worklist.empty()) {
        unsigned state = worklist.front();
        worklist.pop_front();
        if (epsilon_map.find(state) != epsilon_map.end()) {
            for (std::set<unsigned>::iterator it = epsilon_map[state].begin();
                    it != epsilon_map[state].end(); ++it) {
                unsigned new_state = *it;
                if (closure.find(new_state) == closure.end()) {
                    closure.insert(new_state);
                    worklist.push_back(new_state);
                }
            }
        }
    }
}

bool nfa::matches(std::string input) {
    /*
     * Keep a set of all states the NFA can currently be in.
     * Initially this is the e-closure of m_start_state
     * For each character A in the input string,
     * the set of next states contains
     * all states in transition_map[S][A] for each S in current_states,
     * and all states in epsilon_map[S] for each S in current_states.
     * After consuming the entire input string,
     * the match is successful iff current_states contains m_end_state.
     */
    std::set<unsigned> current_states;
    epsilon_closure(m_start_state, current_states);
    for (unsigned i = 0; i < input.length(); ++i) {
        char A = input.at(i);
        std::set<unsigned> next_states;
        for (std::set<unsigned>::iterator it = current_states.begin();
                it != current_states.end(); ++it) {
            unsigned S = *it;
            // check transition_map
            if (transition_map[S].find(A) != transition_map[S].end()) {
                next_states.insert(transition_map[S][A]);
            }
        }

        // take e-closure over next_states to compute the actual next_states
        std::set<unsigned> epsilon_next_states;
        for (std::set<unsigned>::iterator it = next_states.begin(); it != next_states.end(); ++it) {
            unsigned S = *it;
            std::set<unsigned> closure;
            epsilon_closure(S, closure);
            epsilon_next_states.insert(closure.begin(), closure.end());
        }
        current_states = epsilon_next_states;
    }
    if (current_states.find(m_end_state) != current_states.end()) {
        return true;
    } else {
        return false;
    }
}


br_status str_rewriter::mk_str_Concat(expr * arg0, expr * arg1, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Concat " << mk_pp(arg0, m()) << " " << mk_pp(arg1, m()) << ")" << std::endl;);
    if(m_strutil.is_string(arg0) && m_strutil.is_string(arg1)) {
        TRACE("t_str_rw", tout << "evaluating concat of two constant strings" << std::endl;);
        std::string arg0Str = m_strutil.get_string_constant_value(arg0);
        std::string arg1Str = m_strutil.get_string_constant_value(arg1);
        std::string resultStr = arg0Str + arg1Str;
        result = m_strutil.mk_string(resultStr);
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Length(expr * arg0, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Length " << mk_pp(arg0, m()) << ")" << std::endl;);
    if (m_strutil.is_string(arg0)) {
        TRACE("t_str_rw", tout << "evaluating length of constant string" << std::endl;);
        std::string arg0Str = m_strutil.get_string_constant_value(arg0);
        rational arg0Len((unsigned)arg0Str.length());
        result = m_autil.mk_numeral(arg0Len, true);
        TRACE("t_str_rw", tout << "result is " << mk_pp(result, m()) << std::endl;);
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_CharAt(expr * arg0, expr * arg1, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (CharAt " << mk_pp(arg0, m()) << " " << mk_pp(arg1, m()) << ")" << std::endl;);
    // if arg0 is a string constant and arg1 is an integer constant,
    // we can rewrite this by evaluating the expression
    rational arg1Int;
    if (m_strutil.is_string(arg0) && m_autil.is_numeral(arg1, arg1Int)) {
        TRACE("t_str_rw", tout << "evaluating constant CharAt expression" << std::endl;);
        std::string arg0Str = m_strutil.get_string_constant_value(arg0);
        std::string resultStr;
        if (arg1Int >= rational(0) && arg1Int <= rational((unsigned)arg0Str.length())) {
            resultStr = arg0Str.at(arg1Int.get_unsigned());
            TRACE("t_str_rw", tout << "result is '" << resultStr << "'" << std::endl;);
        } else {
            resultStr = "";
            TRACE("t_str_rw", tout << "bogus length argument, result is empty string" << std::endl;);
        }
        result = m_strutil.mk_string(resultStr);
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_StartsWith(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (StartsWith " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant StartsWith predicate" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.length() < needleStr.length()) {
            result = m().mk_false();
            return BR_DONE;
        } else {
            if (haystackStr.substr(0, needleStr.length()) == needleStr) {
                result = m().mk_true();
            } else {
                result = m().mk_false();
            }
            return BR_DONE;
        }
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_EndsWith(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (EndsWith " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant EndsWith predicate" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.length() < needleStr.length()) {
            result = m().mk_false();
            return BR_DONE;
        } else {
            if (haystackStr.substr(haystackStr.length() - needleStr.length(), needleStr.length()) == needleStr) {
                result = m().mk_true();
            } else {
                result = m().mk_false();
            }
            return BR_DONE;
        }
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Contains(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Contains " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (haystack == needle) {
        TRACE("t_str_rw", tout << "eliminate (Contains) over identical terms" << std::endl;);
        result = m().mk_true();
        return BR_DONE;
    } else if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant Contains predicate" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.find(needleStr) != std::string::npos) {
            result = m().mk_true();
        } else {
            result = m().mk_false();
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Indexof(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Indexof " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant Indexof expression" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.find(needleStr) != std::string::npos) {
            int index = haystackStr.find(needleStr);
            result = m_autil.mk_numeral(rational(index), true);
        } else {
            result = m_autil.mk_numeral(rational(-1), true);
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Indexof2(expr * arg0, expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Indexof2 " << mk_pp(arg0, m()) << " " << mk_pp(arg1, m()) << " " << mk_pp(arg2, m()) << ")" << std::endl;);
    //if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr && getNodeType(t, args[2]) == my_Z3_Num) {
    rational arg2Int;
    if (m_strutil.is_string(arg0) && m_strutil.is_string(arg1) && m_autil.is_numeral(arg2, arg2Int)) {
        TRACE("t_str_rw", tout << "evaluating constant Indexof2 expression" << std::endl;);
        std::string arg0str = m_strutil.get_string_constant_value(arg0);
        std::string arg1str = m_strutil.get_string_constant_value(arg1);
        if (arg2Int >= rational((unsigned)arg0str.length())) {
            result = m_autil.mk_numeral(rational(-1), true);
        } else if (arg2Int < rational(0)) {
            int index = arg0str.find(arg1str);
            result = m_autil.mk_numeral(rational(index), true);
        } else {
            std::string suffixStr = arg0str.substr(arg2Int.get_unsigned(), arg0str.length() - arg2Int.get_unsigned());
            if (suffixStr.find(arg1str) != std::string::npos) {
                int index = suffixStr.find(arg1str) + arg2Int.get_unsigned();
                result = m_autil.mk_numeral(rational(index), true);
            } else {
                result = m_autil.mk_numeral(rational(-1), true);
            }
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_LastIndexof(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (LastIndexof " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant LastIndexof expression" << std::endl;);
        std::string arg0Str = m_strutil.get_string_constant_value(haystack);
        std::string arg1Str = m_strutil.get_string_constant_value(needle);
        if (arg0Str.rfind(arg1Str) != std::string::npos) {
            int index = arg0Str.rfind(arg1Str);
            result = m_autil.mk_numeral(rational(index), true);
        } else {
            result = m_autil.mk_numeral(rational(-1), true);
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Replace(expr * base, expr * source, expr * target, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Replace " << mk_pp(base, m()) << " " << mk_pp(source, m()) << " " << mk_pp(target, m()) << ")" << std::endl;);
    if (m_strutil.is_string(base) && m_strutil.is_string(source) && m_strutil.is_string(target)) {
        std::string arg0Str = m_strutil.get_string_constant_value(base);
        std::string arg1Str = m_strutil.get_string_constant_value(source);
        std::string arg2Str = m_strutil.get_string_constant_value(target);
        if (arg0Str.find(arg1Str) != std::string::npos) {
            int index1 = arg0Str.find(arg1Str);
            int index2 = index1 + arg1Str.length();
            std::string substr0 = arg0Str.substr(0, index1);
            std::string substr2 = arg0Str.substr(index2);
            std::string replaced = substr0 + arg2Str + substr2;
            result = m_strutil.mk_string(replaced);
        } else {
            result = base;
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_prefixof(expr * pre, expr * full, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (str.prefixof " << mk_pp(pre, m()) << " " << mk_pp(full, m()) << ")" << std::endl;);
    result = m_strutil.mk_str_StartsWith(full, pre);
    return BR_REWRITE_FULL;
}

br_status str_rewriter::mk_str_suffixof(expr * post, expr * full, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (str.suffixof" << mk_pp(post, m()) << " " << mk_pp(full, m()) << ")" << std::endl;);
    result = m_strutil.mk_str_EndsWith(full, post);
    return BR_REWRITE_FULL;
}

br_status str_rewriter::mk_str_to_int(expr * arg0, expr_ref & result) {
	TRACE("t_str_rw", tout << "rewrite (str.to-int " << mk_pp(arg0, m()) << ")" << std::endl;);

	if (m_strutil.is_string(arg0)) {
		std::string str = m_strutil.get_string_constant_value(arg0);
		if (str.length() == 0) {
			result = m_autil.mk_numeral(rational::zero(), true);
			return BR_DONE;
		}

		// interpret str as a natural number and rewrite to the corresponding integer.
		// if this is not valid, rewrite to -1
		rational convertedRepresentation(0);
		rational ten(10);
		for (unsigned i = 0; i < str.length(); ++i) {
			char digit = str.at(i);
			if (isdigit((int)digit)) {
				std::string sDigit(1, digit);
				int val = atoi(sDigit.c_str());
				convertedRepresentation = (ten * convertedRepresentation) + rational(val);
			} else {
				// not a digit, invalid
				TRACE("t_str_rw", tout << "str.to-int argument contains non-digit character '" << digit << "'" << std::endl;);
				convertedRepresentation = rational::minus_one();
				break;
			}
		}
		result = m_autil.mk_numeral(convertedRepresentation, true);
		return BR_DONE;
	}
	return BR_FAILED;

}

br_status str_rewriter::mk_str_from_int(expr * arg0, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (str.from-int " << mk_pp(arg0, m()) << ")" << std::endl;);
    rational arg0Int;
    if (m_autil.is_numeral(arg0, arg0Int)) {
        // (str.from-int N) with N non-negative is the corresponding string in decimal notation.
        // otherwise it is the empty string
        if (arg0Int.is_nonneg()) {
            std::string str = arg0Int.to_string();
            result = m_strutil.mk_string(str);
            TRACE("t_str_rw", tout << "convert non-negative integer constant to " << str << std::endl;);
        } else {
            result = m_strutil.mk_string("");
            TRACE("t_str_rw", tout << "convert invalid integer constant to empty string" << std::endl;);
        }
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status str_rewriter::mk_str_Substr(expr * base, expr * start, expr * len, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Substr " << mk_pp(base, m()) << " " << mk_pp(start, m()) << " " << mk_pp(len, m()) << ")" << std::endl;);

    bool constant_base = m_strutil.is_string(base);
    std::string baseStr;
    if (constant_base) {
        baseStr = m_strutil.get_string_constant_value(base);
    }
    rational startVal;
    bool constant_start = m_autil.is_numeral(start, startVal);
    rational lenVal;
    bool constant_len = m_autil.is_numeral(len, lenVal);

    // case 1: start < 0 or len < 0
    if ( (constant_start && startVal.is_neg()) || (constant_len && lenVal.is_neg()) ) {
        TRACE("t_str_rw", tout << "start/len of substr is negative" << std::endl;);
        result = m_strutil.mk_string("");
        return BR_DONE;
    }
    // case 1.1: start >= length(base)
    if (constant_start && constant_base) {
        rational baseStrlen((unsigned int)baseStr.length());
        if (startVal >= baseStrlen) {
            TRACE("t_str_rw", tout << "start >= strlen for substr" << std::endl;);
            result = m_strutil.mk_string("");
            return BR_DONE;
        }
    }

    if (constant_base && constant_start && constant_len) {
        rational baseStrlen((unsigned int)baseStr.length());
        std::string retval;
        if (startVal + lenVal >= baseStrlen) {
            // case 2: pos+len goes past the end of the string
            retval = baseStr.substr(startVal.get_unsigned(), std::string::npos);
        } else {
            // case 3: pos+len still within string
            retval = baseStr.substr(startVal.get_unsigned(), lenVal.get_unsigned());
        }
        result = m_strutil.mk_string(retval);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status str_rewriter::mk_re_Str2Reg(expr * str, expr_ref & result) {
	// the argument to Str2Reg *must* be a string constant
	ENSURE(m_strutil.is_string(str));
	return BR_FAILED;
}

br_status str_rewriter::mk_re_RegexIn(expr * str, expr * re, expr_ref & result) {
	// fast path:
	// (RegexIn E (Str2Reg S)) --> (= E S)
	if (m_strutil.is_re_Str2Reg(re)) {
		expr * regexStr = to_app(re)->get_arg(0);
		ENSURE(m_strutil.is_string(regexStr));
		result = m().mk_eq(str, regexStr);
		TRACE("t_str_rw", tout << "RegexIn fast path: " << mk_pp(str, m()) << " in " << mk_pp(re, m()) << " ==> " << mk_pp(result, m()) << std::endl;);
		return BR_REWRITE_FULL;
	}

	// necessary for model validation
	if (m_strutil.is_string(str)) {
	    TRACE("t_str_rw", tout << "RegexIn with constant string argument" << std::endl;);
	    nfa regex_nfa(m_strutil, re);
	    ENSURE(regex_nfa.is_valid());
	    std::string input = m_strutil.get_string_constant_value(str);
	    if (regex_nfa.matches(input)) {
	        result = m().mk_true();
	    } else {
	        result = m().mk_false();
	    }
	    return BR_DONE;
	}

	return BR_FAILED;
}

br_status str_rewriter::mk_re_RegexStar(expr * re, expr_ref & result) {
    if (m_strutil.is_re_RegexStar(re)) {
        result = re;
        return BR_REWRITE_FULL;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_re_RegexConcat(expr * r0, expr * r1, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (RegexConcat " << mk_pp(r0, m()) << " " << mk_pp(r1, m()) << ")" << std::endl;);
    // (RegexConcat (Str2Reg "A") (Str2Reg "B")) --> (Str2Reg "AB")
    if (m_strutil.is_re_Str2Reg(r0) && m_strutil.is_re_Str2Reg(r1)) {
        expr * r0str = to_app(r0)->get_arg(0);
        expr * r1str = to_app(r1)->get_arg(0);
        ENSURE(m_strutil.is_string(r0str));
        ENSURE(m_strutil.is_string(r1str));
        std::string r0val = m_strutil.get_string_constant_value(r0str);
        std::string r1val = m_strutil.get_string_constant_value(r1str);
        std::string simplifyVal = r0val + r1val;
        TRACE("t_str_rw", tout << "RegexConcat fast path: both sides are Str2Reg, simplify to (Str2Reg \"" << simplifyVal << "\")" << std::endl;);
        result = m_strutil.mk_re_Str2Reg(simplifyVal);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status str_rewriter::mk_re_RegexPlus(expr * re, expr_ref & result) {
    /*
     * Two optimizations are possible if we inspect 're'.
     * If 're' is (RegexPlus X), then reduce to 're'.
     * If 're' is (RegexStar X), then reduce to 're'.
     * Otherwise, reduce to (RegexConcat re (RegexStar re)).
     */

    if (m_strutil.is_re_RegexPlus(re)) {
        result = re;
        return BR_REWRITE_FULL;
    } else if (m_strutil.is_re_RegexStar(re)) {
        // Z3str2 re-created the AST under 're' here, but I don't think we need to do that
        result = re;
        return BR_REWRITE_FULL;
    } else {
        result = m_strutil.mk_re_RegexConcat(re, m_strutil.mk_re_RegexStar(re));
        return BR_REWRITE_FULL;
    }
}

br_status str_rewriter::mk_re_RegexCharRange(expr * start, expr * end, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (RegexCharRange " << mk_pp(start, m()) << " " << mk_pp(end, m()) << ")" << std::endl;);
    // both 'start' and 'end' must be string constants
    ENSURE(m_strutil.is_string(start) && m_strutil.is_string(end));
    std::string arg0Value = m_strutil.get_string_constant_value(start);
    std::string arg1Value = m_strutil.get_string_constant_value(end);
    ENSURE(arg0Value.length() == 1 && arg1Value.length() == 1);
    char low = arg0Value[0];
    char high = arg1Value[0];
    if (low > high) {
      char t = low;
      low = high;
      high = t;
    }

    char c = low;
    std::string cStr;
    cStr.push_back(c);
    expr * res = m_strutil.mk_re_Str2Reg(cStr);
    c++;
    for (; c <= high; c++) {
      cStr.clear();
      cStr.push_back(c);
      res = m_strutil.mk_re_RegexUnion(res, m_strutil.mk_re_Str2Reg(cStr));
    }
    result = res;
    return BR_DONE;
}

br_status str_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());

    TRACE("t_str_rw", tout << "rewrite app: " << f->get_name() << std::endl;);

    switch(f->get_decl_kind()) {
    case OP_STRCAT:
        SASSERT(num_args == 2);
        return mk_str_Concat(args[0], args[1], result);
    case OP_STRLEN:
        SASSERT(num_args == 1);
        return mk_str_Length(args[0], result);
    case OP_STR_CHARAT:
        SASSERT(num_args == 2);
        return mk_str_CharAt(args[0], args[1], result);
    case OP_STR_STARTSWITH:
        SASSERT(num_args == 2);
        return mk_str_StartsWith(args[0], args[1], result);
    case OP_STR_ENDSWITH:
        SASSERT(num_args == 2);
        return mk_str_EndsWith(args[0], args[1], result);
    case OP_STR_CONTAINS:
        SASSERT(num_args == 2);
        return mk_str_Contains(args[0], args[1], result);
    case OP_STR_INDEXOF:
        SASSERT(num_args == 2);
        return mk_str_Indexof(args[0], args[1], result);
    case OP_STR_INDEXOF2:
        SASSERT(num_args == 3);
        return mk_str_Indexof2(args[0], args[1], args[2], result);
    case OP_STR_LASTINDEXOF:
        SASSERT(num_args == 2);
        return mk_str_LastIndexof(args[0], args[1], result);
    case OP_STR_REPLACE:
        SASSERT(num_args == 3);
        return mk_str_Replace(args[0], args[1], args[2], result);
    case OP_STR_PREFIXOF:
        SASSERT(num_args == 2);
        return mk_str_prefixof(args[0], args[1], result);
    case OP_STR_SUFFIXOF:
        SASSERT(num_args == 2);
        return mk_str_suffixof(args[0], args[1], result);
    case OP_STR_STR2INT:
    	SASSERT(num_args == 1);
    	return mk_str_to_int(args[0], result);
    case OP_STR_INT2STR:
        SASSERT(num_args == 1);
        return mk_str_from_int(args[0], result);
    case OP_STR_SUBSTR:
        SASSERT(num_args == 3);
        return mk_str_Substr(args[0], args[1], args[2], result);
    case OP_RE_STR2REGEX:
    	SASSERT(num_args == 1);
    	return mk_re_Str2Reg(args[0], result);
    case OP_RE_REGEXIN:
    	SASSERT(num_args == 2);
    	return mk_re_RegexIn(args[0], args[1], result);
    case OP_RE_REGEXPLUS:
        SASSERT(num_args == 1);
        return mk_re_RegexPlus(args[0], result);
    case OP_RE_REGEXSTAR:
        SASSERT(num_args == 1);
        return mk_re_RegexStar(args[0], result);
    case OP_RE_REGEXCONCAT:
        SASSERT(num_args == 2);
        return mk_re_RegexConcat(args[0], args[1], result);
    case OP_RE_REGEXCHARRANGE:
        SASSERT(num_args == 2);
        return mk_re_RegexCharRange(args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_eq_core(expr * l, expr * r, expr_ref & result) {
    // from seq_rewriter
    expr_ref_vector lhs(m()), rhs(m()), res(m());
    bool changed = false;
    if (!reduce_eq(l, r, lhs, rhs, changed)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (!changed) {
        return BR_FAILED;
    }
    for (unsigned i = 0; i < lhs.size(); ++i) {
        res.push_back(m().mk_eq(lhs[i].get(), rhs[i].get()));
    }
    result = mk_and(res);
    return BR_REWRITE3;
}

bool str_rewriter::reduce_eq(expr * l, expr * r, expr_ref_vector & lhs, expr_ref_vector & rhs, bool & change) {
    change = false;
    return true;
}

bool str_rewriter::reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_vector& lhs, expr_ref_vector& rhs, bool& change) {
    change = false;
    return true;
}

#endif /* disable */
