/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#include <unordered_map>
#include <vector>
#include <string>
#include <set>
#include <iostream>

namespace lp {
class argument_parser {
    std::unordered_map<std::string, std::string> m_options;
    std::unordered_map<std::string, std::string> m_options_with_after_string;
    std::set<std::string> m_used_options;
    std::unordered_map<std::string, std::string> m_used_options_with_after_string;
    std::vector<std::string> m_free_args;
    std::vector<std::string> m_args;

public:
    std::string m_error_message;
    argument_parser(unsigned argn, char * const* args) {
        for (unsigned i = 0; i < argn; i++) {
            m_args.push_back(std::string(args[i]));
        }
    }

    void add_option(std::string s) {
        add_option_with_help_string(s, "");
    }

    void add_option_with_help_string(std::string s, std::string help_string) {
        m_options[s]=help_string;
    }

    void add_option_with_after_string(std::string s) {
        add_option_with_after_string_with_help(s, "");
    }

    void add_option_with_after_string_with_help(std::string s, std::string help_string) {
        m_options_with_after_string[s]=help_string;
    }


    bool parse() {
        bool status_is_ok = true;
        for (unsigned i = 0; i < m_args.size(); i++) {
            std::string ar = m_args[i];
            if (m_options.find(ar) != m_options.end() )
                m_used_options.insert(ar);
            else if (m_options_with_after_string.find(ar) != m_options_with_after_string.end()) {
                if (i == m_args.size() - 1) {
                    m_error_message = "Argument is missing after "+ar;
                    return false;
                }
                i++;
                m_used_options_with_after_string[ar] = m_args[i];
            } else {
                 if (starts_with(ar, "-") || starts_with(ar, "//")) 
                     status_is_ok = false;

                m_free_args.push_back(ar);
            }
        }
        return status_is_ok;
    }

    bool contains(std::unordered_map<std::string, std::string> & m, std::string s) {
        return m.find(s) != m.end();
    }

    bool contains(std::set<std::string> & m, std::string s) {
        return m.find(s) != m.end();
    }

    bool option_is_used(std::string option) {
        return contains(m_used_options, option) || contains(m_used_options_with_after_string, option);
    }

    std::string get_option_value(std::string option) {
        auto t = m_used_options_with_after_string.find(option);
        if (t != m_used_options_with_after_string.end()){
            return t->second;
        }
        return std::string();
    }

    bool starts_with(std::string s, char const * prefix) {
        return starts_with(s, std::string(prefix));
    }

    bool starts_with(std::string s, std::string prefix) {
        return s.substr(0, prefix.size()) == prefix;
    }

    std::string usage_string() {
        std::string ret = "";
        std::vector<std::string> unknown_options;
        for (const auto & t : m_free_args) {
            if (starts_with(t, "-") || starts_with(t, "\\")) {
                unknown_options.push_back(t);
            }
        }
        if (unknown_options.size()) {
            ret = "Unknown options:";
        }
        for (const auto & unknownOption : unknown_options) {
            ret += unknownOption;
            ret += ",";
        }
        ret += "\n";
        ret += "Usage:\n";
        for (auto allowed_option : m_options)
            ret += allowed_option.first + " " + (allowed_option.second.size() == 0 ? std::string("") : std::string("/") + allowed_option.second) + std::string("\n");
        for (auto s : m_options_with_after_string) {
            ret += s.first + " " + (s.second.size() == 0? " \"option value\"":("\""+ s.second+"\"")) + "\n";
        }
        return ret;
    }

    void print() {
        if (m_used_options.size() == 0 && m_used_options_with_after_string.size() == 0 && m_free_args.size() == 0) {
            std::cout << "no options are given" << std::endl;
            return;
        }
        std::cout << "options are: " << std::endl;
        for (const std::string & s : m_used_options) {
            std::cout << s << std::endl;
        }
        for (auto & t : m_used_options_with_after_string) {
            std::cout << t.first << " " << t.second << std::endl;
        }
        if (m_free_args.size() > 0) {
            std::cout << "free arguments are: "  << std::endl;
            for (auto & t : m_free_args) {
                std::cout << t << " " <<  std::endl;
            }
        }
    }
};
}
