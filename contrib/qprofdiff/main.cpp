/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    main.cpp

Abstract:

    Main file for qprofdiff.

Author:

    Christoph M. Wintersteiger (cwinter)

Revision History:
--*/
#include<errno.h>
#include<limits.h>

#include<string>
#include<iostream>
#include<fstream>
#include<map>
#include<vector>
#include<set>
#include<algorithm>

using namespace std;

set<string> options;

// Profile format:
// [quantifier_instances] qname : num_instances : max_generation : max_cost_s
const string prefix = "[quantifier_instances]";
unsigned prefix_len = prefix.length();
typedef struct { unsigned num_instances, max_generation, max_cost; } map_entry;

string trim(string str) {
    size_t linx = str.find_first_not_of(' ');
    size_t rinx = str.find_last_not_of(' ');
    return str.substr(linx, rinx-linx+1);
}

int parse(string const & filename, map<string, map_entry> & data) {
    ifstream fs(filename.c_str());

    if (!fs.is_open()) {
        cout << "Can't open file '" << filename << "'" << endl;
        return ENOENT;
    }

    string qid;
    string tokens[4];
    unsigned cur_token = 0;

    while (!fs.eof()) {
        string line;
        getline(fs, line);

        if (line.substr(0, prefix_len) == prefix) {
            line = trim(line.substr(prefix_len));
            size_t from = 0, ti = 0;
            for (size_t inx = line.find(':', from);
                inx != string::npos;
                inx = line.find(':', from)) {
                tokens[ti] = trim(line.substr(from, inx-from));
                from = inx+1;
                ti++;
            }
            if (from != line.length() && ti < 4)
                tokens[ti] = trim(line.substr(from));

            qid = tokens[0];

            if (data.find(qid) == data.end()) {
                map_entry & entry = data[qid];
                entry.num_instances = entry.max_generation = entry.max_cost = 0;
            }

            map_entry & entry = data[qid];
            entry.num_instances = atoi(tokens[1].c_str());
            entry.max_generation = (unsigned)atoi(tokens[2].c_str());
            entry.max_cost = (unsigned)atoi(tokens[3].c_str());
        }
    }

    fs.close();

    return 0;
}

void display_data(map<string, map_entry> & data) {
    for (map<string, map_entry>::iterator it = data.begin();
         it != data.end();
         it++)
        cout << it->first << ": " << it->second.num_instances <<
                             ", " << it->second.max_generation <<
                             ", " << it->second.max_cost << endl;
}


typedef struct {
    int d_num_instances, d_max_generation, d_max_cost;
    bool left_only, right_only;
} diff_entry;

typedef struct { string qid; diff_entry e; } diff_item;

#define DIFF_LT(X) bool diff_item_lt_ ## X (diff_item const & l, diff_item const & r) { \
    int l_lt_r = l.e.d_ ## X < r.e.d_ ## X; \
    int l_eq_r = l.e.d_ ## X == r.e.d_ ## X; \
    return \
        l.e.left_only ? (r.e.left_only ? ((l_eq_r) ? l.qid < r.qid : l_lt_r) : false) : \
        l.e.right_only ? (r.e.right_only ? ((l_eq_r) ? l.qid < r.qid : l_lt_r) : true) : \
        r.e.right_only ? false : \
        r.e.left_only ? true : \
        l_lt_r; \
}

DIFF_LT(num_instances)
DIFF_LT(max_generation)
DIFF_LT(max_cost)

int indicate(diff_entry const & e, bool suppress_unchanged) {
    if (e.left_only) {
        cout << "< ";
        return INT_MIN;
    }
    else if (e.right_only) {
        cout << "> ";
        return INT_MAX;
    }
    else {
        int const & delta =
            (options.find("-si") != options.end()) ? e.d_num_instances :
            (options.find("-sg") != options.end()) ? e.d_max_generation :
            (options.find("-sc") != options.end()) ? e.d_max_cost :
            e.d_num_instances;

        if (delta < 0)
            cout << "+ ";
        else if (delta > 0)
            cout << "- ";
        else if (delta == 0 && !suppress_unchanged)
            cout << "= ";

        return delta;
    }
}

void diff(map<string, map_entry> & left, map<string, map_entry> & right) {
    map<string, diff_entry> diff_data;

    for (map<string, map_entry>::const_iterator lit = left.begin();
        lit != left.end();
        lit++) {
        string const & qid = lit->first;
        map_entry const & lentry = lit->second;

        map<string, map_entry>::const_iterator rit = right.find(qid);
        if (rit != right.end()) {
            map_entry const & rentry = rit->second;
            diff_entry & de = diff_data[qid];

            de.left_only = de.right_only = false;
            de.d_num_instances = lentry.num_instances - rentry.num_instances;
            de.d_max_generation = lentry.max_generation - rentry.max_generation;
            de.d_max_cost = lentry.max_cost - rentry.max_cost;
        }
        else {
            diff_entry & de = diff_data[qid];
            de.left_only = true;
            de.right_only = false;
            de.d_num_instances = lentry.num_instances;
            de.d_max_generation = lentry.max_generation;
            de.d_max_cost = lentry.max_cost;
        }
    }

    for (map<string, map_entry>::const_iterator rit = right.begin();
        rit != right.end();
        rit++) {
        string const & qid = rit->first;
        map_entry const & rentry = rit->second;

        map<string, map_entry>::const_iterator lit = left.find(qid);
        if (lit == left.end()) {
            diff_entry & de = diff_data[qid];
            de.left_only = false;
            de.right_only = true;
            de.d_num_instances = -(int)rentry.num_instances;
            de.d_max_generation = -(int)rentry.max_generation;
            de.d_max_cost = -(int)rentry.max_cost;
        }
    }

    vector<diff_item> flat_data;
    for (map<string, diff_entry>::const_iterator it = diff_data.begin();
        it != diff_data.end();
        it++) {
        flat_data.push_back(diff_item());
        flat_data.back().qid = it->first;
        flat_data.back().e = it->second;
    }

    stable_sort(flat_data.begin(), flat_data.end(),
        options.find("-si") != options.end() ? diff_item_lt_num_instances:
        options.find("-sg") != options.end() ? diff_item_lt_max_generation :
        options.find("-sc") != options.end() ? diff_item_lt_max_cost :
        diff_item_lt_num_instances);

    bool suppress_unchanged = options.find("-n") != options.end();

    for (vector<diff_item>::const_iterator it = flat_data.begin();
        it != flat_data.end();
        it++) {
        diff_item const & d = *it;
        string const & qid = d.qid;
        diff_entry const & e = d.e;

        int delta = indicate(e, suppress_unchanged);

        if (!(delta == 0 && suppress_unchanged))
            cout << qid << " (" <<
                (e.d_num_instances > 0 ? "" : "+") << -e.d_num_instances << " inst., " <<
                (e.d_max_generation > 0 ? "" : "+") << -e.d_max_generation << " max. gen., " <<
                (e.d_max_cost > 0 ? "" : "+") << -e.d_max_cost << " max. cost)" <<
                endl;
    }
}

void display_usage() {
    cout << "Usage: qprofdiff [options] <filename> <filename>" << endl;
    cout << "Options:" << endl;
    cout << " -n      Suppress unchanged items" << endl;
    cout << " -si     Sort by difference in number of instances" << endl;
    cout << " -sg     Sort by difference in max. generation" << endl;
    cout << " -sc     Sort by difference in max. cost" << endl;
}

int main(int argc, char ** argv) {
    char * filename1 = 0;
    char * filename2 = 0;

    for (int i = 1; i < argc; i++) {
        int len = string(argv[i]).length();
        if (len > 1 && argv[i][0] == '-') {
            options.insert(string(argv[i]));
        }
        else if (filename1 == 0)
            filename1 = argv[i];
        else if (filename2 == 0)
            filename2 = argv[i];
        else {
            cout << "Invalid argument: " << argv[i] << endl << endl;
            display_usage();
            return EINVAL;
        }
    }

    if (filename1 == 0 || filename2 == 0) {
        cout << "Two filenames required." << endl << endl;
        display_usage();
        return EINVAL;
    }


    cout << "Comparing " << filename1 << " to " << filename2 << endl;

    map<string, map_entry> data1, data2;

    int r = parse(filename1, data1);
    if (r != 0) return r;
    r = parse(filename2, data2);
    if (r != 0) return r;

    // display_data(data1);
    // display_data(data2);

    diff(data1, data2);

    return 0;
}
