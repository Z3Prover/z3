# Copyright (c) Microsoft Corporation 2015
"""
Tactic documentation generator script
"""

import os
import re
import sys
import subprocess

BUILD_DIR='../build'
SCRIPT_DIR = os.path.abspath(os.path.dirname(__file__))
OUTPUT_DIRECTORY = os.path.join(os.getcwd(), 'api')

def doc_path(path):
    return os.path.join(SCRIPT_DIR, path)

is_doc = re.compile("Tactic Documentation")
is_doc_end = re.compile("\-\-\*\/")
is_tac_name = re.compile("## Tactic (.*)")
is_simplifier = re.compile("ADD_SIMPLIFIER\(.*\"([^\"]*)\".*,.*\"([^\"]*)\".*,.*\"([^\"]*)\"\.*\)")

def is_ws(s):
    return all([0 for ch in s if ch != ' ' and ch != '\n'])

def extract_params(ous, tac):
    z3_exe = BUILD_DIR + "/z3"
    out = subprocess.Popen([z3_exe, f"-tacticsmd:{tac}"], stdout=subprocess.PIPE).communicate()[0]
    if not out:
        return
    out = out.decode(sys.getdefaultencoding())
    if is_ws(out):
        return
    ous.write("### Parameters\n\n")
    for line in out:
        ous.write(line.replace("\r",""))
    ous.write("\n")
    
def generate_tactic_doc(ous, f, ins):
    tac_name = None
    for line in ins:
        m = is_tac_name.search(line)
        if m:
            tac_name = m.group(1)
        if is_doc_end.search(line):
            if tac_name:
                extract_params(ous, tac_name)
            break
        ous.write(line)

def extract_tactic_doc(ous, f):
    with open(f) as ins:
        for line in ins:
            if is_doc.search(line):
                generate_tactic_doc(ous, f, ins)

def generate_simplifier_doc(ous, name, desc):
    ous.write("## Simplifier [" + name + "](https://microsoft.github.io/z3guide/docs/strategies/summary/#tactic-" + name + ")\n")
    ous.write("### Description\n" + desc + "\n")

              
def extract_simplifier_doc(ous, f):
    with open(f) as ins:
        for line in ins:
            m = is_simplifier.search(line)
            if m:
                generate_simplifier_doc(ous, m.group(1), m.group(2))

def find_tactic_name(path):
    with open(path) as ins:
        for line in ins:
            m = is_tac_name.search(line)
            if m:
                return m.group(1)
    print(f"no tactic in {path}")
    return ""

def find_simplifier_name(path):
    with open(path) as ins:
        for line in ins:
            m = is_simplifier.search(line)
            if m:
                return m.group(1)
    print(f"no simplifier in {path}")
    return ""

def presort_files(find_fn):
    tac_files = []
    for root, dirs, files in os.walk(doc_path("../src")):
        for f in files:
            if f.endswith("~"):
                continue
            if f.endswith("tactic.h") or "simplifiers" in root:
                tac_files += [(f, os.path.join(root, f))]
    tac_files = sorted(tac_files, key = lambda x: find_fn(x[1]))
    return tac_files
    
    
def help(ous):
    ous.write("---\n")
    ous.write("title: Tactics Summary\n")
    ous.write("sidebar_position: 6\n")
    ous.write("---\n")
    tac_files = presort_files(find_tactic_name)
    for file, path in tac_files:
        extract_tactic_doc(ous, path)



def help_simplifier(ous):
    ous.write("---\n")
    ous.write("title: Simplifiers Summary\n")
    ous.write("sidebar_position: 7\n")
    ous.write("---\n")
    tac_files = presort_files(find_simplifier_name)
    for file, path in tac_files:
        extract_simplifier_doc(ous, path)

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

mk_dir(os.path.join(OUTPUT_DIRECTORY, 'md'))

with open(OUTPUT_DIRECTORY + "/md/tactics-summary.md",'w') as ous:
    help(ous)

with open(OUTPUT_DIRECTORY + "/md/simplifier-summary.md",'w') as ous:
    help_simplifier(ous)
