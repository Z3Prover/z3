# Copyright (c) Microsoft Corporation 2015
"""
Tactic documentation generator script
"""

import os
import re

SCRIPT_DIR = os.path.abspath(os.path.dirname(__file__))
OUTPUT_DIRECTORY = os.path.join(os.getcwd(), 'api')

def doc_path(path):
    return os.path.join(SCRIPT_DIR, path)

is_doc = re.compile("Tactic Documentation")
is_doc_end = re.compile("\-\-\*\/")

def generate_tactic_doc(ous, f, ins):
    for line in ins:
        if is_doc_end.search(line):
            break
        ous.write(line)

def extract_tactic_doc(ous, f):
    with open(f) as ins:
        for line in ins:
            if is_doc.search(line):
                generate_tactic_doc(ous, f, ins)

def help(ous):
    ous.write("---\n")
    ous.write("title: Tactics Summary\n")
    ous.write("sidebar_position: 5\n")
    ous.write("---\n")
    for root, dirs, files in os.walk(doc_path("../src")):
        for f in files:
            if f.endswith("tactic.h"):
                extract_tactic_doc(ous, os.path.join(root, f))

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

mk_dir(os.path.join(OUTPUT_DIRECTORY, 'md'))

with open(OUTPUT_DIRECTORY + "/md/tactics-summary.md",'w') as ous:
    help(ous)
