############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Auxiliary scripts for generating Java bindings
# from the managed API.
#
# Author: Christoph M. Wintersteiger (cwinter)
############################################

CS="../dotnet/"
EXT=".cs"
EXCLUDE=["Enumerations.cs", "Native.cs", "AssemblyInfo.cs"]
OUTDIR="com/Microsoft/Z3/"

import os
import fileinput
import string
import re

def mk_java_bindings():
    print "Generating Java bindings (from C# bindings in " + CS + ")."
    for root, dirs, files in os.walk(CS):
        for fn in files:
            if not fn in EXCLUDE and fn.endswith(EXT):
                translate(fn)

def subst_getters(s, getters):
    for g in getters:
        s = s.replace(g, g + "()")

def type_replace(s):
    s = s.replace("bool", "boolean")
    s = s.replace("uint", "Integer")
    s = s.replace("string", "String")
    return s

def rename_native(s):
    a = re.sub("Native.Z3_(?P<id>\w+)", "Native.\g<id>", s)
    lc_callback = lambda pat: pat.group("id").upper()
    return re.sub("_(?P<id>\w)", lc_callback, a)


def translate(filename):
    tgtfn = OUTDIR + filename.replace(EXT, ".java")
    print "Translating " + filename + " to " + tgtfn
    tgt = open(tgtfn, "w")
    in_header = 0
    in_class = 0
    in_static_class = 0
    in_javadoc = 0
    lastindent = 0
    skip_brace = 0
    in_getter = ""
    in_getter_type = ""
    in_unsupported = 0
    getters = []
    for line in fileinput.input(os.path.join(CS, filename)):
        s = string.rstrip(string.lstrip(line))
        if in_javadoc:
            if s.startswith("///"):
                lastindent = line.find(s);
                if s.startswith("/// </summary>"):
                    pass
                else: 
                    a = line
                    a = a.replace("<c>", "<code>")
                    a = a.replace("</c>", "</code>")
                    a = a.replace("///"," *")
                    a = a.replace("<returns>","@return ")
                    a = a.replace("</returns>","")
                    tgt.write(a)
            else:
                t = ""
                for i in range(0, lastindent):
                    t += " "
                tgt.write(t + " **/\n")
                in_javadoc = 0

        if in_unsupported:
            if s == "}":
                in_unsupported = 0                
        elif not in_javadoc:
            if not in_header and s.find("/*++") != -1:
                in_header = 1
                tgt.write("/**\n")
            elif in_header and s.startswith("--*/"):
                in_header = 0
                tgt.write(" * This file was automatically generated from " + filename + " \n")
                tgt.write(" **/\n")
                tgt.write("\npackage com.Microsoft.Z3;\n")

            elif in_header == 1:
                # tgt.write(" * " + line.replace(filename, tgtfn))
                pass
            elif s.startswith("using"):
                if s.find("System.Diagnostics.Contracts") == -1:
                    tgt.write("/* " + s + " */\n")
            elif s.startswith("namespace"):
                pass
            elif s.startswith("public") and s.find("operator") and (s.find("==") != -1 or s.find("!=") != -1):
                t = ""
                for i in range(0, line.find(s)+1):
                    t += " "                    
                tgt.write(t + "/* Overloaded operators are not translated. */\n")
                in_unsupported = 1;
            elif s.startswith("public class") or s.startswith("internal class"):
                a = line.replace(":", "extends").replace("internal ", "")
                a = a.replace(", IComparable", "")
                tgt.write(a)
                in_class = 1
                in_static_class = 0
            elif s.startswith("public static class"):
                tgt.write(line.replace(":", "extends").replace("static", "final"))
                in_class = 1
                in_static_class = 1
            elif s.startswith("/// <summary>"):
                tgt.write(line.replace("/// <summary>", "/**"))
                in_javadoc = 1
            elif skip_brace and s == "{":
                skip_brace = 0
            elif s.find("public") != -1 and s.find("class") == -1 and s.find("event") == -1 and s.find("(") == -1:
                tokens = s.split(" ")
                print "# TOKENS: " + str(len(tokens))
                if len(tokens) == 3:
                    in_getter = tokens[2]
                    in_getter_type = type_replace((tokens[0] + " " + tokens[1]))
                    if in_static_class:
                        in_getter_type = in_getter_type.replace("static", "")                        
                    lastindent = line.find(s)
                    skip_brace = 1
                elif len(tokens) == 4:
                    in_getter = tokens[3]
                    in_getter_type = type_replace(tokens[0] + " " + tokens[1] + " " + tokens[2])
                    if in_static_class:
                        in_getter_type = in_getter_type.replace("static", "")
                    lastindent = line.find(s)
                    skip_brace = 1                
                else:
                    in_getter = tokens[2]
                    in_getter_type = type_replace(tokens[0] + " " + tokens[1])
                    if in_static_class:
                        in_getter_type = in_getter_type.replace("static", "")                        
                    rest = s[s.find("get ") + 4:-1]
                    subst_getters(rest, getters)
                    rest = type_replace(rest)
                    rest = rename_native(rest)
                    t = ""
                    for i in range(0, lastindent):
                        t += " "
                    tgt.write(t + in_getter_type + " " + in_getter + "() " + rest + "\n")
                getters.append(in_getter)
                print "ACC: " + s + " --> " + in_getter
            elif s.find("{ get {") != -1:
                line = type_replace(line)
                line = line.replace("internal ", "")
                d = line[0:line.find("{ get")]
                rest = line[line.find("{ get")+5:]
                rest = rest.replace("} }", "}")
                subst_getters(rest, getters)
                rest = rename_native(rest)
                tgt.write(d + "()" + rest)
                print "ACC: " + s + " --> " + in_getter
            elif in_getter != "" and s.startswith("get"):
                t = ""
                for i in range(0, lastindent):
                    t += " "
                if len(s) > 3: rest = s[3:]
                else: rest = ""
                subst_getters(rest, getters)
                rest = type_replace(rest)
                rest = rename_native(rest)
                tgt.write(t + in_getter_type + " " + in_getter + "() " + rest + "\n")
            elif in_getter != "" and s.startswith("set"):
                t = ""
                for i in range(0, lastindent):
                    t += " "
                if len(s) > 3: rest = type_replace(s[3:])
                else: rest = ""
                subst_getters(rest, getters)
                rest = rest.replace("(Integer)value", "Integer(value)")
                rest = type_replace(rest)
                rest = rename_native(rest)
                ac_acc = in_getter_type[:in_getter_type.find(' ')]
                ac_type = in_getter_type[in_getter_type.find(' ')+1:]
                tgt.write(t + ac_acc + " void set" + in_getter + "(" + ac_type + " value) " + rest + "\n")
            elif in_getter != "" and s == "}":
                in_getter = ""
                in_getter_type == ""
                skip_brace = 0
            elif s.startswith("uint ") and s.find("=") == -1:
                line = line.replace("uint", "Integer", line)
                line = re.sub("(?P<n>\w+)(?P<c>[,;])", "\g<n>\g<c>", line)
                tgt.write(line);
            elif (not in_class and (s.startswith("{") or s.startswith("}"))) or s.startswith("[") or s.startswith("#"):
                # print "Skipping: " + s;
                pass
            elif line == "}\n":
                pass
            else:
                # indent = line.find(s)
                if line.find(": base") != -1:
                    line = re.sub(": base\((?P<p>[\w,.\(\) ]*)\)", "{ super(\g<p>);", line)
                    if line.find("; {") != -1:
                        line = line.replace("; {", ";")
                    else:
                        skip_brace = 1                        
                if s.startswith("public"):
                    line = re.sub(" = [\w.]+(?P<d>[,;\)])", "\g<d>", line)
                    line = re.sub("(?P<d>[\(, ])params ", "\g<d>", line)
                line = line.replace("base.", "super.")
                a = type_replace(line)
                a = re.sub("Contract.\w+\([\s\S]*\);", "", a)
                a = rename_native(a)
                a = re.sub("~\w+\(\)", "protected void finalize()", a)
                a = re.sub("foreach\s*\((?P<t>[\w <>,]+)\s+(?P<i>\w+)\s+in\s+(?P<w>\w+)\)",
                           "for (\g<t>.Iterator \g<i> = \g<w>.iterator(); \g<i>.hasNext(); )", a)
                a = a.replace("readonly private", "private")
                a = a.replace("new public", "public")
                a = a.replace("ToString", "toString")
                a = a.replace("internal ", "")
                a = a.replace("override ", "")
                a = a.replace("virtual ", "")
                a = a.replace("o as AST", "(AST) o")
                a = a.replace("other as AST", "(AST) other")
                if in_static_class:
                    a = a.replace("static", "")
                a = re.sub("ref (?P<id>\w+)", "\g<id>", a)
                subst_getters(a, getters)
                tgt.write(a)
                
    tgt.close()

mk_java_bindings()
