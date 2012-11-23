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
    s = s.replace(" bool", " boolean")
    s = s.replace("(bool", "(boolean")
    s = s.replace("uint", "long")
    s = s.replace("ulong", "long")
    s = s.replace("string", "String")
    s = s.replace("IntPtr", "long")
    s = s.replace("Dictionary<", "Map<")
    s = s.replace("UInt64", "long")
    s = s.replace("Int64", "long")
    s = s.replace("List<long>", "List<Long>")
    s = s.replace("System.Exception", "Exception")
    return s

def rename_native(s):
    while s.find("Native.Z3") != -1:
        i0 = s.find("Native.Z3")
        i1 = s.find("(", i0)
        c0 = s[:i0]
        c1 = s[i0:i1]
        c1 = c1.replace("Native.Z3_", "Native.")
        c2 = s[i1:]
        lc_callback = lambda pat: pat.group("id").upper()
        c1 = re.sub("_(?P<id>\w)", lc_callback, c1)
        s = c0 + c1 + c2
    return s

def replace_generals(a):
    a = re.sub(" NativeObject", " NativeObject()", a)
    a = re.sub(".NativeObject;", ".NativeObject();", a)
    a = re.sub("Context.nCtx", "Context().nCtx()", a)
    a = re.sub("ctx.nCtx", "ctx.nCtx()", a)
    a = re.sub("ASTKind", "ASTKind()", a)
    return a

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
    in_bracket_op = 0
    in_getter_get = 0
    in_getter_set = 0
    had_ulong_res = 0
    in_enum = 0
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
                tgt.write("\npackage com.Microsoft.Z3;\n\n")
                tgt.write("import java.math.BigInteger;\n")
                tgt.write("import java.util.*;\n")
                tgt.write("import java.lang.Exception;\n")
            elif in_header == 1:
                # tgt.write(" * " + line.replace(filename, tgtfn))
                pass
            elif s.startswith("using"):
                if s.find("System.Diagnostics.Contracts") == -1:
                    tgt.write("/* " + s + " */\n")
            elif s.startswith("namespace"):
                pass
            elif s.startswith("public") and s.find("operator") != -1 and (s.find("==") != -1 or s.find("!=") != -1):
                t = ""
                for i in range(0, line.find(s)+1):
                    t += " "                    
                tgt.write(t + "/* Overloaded operators are not translated. */\n")
                in_unsupported = 1
            elif s.startswith("public enum"):
                tgt.write(line)
                in_enum = 1
            elif in_enum == 1:
                if s == "}":
                    tgt.write(line)
                    in_enum = 0
                else:
                    tgt.write(re.sub("(?P<id>.*)\W*=\W*(?P<val>[^\n,])", "\g<id> (\g<val>)", line))
            elif s.startswith("public class") or s.startswith("internal class") or s.startswith("internal abstract class"):
                a = line.replace(":", "extends").replace("internal ", "")
                a = a.replace(", IComparable", "")
                a = type_replace(a)
                tgt.write(a)
                in_class = 1
                in_static_class = 0
            elif s.startswith("public static class") or s.startswith("abstract class"):
                tgt.write(line.replace(":", "extends").replace("static", "final"))
                in_class = 1
                in_static_class = 1
            elif s.startswith("/// <summary>"):
                tgt.write(line.replace("/// <summary>", "/**"))
                in_javadoc = 1
            elif skip_brace and s == "{":
                skip_brace = 0
            elif ((s.find("public") != -1 or s.find("protected") != -1) and s.find("class") == -1 and s.find("event") == -1 and s.find("(") == -1) or s.startswith("internal virtual IntPtr NativeObject") or s.startswith("internal Context Context"):
                if (s.startswith("new")):
                    s = s[3:]
                s = s.replace("internal virtual", "")
                s = s.replace("internal", "")
                tokens = s.split(" ")
                print "TOKENS: " + str(len(tokens))
                if len(tokens) == 3:
                    in_getter = tokens[2]
                    in_getter_type = type_replace((tokens[0] + " " + tokens[1]))
                    if in_static_class:
                        in_getter_type = in_getter_type.replace("static", "")                        
                    lastindent = line.find(s)
                    skip_brace = 1
                    getters.append(in_getter)
                elif len(tokens) == 4:
                    if tokens[2].startswith("this["):
                        in_bracket_op = 1
                        in_getter = type_replace(tokens[2]).replace("this[", "get(")
                        in_getter += " " + tokens[3].replace("]", ")")
                        in_getter_type = type_replace(tokens[0] + " " + tokens[1])
                    else:
                        in_getter = tokens[3]
                        in_getter_type = type_replace(tokens[0] + " " + tokens[1] + " " + tokens[2])
                    if in_static_class:
                        in_getter_type = in_getter_type.replace("static", "")
                    lastindent = line.find(s)
                    skip_brace = 1         
                    getters.append(in_getter)       
                else:
                    in_getter = tokens[2]
                    in_getter_type = type_replace(tokens[0] + " " + tokens[1])
                    if tokens[2].startswith("this["):
                        lastindent = line.find(s)
                        t = ""
                        for i in range(0, lastindent): t += " "                                
                        tgt.write(t + "/* operator this[] not translated */\n ")
                        in_unsupported = 1
                    else:
                        if in_static_class:
                            in_getter_type = in_getter_type.replace("static", "")                        
                        rest = s[s.find("get ") + 4:-1]
                        subst_getters(rest, getters)
                        rest = type_replace(rest)
                        rest = rename_native(rest)
                        rest = replace_generals(rest)
                        t = ""
                        for i in range(0, lastindent):
                            t += " "
                        tgt.write(t + in_getter_type + " " + in_getter + "() " + rest + "\n")
                        if rest.find("}") == -1:
                            in_getter_get = 1
                        else:
                            getters.append(in_getter)
                            in_getter = ""
                        in_getter_type = ""
                print "ACC: " + s + " --> " + in_getter
            elif s.find("{ get {") != -1:
                line = type_replace(line)
                line = line.replace("internal ", "")
                d = line[0:line.find("{ get")]
                rest = line[line.find("{ get")+5:]
                rest = rest.replace("} }", "}")
                rest = re.sub("Contract.\w+\([\s\S]*\);", "", rest)
                subst_getters(rest, getters)
                rest = rename_native(rest)
                rest = replace_generals(rest)
                if  in_bracket_op:
                    tgt.write(d + rest)
                else:
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
                rest = replace_generals(rest)
                if  in_bracket_op:
                    tgt.write(t + in_getter_type + " " + in_getter + " " + rest + "\n")
                else:
                    tgt.write(t + in_getter_type + " " + in_getter + "() " + rest + "\n")
                if rest.find("}") == -1:
                    in_getter_get = 1
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
                rest = replace_generals(rest)
                ac_acc = in_getter_type[:in_getter_type.find(' ')]
                ac_type = in_getter_type[in_getter_type.find(' ')+1:]
                if  in_bracket_op:
                    in_getter = in_getter.replace("get", "set").replace(")", "")
                    tgt.write(t + ac_acc + " void " + in_getter + ", " + ac_type + " value) " + rest + "\n")
                else:
                    tgt.write(t + ac_acc + " void set" + in_getter + "(" + ac_type + " value) " + rest + "\n")
                if rest.find("}") == -1:
                    in_getter_set = 1
            elif in_getter != "" and in_getter_get == 1 and s == "}":
                tgt.write(line)
                in_getter_get = 0
            elif in_getter != "" and in_getter_set == 1 and s == "}":
                tgt.write(line)
                in_getter_set = 0
            elif in_getter != "" and in_getter_get == 0 and in_getter_set == 0 and s == "}":
                in_getter = ""
                in_getter_type == ""
                in_bracket_op = 0
                skip_brace = 0
            elif s.startswith("uint ") and s.find("=") == -1:
                line = line.replace("uint", "Integer", line)
                line = re.sub("(?P<n>\w+)(?P<c>[,;])", "\g<n>\g<c>", line)
                tgt.write(line);
            elif (not in_class and (s.startswith("{") or s.startswith("}"))) or s.startswith("[") or s.startswith("#"):
                # tgt.write("// Skipping: " + s)
                pass
            elif line == "}\n":
                pass
            else:
                # indent = line.find(s)
                # tgt.write("// LINE: " + line)
                if line.find(": base") != -1:
                    line = re.sub(": base\((?P<p>[^\{]*)\)", "{ super(\g<p>);", line)
                    line = line[4:]
                    obraces = line.count("{")
                    cbraces = line.count("}")
                    mbraces = obraces - cbraces
                    # tgt.write("// obraces = " + str(obraces) + "\n")
                    if obraces == 1:
                        skip_brace = 1
                    else:
                        for i in range(0, mbraces):
                            line = line.replace("\n", "}\n")
                if s.find("(") != -1:
                    line = re.sub(" = [\w.]+(?P<d>[,;\)])", "\g<d>", line)
                a = type_replace(line)
                a = re.sub("(?P<d>[\(, ])params ", "\g<d>", a)
                a = a.replace("base.", "super.")
                a = re.sub("Contract.\w+\([\s\S]*\);", "", a)
                a = rename_native(a)
                a = re.sub("~\w+\(\)", "protected void finalize()", a)
                a = re.sub("foreach\s*\((?P<t>[\w <>,]+)\s+(?P<i>\w+)\s+in\s+(?P<w>\w+)\)",
                           "for (Iterator \g<i> = \g<w>.iterator(); \g<i>.hasNext(); )", a)
                a = a.replace("readonly ", "")
                a = a.replace("const ", "final ")
                a = a.replace("String ToString", "String toString")
                a = a.replace("internal ", "")
                a = a.replace("new static", "static")
                a = a.replace("new public", "public")
                a = a.replace("override ", "")
                a = a.replace("virtual ", "")
                a = a.replace("o as AST", "(AST) o")
                a = a.replace("o as Sort", "(Sort) o")
                a = a.replace("other as AST", "(AST) other")
                a = a.replace("o as FuncDecl", "(FuncDecl) o")
                a = a.replace("IntPtr obj", "long obj")
                a = a.replace("IntPtr o", "long o")
                a = a.replace("new long()", "0")
                a = a.replace("long.Zero", "0")
                a = a.replace("object o", "Object o")
                a = a.replace("object other", "Object other")
                a = a.replace("IntPtr res = IntPtr.Zero;", "Native.IntPtr res = new Native.IntPtr();")
                a = a.replace("out res", "res")
                a = a.replace("GC.ReRegisterForFinalize(m_ctx);", "")
                a = a.replace("GC.SuppressFinalize(this);", "")
                if had_ulong_res == 0 and a.find("ulong res = 0") != -1:
                    a = a.replace("ulong res = 0;", "LongPtr res = new LongPtr();")
                elif had_ulong_res == 1:
                    a = a.replace("ref res)", "res)")
                    if a.find("return res;") != -1:
                        a = a.replace("return res;", "return res.value;")
                        had_ulong_res = 0
                a = a.replace("lock (", "synchronized (")
                if in_static_class:
                    a = a.replace("static", "")
                a = re.sub("ref (?P<id>\w+)", "\g<id>", a)
                subst_getters(a, getters)
                a = re.sub("NativeObject = (?P<rest>.*);", "setNativeObject(\g<rest>);", a)
                a = replace_generals(a)
                tgt.write(a)
                
    tgt.close()

mk_java_bindings()
