"""Prototype preprocessing for native FiniteSet bounded-filter formulas."""

import collections


def symbol(node):
    return node[1:-1] if node.startswith("|") and node.endswith("|") else node


def occurs(node, name):
    if isinstance(node, str):
        return symbol(node) == symbol(name)
    if node and node[0] in ("lambda", "forall", "exists", "let"):
        if node[0] == "let" and any(occurs(v, name) for _, v in node[1]):
            return True
        if any(symbol(n) == symbol(name) for n, _ in node[1]):
            return False
        return occurs(node[2], name)
    return any(occurs(child, name) for child in node)


def empty(node):
    return isinstance(node, list) and len(node) == 3 and node[:2] == ["as", "set.empty"]


class FiniteSetSimplifier:
    def __init__(self):
        self.stats = collections.Counter()
        self.records = {}
        self.selectors = {}
        self.results = {}
        self.names = set()
        self.serial = 0

    def register_sort(self, name, sort):
        name = symbol(name)
        previous = self.results.get(name, sort)
        self.results[name] = sort if previous == sort else None

    def sort_of(self, node):
        if isinstance(node, str):
            if node in ("true", "false"):
                return "Bool"
            if node.lstrip("-").isdigit():
                return "Int"
            return self.results.get(symbol(node))
        if not node or not isinstance(node[0], str):
            return None
        op, *args = node
        if op in ("+", "-", "*", "abs"):
            sorts = [self.sort_of(a) for a in args]
            if sorts and all(s == "Int" for s in sorts):
                return "Int"
            if sorts and all(s in ("Int", "Real") for s in sorts):
                return "Real"
            return None
        if op in ("div", "mod") and all(self.sort_of(a) == "Int" for a in args):
            return "Int"
        if op in ("/", "to_real"):
            return "Real"
        if op == "ite" and len(args) == 3:
            a, b = self.sort_of(args[1]), self.sort_of(args[2])
            return a if a == b else None
        return self.results.get(symbol(op))

    def fresh(self):
        while True:
            self.serial += 1
            name = f"__fspp_{self.serial}"
            if name not in self.names:
                self.names.add(name)
                return name

    def substitute(self, node, name, value):
        if isinstance(node, str):
            return value if symbol(node) == symbol(name) else node
        if node and node[0] in ("lambda", "forall", "exists", "let"):
            op, bindings, body = node
            bindings = [[n, self.substitute(v, name, value) if op == "let" else v]
                        for n, v in bindings]
            if any(symbol(n) == symbol(name) for n, _ in bindings):
                return [op, bindings, body]
            for binding in bindings:
                if occurs(value, binding[0]):
                    fresh = self.fresh()
                    body = self.substitute(body, binding[0], fresh)
                    binding[0] = fresh
            return [op, bindings, self.substitute(body, name, value)]
        return [self.substitute(child, name, value) for child in node]

    def basic(self, node):
        if not node:
            return node
        op, *args = node
        if op in ("and", "or"):
            identity, absorbing = ("true", "false") if op == "and" else ("false", "true")
            flat = []
            for arg in args:
                if arg == absorbing:
                    return absorbing
                if arg == identity:
                    continue
                flat.extend(arg[1:] if isinstance(arg, list) and arg and arg[0] == op else [arg])
            return identity if not flat else flat[0] if len(flat) == 1 else [op, *flat]
        if op == "not" and len(args) == 1:
            arg = args[0]
            if arg in ("true", "false"):
                return "false" if arg == "true" else "true"
            if isinstance(arg, list) and arg and arg[0] == "not":
                return arg[1]
        if op == "=>" and len(args) == 2:
            a, b = args
            if a == "false" or b == "true" or a == b:
                return "true"
            if a == "true":
                return b
            if b == "false":
                return self.basic(["not", a])
        if op == "+":
            args = [a for a in args if a != "0"]
            return "0" if not args else args[0] if len(args) == 1 else [op, *args]
        if op == "-" and len(args) == 2 and args[1] == "0":
            return args[0]
        if op in ("=", "distinct", "<=", ">=", "<", ">") and len(args) == 2:
            a, b = args
            if a == b:
                return "false" if op in ("distinct", "<", ">") else "true"
            if op == "=":
                if empty(a) and isinstance(b, list) and b[0] == "set.singleton":
                    return "false"
                if empty(b) and isinstance(a, list) and a[0] == "set.singleton":
                    return "false"
                if a in ("true", "false"):
                    return b if a == "true" else self.basic(["not", b])
                if b in ("true", "false"):
                    return a if b == "true" else self.basic(["not", a])
        if op == "set.in" and len(args) == 2:
            if empty(args[1]):
                return "false"
            if isinstance(args[1], list) and args[1][0] == "set.singleton":
                return self.basic(["=", args[0], args[1][1]])
        selector = self.selectors.get(symbol(op)) if isinstance(op, str) else None
        if selector is not None and len(args) == 1:
            ctor, index = selector
            value = args[0]
            if (isinstance(value, list) and value and isinstance(value[0], str)
                    and symbol(value[0]) == symbol(ctor)):
                return value[index + 1]
        return node

    def point(self, name, sort, body):
        conjuncts = body[1:] if isinstance(body, list) and body and body[0] == "and" else [body]
        targets = [(name, None)]
        record = self.records.get(symbol(sort)) if isinstance(sort, str) else None
        if record and len(record[1]) == 1:
            targets.append(([record[1][0], name], record[0]))
        for target, ctor in targets:
            if ctor and self.results.get(symbol(ctor)) != sort:
                continue
            lower, upper = [], []
            value = None
            for term in conjuncts:
                if not isinstance(term, list) or len(term) != 3:
                    continue
                op, a, b = term
                if b == target:
                    a, b = b, a
                    op = {"<=": ">=", ">=": "<="}.get(op, op)
                if a != target or occurs(b, name):
                    continue
                if op == "=":
                    value = b
                    break
                if op == ">=":
                    lower.append(b)
                if op == "<=":
                    upper.append(b)
            if value is None:
                value = next((a for a in lower if any(a == b for b in upper)), None)
            expected = self.results[symbol(record[1][0])] if ctor else sort
            if expected is not None and value is not None and self.sort_of(value) == expected:
                return [ctor, value] if ctor else value
        return None

    def bounded(self, mode, predicate, domain):
        name, sort = predicate[1][0]
        body = self.rewrite(predicate[2])
        domain = self.rewrite(domain)
        zero = ["as", "set.empty", ["FiniteSet", sort]]
        is_empty = self.basic(["=", domain, zero])
        if empty(domain):
            self.stats["empty_domain"] += 1
            return "true"
        if not occurs(body, name):
            self.stats["unused_binder"] += 1
            if mode == "all":
                return self.basic(["or", is_empty, body])
            nonempty = self.basic(["not", is_empty])
            return self.basic(["not", self.basic(["and", nonempty, body])])
        point = self.point(name, sort, body)
        if point is not None:
            self.stats["fixed_point"] += 1
            condition = self.rewrite(self.substitute(body, name, point))
            if mode == "all":
                singleton = ["set.singleton", point]
                return self.basic(["or", is_empty,
                                   self.basic(["and", ["=", domain, singleton], condition])])
            member = self.basic(["set.in", point, domain])
            return self.basic(["not", self.basic(["and", member, condition])])
        if mode == "all" and isinstance(body, list) and body[0] == "=>" and not occurs(body[1], name):
            self.stats["independent_guard"] += 1
            rest = self.bounded(mode, ["lambda", predicate[1], body[2]], domain)
            return self.basic(["or", self.basic(["not", body[1]]), rest])
        if mode == "none" and isinstance(body, list) and body[0] == "and":
            independent = [a for a in body[1:] if not occurs(a, name)]
            dependent = [a for a in body[1:] if occurs(a, name)]
            if independent and dependent:
                self.stats["independent_guard"] += 1
                guard = self.basic(["and", *independent])
                rest = self.bounded(mode, ["lambda", predicate[1],
                                          self.basic(["and", *dependent])], domain)
                return self.basic(["or", self.basic(["not", guard]), rest])
        filtered = ["set.filter", ["lambda", predicate[1], body], domain]
        return ["=", filtered, domain if mode == "all" else zero]

    def rewrite(self, node):
        if not isinstance(node, list):
            return node
        if len(node) == 3 and node[0] == "=":
            for filtered, other in ((node[1], node[2]), (node[2], node[1])):
                if not (isinstance(filtered, list) and len(filtered) == 3 and filtered[0] == "set.filter"):
                    continue
                predicate, domain = filtered[1:]
                if not (isinstance(predicate, list) and len(predicate) == 3
                        and predicate[0] == "lambda" and len(predicate[1]) == 1):
                    continue
                if other == domain:
                    return self.bounded("all", predicate, domain)
                if empty(other):
                    return self.bounded("none", predicate, domain)
        if node and node[0] in ("lambda", "forall", "exists"):
            return [node[0], node[1], self.rewrite(node[2])]
        if node and node[0] == "let":
            return ["let", [[n, self.rewrite(v)] for n, v in node[1]], self.rewrite(node[2])]
        return self.basic([self.rewrite(child) for child in node])

    def simplify(self, commands):
        pending = list(commands)
        while pending:
            node = pending.pop()
            if isinstance(node, str):
                self.names.add(symbol(node))
            else:
                pending.extend(node)
        for cmd in commands:
            if cmd[0] == "declare-const":
                self.register_sort(cmd[1], cmd[2])
            if cmd[0] == "declare-fun":
                self.register_sort(cmd[1], cmd[3])
            if cmd[0] != "declare-datatypes":
                continue
            for (sort, arity), constructors in zip(cmd[1], cmd[2]):
                if arity != "0" or len(constructors) != 1:
                    continue
                ctor, *fields = constructors[0]
                self.records[symbol(sort)] = (ctor, [n for n, _ in fields])
                self.register_sort(ctor, sort)
                for index, (selector, _) in enumerate(fields):
                    key = symbol(selector)
                    value = (ctor, index)
                    previous = self.selectors.get(key, value)
                    self.selectors[key] = value if previous == value else None
                for selector, field_sort in fields:
                    self.register_sort(selector, field_sort)
        return [["assert", self.rewrite(cmd[1])] if cmd[0] == "assert" else cmd
                for cmd in commands]


if __name__ == "__main__":
    import argparse
    import json
    from pathlib import Path
    import time
    from sleec import emit, parse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    simplifier = FiniteSetSimplifier()
    start = time.perf_counter()
    commands = simplifier.simplify(parse(args.input.read_text(encoding="utf-8")))
    args.output.write_text("\n".join(map(emit, commands)) + "\n", encoding="utf-8")
    print(json.dumps({"rules": dict(simplifier.stats),
                      "seconds": time.perf_counter() - start}, indent=2))
