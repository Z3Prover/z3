############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Z3 Python regex translator
#
# Author: Z3 Contributors
############################################

import re
import sys

if sys.version_info < (3, 11):
    import sre_constants as _re_constants
    import sre_parse as _re_parser
else:
    import re._constants as _re_constants
    import re._parser as _re_parser

from .z3 import *


def _all_char(ctx=None):
    return AllChar(ReSort(StringSort(ctx)))


def _mk_union(parts):
    if len(parts) == 1:
        return parts[0]
    return Union(*parts)


def _mk_concat(parts, ctx=None):
    if len(parts) == 0:
        return Re("", ctx)
    if len(parts) == 1:
        return parts[0]
    return Concat(*parts)


def _category_re(cat, ctx=None):
    digits = Range("0", "9", ctx=ctx)
    spaces = Union(Re(" ", ctx), Re("\t", ctx), Re("\n", ctx), Re("\r", ctx), Re("\f", ctx), Re("\v", ctx))
    word = Union(Range("a", "z", ctx=ctx), Range("A", "Z", ctx=ctx), digits, Re("_", ctx))
    if cat == _re_constants.CATEGORY_DIGIT:
        return digits
    if cat == _re_constants.CATEGORY_NOT_DIGIT:
        return Diff(_all_char(ctx), digits)
    if cat == _re_constants.CATEGORY_SPACE:
        return spaces
    if cat == _re_constants.CATEGORY_NOT_SPACE:
        return Diff(_all_char(ctx), spaces)
    if cat == _re_constants.CATEGORY_WORD:
        return word
    if cat == _re_constants.CATEGORY_NOT_WORD:
        return Diff(_all_char(ctx), word)
    raise NotImplementedError(f"unsupported regex category: {cat}")


def _translate_repeat(lo, hi, value, flags, ctx):
    body = _translate_subpattern(value, flags, ctx)
    if hi == _re_constants.MAXREPEAT:
        if lo == 0:
            return Star(body)
        if lo == 1:
            return Plus(body)
        return Loop(body, lo)
    if lo == 0 and hi == 1:
        return Option(body)
    return Loop(body, lo, hi)


def _translate_in(charset, flags, ctx):
    negate = len(charset) > 0 and charset[0][0] == _re_constants.NEGATE
    if negate:
        charset = charset[1:]
    parts = [_translate_token(tok, flags, ctx) for tok in charset]
    body = _mk_union(parts)
    if negate:
        body = Diff(_all_char(ctx), body)
    return body


def _translate_token(tok, flags, ctx):
    op, value = tok
    if op == _re_constants.LITERAL:
        return Re(chr(value), ctx)
    if op == _re_constants.NOT_LITERAL:
        return Diff(_all_char(ctx), Re(chr(value), ctx))
    if op == _re_constants.ANY:
        if flags & re.DOTALL:
            return _all_char(ctx)
        return Diff(_all_char(ctx), Re("\n", ctx))
    if op == _re_constants.RANGE:
        return Range(chr(value[0]), chr(value[1]), ctx=ctx)
    if op == _re_constants.CATEGORY:
        return _category_re(value, ctx)
    if op == _re_constants.IN:
        return _translate_in(value, flags, ctx)
    if op == _re_constants.BRANCH:
        _, branches = value
        return _mk_union([_translate_subpattern(branch, flags, ctx) for branch in branches])
    if op == _re_constants.SUBPATTERN:
        return _translate_subpattern(value[-1], flags, ctx)
    if op == _re_constants.MAX_REPEAT or op == _re_constants.MIN_REPEAT:
        lo, hi, body = value
        return _translate_repeat(lo, hi, body, flags, ctx)
    if op == _re_constants.AT:
        if value in (_re_constants.AT_BEGINNING, _re_constants.AT_BEGINNING_STRING, _re_constants.AT_END, _re_constants.AT_END_STRING):
            return Re("", ctx)
        raise NotImplementedError(f"unsupported regex anchor: {value}")
    raise NotImplementedError(f"unsupported regex construct: {tok}")


def _translate_subpattern(parsed, flags, ctx):
    parts = [_translate_token(tok, flags, ctx) for tok in parsed]
    return _mk_concat(parts, ctx)


def regex_to_re(pattern, flags=0, ctx=None):
    """Translate a Python regular expression to a Z3 regular expression.

    Unsupported non-regular features (for example, look-arounds and backreferences)
    raise ``NotImplementedError``.

    >>> re_a = regex_to_re("a+")
    >>> simplify(InRe("aaa", re_a))
    True
    >>> simplify(InRe("bbb", regex_to_re("a|b+")))
    True
    >>> simplify(InRe("x", regex_to_re("[a-z]")))
    True
    >>> simplify(InRe("X", regex_to_re("[a-z]")))
    False
    """
    if isinstance(pattern, re.Pattern):
        if flags != 0:
            raise ValueError("flags cannot be provided when pattern is a compiled regex")
        flags = pattern.flags
        pattern = pattern.pattern
    if not isinstance(pattern, str):
        raise TypeError("pattern must be a string or compiled regex pattern")
    parsed = _re_parser.parse(pattern, flags)
    return _translate_subpattern(parsed, flags, ctx)


def fullmatch_in_re(s, pattern, flags=0, ctx=None):
    """Convenience helper that checks sequence membership in a translated regex.

    >>> simplify(fullmatch_in_re("abc", "a.c"))
    True
    >>> simplify(fullmatch_in_re("abc", "a\\.c"))
    False
    """
    return InRe(s, regex_to_re(pattern, flags=flags, ctx=ctx))

