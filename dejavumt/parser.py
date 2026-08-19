"""
Parser for DejaVuMT specifications.

Surface syntax follows DejaVu's QTL (see dejavu Parser.scala), with optional
type annotations on declared predicate/event parameters.

Currently supported (slice 1 -- untimed fragment):

    declarations:  pred/event/preds/events  name(p1: Sort, ...), ...
    macros:        pred name(a, ...) = <ltl>
    properties:    prop name : <ltl>

    operators:     -> <-> | & ! @ S Z P H [_,_)  Exists/Forall
    future:        X (next), U (until), F (eventually), G (always), with or
                   without a time bound -- verdicts may then be delayed
    timed:         S/Z/U/P/H/F/G with a time bound: [a,b], [a,*], or the sugar
                   [<=n] [<n] [>=n] [>n]  (e.g.  p S[<=3] q,  P[10,20] p)
    relations:     = < <= > >=   over variables and constants
    strings:       s contains "sub"   substring test over String terms
    parametric:    a symbolic upper bound on a timed operator (P[<=n],
                   F[<=n], S[0,n]; not U) -- the monitor leaves n free and
                   reports, per position, the constraint on n under which
                   the property holds

Not yet supported (planned): recursive rules (where ... :=) and the seen-only
lowercase exists/forall quantifiers.
"""
from __future__ import annotations

from lark import Lark, Transformer, v_args

from . import ast


_GRAMMAR = r"""
    start: definition+

    ?definition: macrodef
               | eventdef
               | propertydef

    macrodef: PRED NAME paren_params? "=" ltl

    eventdef: DECLKW predsig ("," predsig)*
    predsig: NAME paren_typed_params?

    propertydef: "prop" NAME ":" ltl

    paren_params: "(" [NAME ("," NAME)*] ")"
    paren_typed_params: "(" [typed_param ("," typed_param)*] ")"
    typed_param: NAME (":" SORT)?

    // --- formulas, loosest binding first ---
    // A quantifier scopes over everything to its right (wide scope), as in
    // DejaVu:  Forall f . close(f) -> phi  ==  Forall f . (close(f) -> phi).
    // Quantifiers may also occur nested in operand position, e.g.
    // ! Exists i . phi  or  a | Exists m . phi, again scoping to the end of
    // the enclosing formula.  To keep the grammar unambiguous, each
    // precedence level has a plain variant (no unparenthesized quantifier)
    // used for non-final operands, and a "q" variant allowing a quantified
    // tail as the final operand — so the wide parse is the only parse.
    ?ltl: ltl_implq

    ?ltl_implq: ltl_or "->" ltl_implq   -> implies
              | ltl_or "<->" ltl_implq  -> iff
              | ltl_orq
    ?ltl_orq: ltl_or "|" ltl_andq       -> or_
            | ltl_andq
    ?ltl_or: ltl_or "|" ltl_and         -> or_
           | ltl_and
    ?ltl_andq: ltl_and "&" ltl_sinceq   -> and_
             | ltl_sinceq
    ?ltl_and: ltl_and "&" ltl_since     -> and_
            | ltl_since
    ?ltl_sinceq: leaf _S timebound uleafq -> timed_since
               | leaf _S uleafq          -> since
               | leaf _Z timebound uleafq -> timed_zince
               | leaf _Z uleafq          -> zince
               | leaf _U timebound uleafq -> timed_until
               | leaf _U uleafq          -> until_
               | uleafq
    ?ltl_since: leaf _S timebound leaf -> timed_since
              | leaf _S leaf            -> since
              | leaf _Z timebound leaf -> timed_zince
              | leaf _Z leaf            -> zince
              | leaf _U timebound leaf -> timed_until
              | leaf _U leaf            -> until_
              | leaf

    // Unary chain that may end in a quantifier (the "q" tail).
    ?uleafq: quant
           | "!" uleafq                     -> not_
           | "@" uleafq                     -> prev
           | _X uleafq                      -> next_
           | _P timebound uleafq            -> timed_once
           | _H timebound uleafq            -> timed_hist
           | _F timebound uleafq            -> timed_ev
           | _G timebound uleafq            -> timed_alw
           | _P uleafq                      -> once
           | _H uleafq                      -> hist
           | _F uleafq                      -> eventually
           | _G uleafq                      -> always
           | leaf

    quant: "Exists" NAME "." ltl            -> exists
         | "Forall" NAME "." ltl            -> forall

    ?leaf: "true"                          -> true_
         | "false"                         -> false_
         | sum OPER sum                     -> compare
         | atom MATCHES ESCAPED_STRING     -> matches_
         | atom MATCHES REGEX_LIT          -> matches_re
         | sum CONTAINS sum                 -> compare
         | NAME paren_args?                -> pred
         | "!" leaf                        -> not_
         | "@" leaf                        -> prev
         | _X leaf                         -> next_
         | _P timebound leaf               -> timed_once
         | _H timebound leaf               -> timed_hist
         | _F timebound leaf               -> timed_ev
         | _G timebound leaf               -> timed_alw
         | _P leaf                         -> once
         | _H leaf                         -> hist
         | _F leaf                         -> eventually
         | _G leaf                         -> always
         | "[" ltl "," ltl ")"            -> interval
         | "(" ltl ")"                     -> parens

    // Time bounds on S/Z/P/H: an interval [a,b] or [a,*], or comparison sugar.
    // The upper bound may also be a NAME: a symbolic parameter, left free by
    // the monitor, whose verdicts then become constraints on it (parametric
    // monitoring; every timed operator except U -- see engine.collect_params).
    ?timebound: "[" "<=" INT "]"       -> tb_le
              | "[" "<" INT "]"        -> tb_lt
              | "[" ">=" INT "]"       -> tb_ge
              | "[" ">" INT "]"        -> tb_gt
              | "[" INT "," INT "]"    -> tb_ab
              | "[" INT "," "*" "]"    -> tb_astar
              | "[" "<=" NAME "]"      -> tb_le_p
              | "[" INT "," NAME "]"   -> tb_ab_p

    // Arithmetic expressions in relation operands (* binds tighter than +/-).
    ?sum: sum "+" product   -> add
        | sum "-" product   -> sub
        | product
    ?product: product "*" atom -> mul
            | atom
    ?atom: NAME             -> var
         | INT              -> int_const
         | FLOAT            -> float_const
         | ESCAPED_STRING   -> str_const
         | "-" atom         -> neg
         | "(" sum ")"

    paren_args: "(" [term ("," term)*] ")"

    // Predicate arguments are plain terms (no arithmetic).
    ?term: NAME             -> var
         | ESCAPED_STRING   -> str_const
         | INT              -> int_const
         | FLOAT            -> float_const
         | "-" INT          -> neg_int_const
         | "-" FLOAT        -> neg_float_const

    OPER: "<=" | ">=" | "<" | ">" | "="
    // `contains` is a string substring test (s contains "sub"). It is an
    // alphabetic keyword, so it must be boundary-guarded and excluded from NAME
    // (below) just like the single-letter operators — else it would lex as the
    // head of an identifier. .2 priority so a bare `contains` beats NAME.
    CONTAINS.2: /contains(?![A-Za-z0-9_])/
    // `matches` tests a String term against a pattern with holes:
    //   m matches "user {u}"        binds hole u to the captured substring
    //   m matches "id {n:[0-9]+}"   hole constrained by a regex subset
    // Semantics is a constraint (all decompositions), see dejavumt/pattern.py.
    MATCHES.2: /matches(?![A-Za-z0-9_])/
    // Slashed pattern: full regex with embedded {holes}.  May not start
    // with '*' (would collide with the /* comment opener).
    REGEX_LIT: /\/(?!\*)([^\/\\\n]|\\.)+\//
    SORT: "String" | "Int" | "Real" | "Bool"
    PRED: "pred"
    DECLKW: "preds" | "pred" | "events" | "event"

    // Past-time operators S/Z/P/H are single uppercase letters. They MUST be
    // word-boundary guarded, else the dynamic lexer matches them at the head of
    // an ALLCAPS predicate name (e.g. "H" in HEATER_TURNED_ON), splitting it.
    // The negative lookahead means the operator only lexes when NOT followed by
    // an identifier char; NAME still matches such identifiers whole. The leading
    // underscore filters these tokens from the parse tree, so the transformer
    // sees the same shape it did when these were bare string literals.
    _S: /S(?![A-Za-z0-9_])/
    _Z: /Z(?![A-Za-z0-9_])/
    _P: /P(?![A-Za-z0-9_])/
    _H: /H(?![A-Za-z0-9_])/
    _U: /U(?![A-Za-z0-9_])/
    _X: /X(?![A-Za-z0-9_])/
    _F: /F(?![A-Za-z0-9_])/
    _G: /G(?![A-Za-z0-9_])/

    NAME: /(?!(Exists|Forall|true|false|contains|matches)\b)[a-zA-Z_][a-zA-Z0-9_]*/

    %import common.ESCAPED_STRING
    %import common.INT
    %import common.FLOAT
    // Full Unicode whitespace (lark's common.WS misses e.g. the vertical tab,
    // which occurs in DejaVu's distributed specs and which DejaVu's own
    // Java-regex-based parser skips).
    WS: /\s+/
    %ignore WS
    %ignore /\/\/[^\n]*/
    %ignore /\/\*(.|\n)*?\*\//
"""


@v_args(inline=True)
class _ToAst(Transformer):
    # --- terms ---
    def var(self, name):
        return ast.Var(str(name))

    def str_const(self, tok):
        # ESCAPED_STRING includes the surrounding quotes.
        return ast.Const(str(tok)[1:-1], "String")

    def int_const(self, tok):
        return ast.Const(int(tok), "Int")

    def float_const(self, tok):
        return ast.Const(float(tok), "Real")

    def neg_int_const(self, tok):
        return ast.Const(-int(tok), "Int")

    def neg_float_const(self, tok):
        return ast.Const(-float(tok), "Real")

    # --- arithmetic ---
    def add(self, left, right):
        return ast.BinExpr(left, "+", right)

    def sub(self, left, right):
        return ast.BinExpr(left, "-", right)

    def mul(self, left, right):
        return ast.BinExpr(left, "*", right)

    def neg(self, x):
        # Constant-fold  -literal  into a negative constant.
        if isinstance(x, ast.Const) and x.kind in ("Int", "Real"):
            return ast.Const(-x.value, x.kind)
        return ast.Neg(x)

    # --- leaves ---
    def true_(self):
        return ast.TrueC()

    def false_(self):
        return ast.FalseC()

    def compare(self, left, op, right):
        return ast.Compare(left, str(op), right)

    def matches_(self, subject, _kw, pat):
        from .pattern import parse_pattern
        text = str(pat)[1:-1]
        return ast.Match(subject, tuple(parse_pattern(text)), text)

    def matches_re(self, subject, _kw, pat):
        from .pattern import parse_regex_pattern
        text = str(pat)[1:-1]
        return ast.Match(subject, tuple(parse_regex_pattern(text)), text,
                         regex=True)

    def pred(self, name, args=None):
        return ast.Pred(str(name), tuple(args) if args else ())

    def paren_args(self, *terms):
        return list(terms)

    def not_(self, f):
        return ast.Not(f)

    def prev(self, f):
        return ast.Prev(f)

    def once(self, f):
        return ast.Once(f)

    def hist(self, f):
        return ast.Hist(f)

    def interval(self, a, b):
        return ast.Interval(a, b)

    def exists(self, var, f):
        return ast.Exists(str(var), f)

    def forall(self, var, f):
        return ast.Forall(str(var), f)

    def parens(self, f):
        return f

    # --- binary connectives ---
    def implies(self, a, b):
        return ast.Implies(a, b)

    def iff(self, a, b):
        return ast.Iff(a, b)

    def or_(self, a, b):
        return ast.Or(a, b)

    def and_(self, a, b):
        return ast.And(a, b)

    def since(self, a, b):
        return ast.Since(a, b)

    # --- time bounds (low, high, display); high=None means unbounded ---
    @staticmethod
    def _tb(low, high, disp):
        if high is not None and high < low:
            raise ValueError(f"empty time interval {disp}")
        return (low, high, disp)

    def tb_le(self, n):
        return self._tb(0, int(n), f"[<={n}]")

    def tb_lt(self, n):
        return self._tb(0, int(n) - 1, f"[<{n}]")

    def tb_ge(self, n):
        return self._tb(int(n), None, f"[>={n}]")

    def tb_gt(self, n):
        return self._tb(int(n) + 1, None, f"[>{n}]")

    def tb_ab(self, a, b):
        return self._tb(int(a), int(b), f"[{a},{b}]")

    def tb_astar(self, a):
        return self._tb(int(a), None, f"[{a},*]")

    # Parametric bounds: the upper bound is a name (kept as a str), standing
    # for a symbolic Int parameter the monitor never fixes.
    def tb_le_p(self, n):
        return (0, str(n), f"[<={n}]")

    def tb_ab_p(self, a, n):
        return (int(a), str(n), f"[{a},{n}]")

    def timed_since(self, l, tb, r):
        return ast.TimedSince(l, tb[0], tb[1], r, tb[2])

    def zince(self, a, b):
        return ast.Zince(a, b)

    def timed_zince(self, l, tb, r):
        return ast.TimedZince(l, tb[0], tb[1], r, tb[2])

    # --- future operators (verdicts may be delayed) ---
    def next_(self, f):
        return ast.Next(f)

    def until_(self, l, r):
        return ast.TimedUntil(l, 0, None, r, "")

    def timed_until(self, l, tb, r):
        return ast.TimedUntil(l, tb[0], tb[1], r, tb[2])

    def eventually(self, f):
        return ast.TimedEventually(0, None, f, "")

    def timed_ev(self, tb, f):
        return ast.TimedEventually(tb[0], tb[1], f, tb[2])

    def always(self, f):
        return ast.TimedAlways(0, None, f, "")

    def timed_alw(self, tb, f):
        return ast.TimedAlways(tb[0], tb[1], f, tb[2])

    def timed_once(self, tb, f):
        return ast.TimedOnce(tb[0], tb[1], f, tb[2])

    def timed_hist(self, tb, f):
        return ast.TimedHist(tb[0], tb[1], f, tb[2])

    # --- declarations ---
    def typed_param(self, name, sort=None):
        return ast.Param(str(name), str(sort) if sort is not None else "String")

    def paren_typed_params(self, *params):
        return list(params)

    def predsig(self, name, params=None):
        return ast.EventDecl(str(name), tuple(params) if params else ())

    def eventdef(self, _kw, *sigs):
        return list(sigs)

    def paren_params(self, *names):
        return [str(n) for n in names]

    def macrodef(self, _kw, name, params=None, body=None):
        # When there are no params, lark passes (kw, name, body).
        if body is None:
            params, body = None, params
        return ast.Macro(str(name), tuple(params) if params else (), body)

    def propertydef(self, name, body):
        return ast.Property(str(name), body)

    def start(self, *defs):
        spec = ast.Spec()
        for d in defs:
            if isinstance(d, list):  # eventdef -> list of EventDecl
                spec.events.extend(d)
            elif isinstance(d, ast.Macro):
                spec.macros.append(d)
            elif isinstance(d, ast.Property):
                spec.properties.append(d)
        return spec


_parser = Lark(_GRAMMAR, parser="earley", maybe_placeholders=False)


def parse_spec(text: str) -> ast.Spec:
    tree = _parser.parse(text)
    return _ToAst().transform(tree)


def parse_file(path: str) -> ast.Spec:
    with open(path, "r") as f:
        return parse_spec(f.read())
