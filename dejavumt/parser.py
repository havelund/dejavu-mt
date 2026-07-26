"""
Parser for DejaVuMT specifications.

Surface syntax follows DejaVu's QTL (see dejavu Parser.scala), with optional
type annotations on declared predicate/event parameters.

Currently supported (slice 1 -- untimed fragment):

    declarations:  pred/event/preds/events  name(p1: Sort, ...), ...
    macros:        pred name(a, ...) = <ltl>
    properties:    prop name : <ltl>

    operators:     -> <-> | & ! @ S Z P H [_,_)  Exists/Forall
    timed:         S/Z/P/H with a time bound: [a,b], [a,*], or the sugar
                   [<=n] [<n] [>=n] [>n]  (e.g.  p S[<=3] q,  P[10,20] p)
    relations:     = < <= > >=   over variables and constants

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
    ?ltl_sinceq: leaf "S" timebound uleafq -> timed_since
               | leaf "S" uleafq        -> since
               | leaf "Z" timebound uleafq -> timed_zince
               | leaf "Z" uleafq        -> zince
               | uleafq
    ?ltl_since: leaf "S" timebound leaf -> timed_since
              | leaf "S" leaf           -> since
              | leaf "Z" timebound leaf -> timed_zince
              | leaf "Z" leaf           -> zince
              | leaf

    // Unary chain that may end in a quantifier (the "q" tail).
    ?uleafq: quant
           | "!" uleafq                     -> not_
           | "@" uleafq                     -> prev
           | "P" timebound uleafq           -> timed_once
           | "H" timebound uleafq           -> timed_hist
           | "P" uleafq                     -> once
           | "H" uleafq                     -> hist
           | leaf

    quant: "Exists" NAME "." ltl            -> exists
         | "Forall" NAME "." ltl            -> forall

    ?leaf: "true"                          -> true_
         | "false"                         -> false_
         | sum OPER sum                     -> compare
         | NAME paren_args?                -> pred
         | "!" leaf                        -> not_
         | "@" leaf                        -> prev
         | "P" timebound leaf              -> timed_once
         | "H" timebound leaf              -> timed_hist
         | "P" leaf                        -> once
         | "H" leaf                        -> hist
         | "[" ltl "," ltl ")"            -> interval
         | "(" ltl ")"                     -> parens

    // Time bounds on S/Z/P/H: an interval [a,b] or [a,*], or comparison sugar.
    ?timebound: "[" "<=" INT "]"       -> tb_le
              | "[" "<" INT "]"        -> tb_lt
              | "[" ">=" INT "]"       -> tb_ge
              | "[" ">" INT "]"        -> tb_gt
              | "[" INT "," INT "]"    -> tb_ab
              | "[" INT "," "*" "]"    -> tb_astar

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
    SORT: "String" | "Int" | "Real" | "Bool"
    PRED: "pred"
    DECLKW: "preds" | "pred" | "events" | "event"

    NAME: /(?!(Exists|Forall|true|false)\b)[a-zA-Z_][a-zA-Z0-9_]*/

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

    def timed_since(self, l, tb, r):
        return ast.TimedSince(l, tb[0], tb[1], r, tb[2])

    def zince(self, a, b):
        return ast.Zince(a, b)

    def timed_zince(self, l, tb, r):
        return ast.TimedZince(l, tb[0], tb[1], r, tb[2])

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
