"""
Parser for DejaVuMT specifications.

Surface syntax follows DejaVu's QTL (see dejavu Parser.scala), with optional
type annotations on declared predicate/event parameters.

Currently supported (slice 1 -- untimed fragment):

    declarations:  pred/event/preds/events  name(p1: Sort, ...), ...
    macros:        pred name(a, ...) = <ltl>
    properties:    prop name : <ltl>

    operators:     -> <-> | & ! @ S P H [_,_)  Exists/Forall
    relations:     = < <= > >=   over variables and constants

Not yet supported (planned): timed operators (S[<=n], P[>n], ...), the Z
operator, recursive rules (where ... :=), and the seen-only lowercase
exists/forall quantifiers.
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
    // Quantifiers bind loosest and scope over the whole formula to their right,
    // so  Forall f . close(f) -> phi  means  Forall f . (close(f) -> phi).
    ?ltl: "Exists" NAME "." ltl       -> exists
        | "Forall" NAME "." ltl       -> forall
        | ltl_impl

    ?ltl_impl: ltl_or "->" ltl        -> implies
             | ltl_or "<->" ltl       -> iff
             | ltl_or
    ?ltl_or: ltl_or "|" ltl_and       -> or_
           | ltl_and
    ?ltl_and: ltl_and "&" ltl_since   -> and_
            | ltl_since
    ?ltl_since: leaf "S" leaf         -> since
              | leaf

    ?leaf: "true"                          -> true_
         | "false"                         -> false_
         | term OPER term                  -> compare
         | NAME paren_args?                -> pred
         | "!" leaf                        -> not_
         | "@" leaf                        -> prev
         | "P" leaf                        -> once
         | "H" leaf                        -> hist
         | "[" ltl "," ltl ")"            -> interval
         | "(" ltl ")"                     -> parens

    paren_args: "(" [term ("," term)*] ")"

    ?term: NAME            -> var
         | ESCAPED_STRING  -> str_const
         | SIGNED_INT      -> int_const
         | SIGNED_FLOAT    -> float_const

    OPER: "<=" | ">=" | "<" | ">" | "="
    SORT: "String" | "Int" | "Real" | "Bool"
    PRED: "pred"
    DECLKW: "preds" | "pred" | "events" | "event"

    NAME: /(?!(Exists|Forall|true|false)\b)[a-zA-Z_][a-zA-Z0-9_]*/

    %import common.ESCAPED_STRING
    %import common.SIGNED_INT
    %import common.SIGNED_FLOAT
    %import common.WS
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
