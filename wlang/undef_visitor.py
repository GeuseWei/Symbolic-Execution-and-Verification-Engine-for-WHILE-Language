# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

from . import ast


class UseDefFact (object):
    """A dataflow fact for a statement.

    Keeps track of all variables defined up to the statement and all uses
    without a definition.
    """

    def __init__(self, defs=None, undefs=None):
        # defined variables
        if defs is None or len(defs) == 0:
            self._defs = set()
        else:
            self._defs = set(defs)

        # used but not defined
        if undefs is None or len(undefs) == 0:
            self._undefs = set()
        else:
            self._undefs = set(undefs)

    def get_defs(self):
        return self._defs

    def get_undefs(self):
        return self._undefs

    def join(self, fact):
        """Joins a given data-flow fact into this one"""
        self._defs = self._defs.intersection(fact._defs)
        self._undefs = self._undefs.union(fact._undefs)

    def fork(self):
        """Splits the current data-flow fact into two"""
        return UseDefFact(self._defs, self._undefs)

    def mark_use(self, var):
        """Marks variable as used"""
        if var not in self._defs:
            self._undefs.add(var)

    def mark_def(self, var):
        """Marks variable as defined"""
        self._defs.add(var)


class UndefVisitor (ast.AstVisitor):
    """Computes all variables that are used before being defined"""

    def __init__(self):
        super(UndefVisitor, self).__init__()
        self._df = UseDefFact()

    def get_defs(self):
        return self._df.get_defs()

    def get_undefs(self):
        return self._df.get_undefs()

    def check(self, node):
        self._df = self.visit(node, df=UseDefFact())

    def visit_StmtList(self, node, *args, **kwargs):
        df = kwargs['df']
        if node.stmts is None:
            return df

        for n in node.stmts:
            df = self.visit(n, df=df)
        return df

    def visit_IntVar(self, node, *args, **kwargs):
        df = kwargs['df']
        df.mark_use(node)
        return df

    def visit_Const(self, node, *args, **kwargs):
        return kwargs['df']

    def visit_Stmt(self, node, *args, **kwargs):
        return kwargs['df']

    def visit_AsgnStmt(self, node, *args, **kwargs):
        df = kwargs['df']
        df = self.visit(node.rhs, df=df)
        df.mark_def(node.lhs)
        return df

    def visit_Exp(self, node, *args, **kwargs):
        df = kwargs['df']
        for a in node.args:
            df = self.visit(a, df=df)
        return df

    def visit_HavocStmt(self, node, *args, **kwargs):
        df = kwargs['df']
        for v in node.vars:
            df.mark_def(v)
        return df

    def visit_AssertStmt(self, node, *args, **kwargs):
        return self.visit(node.cond, *args, **kwargs)

    def visit_AssumeStmt(self, node, *args, **kwargs):
        return self.visit(node.cond, *args, **kwargs)

    def visit_IfStmt(self, node, *args, **kwargs):
        df = kwargs['df']
        df = self.visit(node.cond, df=df)
        df_else = df.fork()
        df = self.visit(node.then_stmt, df=df)
        if node.has_else():
            df_else = self.visit(node.else_stmt, df=df_else)
        df.join(df_else)
        return df

    def visit_WhileStmt(self, node, *args, **kwargs):
        df = kwargs['df']
        df = self.visit(node.cond, df=df)
        df_else = df.fork()
        df = self.visit(node.body, df=df)
        df.join(df_else)
        return df


def main():
    import sys

    prg = ast.parse_file(sys.argv[1])
    uv = UndefVisitor()
    uv.check(prg)
    print('defs at end', uv.get_defs(), 'undefs at end:', uv.get_undefs())


if __name__ == '__main__':
    import sys
    sys.exit(main())
