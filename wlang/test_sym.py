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

import unittest

from . import ast, sym
import z3


class TestSym(unittest.TestCase):
    def test_1(self):
        st = sym.SymState()
        st.is_error()
        st.__repr__()
        print(st)
        st.to_smt2()
        r = z3.IntVal(0) > z3.IntVal(1)
        st._solver.add(r)
        st.pick_concerete()

    def test_2(self):
        prg1 = "x:=0; print_state; skip"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        st.pick_concerete()
        self.assertEquals(len(out), 1)

    def test_3(self):
        prg1 = "havoc x,y; if(x*y)<1 then {x:=2; y:=3} else{x:=4;y:=5}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()

        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 2)

    def test_4(self):
        prg1 = "havoc x,y; if x<=y or y>=x then x:=x/2;w:=x+y else{x:=1;y:=2}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 2)

    def test_5(self):
        prg1 = "havoc x; y:=2; while (not (x=10)) do {x:=x-1; y:=y-1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 11)

    def test_6(self):
        prg1 = "x:=2; while x>1 and true do x:=x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_7(self):
        prg1 = "x:=1; assume x=1; assume x=0 "
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_8(self):
        prg1 = "x:=1; assert x=1; assert x=0"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_9(self):
        ae1 = ast.AExp(['+'], [ast.IntConst("1"), ast.IntConst("2")])
        ae2 = ast.AExp(['+'], [ast.IntConst("1"), ast.IntConst("2")])
        Ast = ast.RelExp(ae1, ["?"], ae2)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(Ast, st)]

    # A program on which the symbolic execution engine diverges, uncomment this test for marking Q4e
    # def test_10(self):
    #     ast1 = ast.parse_file("wlang/diverge.wl")
    #     engine = sym.SymExec()
    #     st = sym.SymState()
    #     out = [s for s in engine.run(ast1, st)]
    #     self.assertEquals(len(out), 2662)
