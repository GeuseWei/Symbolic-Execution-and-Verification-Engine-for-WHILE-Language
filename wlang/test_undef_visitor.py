import unittest

from . import ast, undef_visitor


class TestUndefVisitor (unittest.TestCase):
    def test1(self):
        prg1 = "x := 10; y := x + z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('z')]), uv.get_undefs())

    def test2(self):
        """"Variable defined only on the else branch of the if-statement"""
        prg1 = "havoc x ; if x > 10 then y := x + 1 else { x := x+1 ; z := 10 }; x := z + 1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('z')]), uv.get_undefs())

    def test3(self):
        """Defined only on the then branch of the if statement"""
        prg1 = "havoc x ; if x > 10 then { x := x + 1; z := 10}  else y := x + 1 ; x := z + 1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('z')]), uv.get_undefs())

    def test4(self):
        """Use an undefined variable to re-define itself"""
        prg1 = "x:=x+1"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('x')]), uv.get_undefs())

    def test5(self):
        """Defined inside body of a loop"""
        prg1 = "while true do x := 1 ; y := x"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('x')]), uv.get_undefs())

    def test6(self):
        """Undefined use in a conditional"""
        prg1 = "if x > 0 then skip else skip"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('x')]), uv.get_undefs())

    def test7(self):
        """Undefined use in a loop condition"""
        prg1 = "while x > 0 do skip"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('x')]), uv.get_undefs())

    def test8(self):
        """Undefined use in assume"""
        prg1 = "assume x > 0"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('x')]), uv.get_undefs())

    def test9(self):
        """Undefined use in assert"""
        prg1 = "assert x > 0"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set([ast.IntVar('x')]), uv.get_undefs())

    def test10(self):
        """havoc is a definition"""
        prg1 = "havoc x ; y := x"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals(set(), uv.get_undefs())
