import unittest

from . import ast, stats_visitor


class TestStatsVisitor (unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 2)
        self.assertEquals(sv.get_num_vars(), 1)
