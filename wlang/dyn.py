import sys

import io
import z3

from . import ast, int
from functools import reduce
from random import randint


class DynState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.conEnv = dict()
        self.symEnv = dict()
        # path condition
        self.path = list()
        self.execType="sym"
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def push(self):
        """Create a new local scope."""
        self._solver.push()

    def pop(self):
        """Revert to the previous local scope."""
        self._solver.pop()

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.symEnv.items():
            st.symEnv[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = DynState()
        child.conEnv = dict(self.conEnv)
        child.symEnv = dict(self.symEnv)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.symEnv.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class DynExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        return self.visit(ast, state=[state])

    def visit_IntVar(self, node, *args, **kwargs):
        st=kwargs["state"]
        match st.execType:
            case "con":
                return kwargs['state'].conEnv[node.name]
            case _: 
                return kwargs['state'].symEnv[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        st=kwargs["state"]
        match st.execType:
            case "con":
                return node.val
            case _: 
                return z3.BoolVal(node.val)

        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        st=kwargs["state"]
        match st.execType:
            case "con":
                return node.val
            case _: 
                return z3.IntVal(node.val)
        

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs
        assert False

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        st=kwargs["state"]
        match st.execType: 
            case "con":
                if node.op == "not":
                    assert node.is_unary()
                    assert len(kids) == 1
                    return not kids[0]

                fn = None
                base = None
                if node.op == "and":
                    fn = lambda x, y: x and y
                    base = True
                elif node.op == "or":
                    fn = lambda x, y: x or y
                    base = False

                assert fn is not None
                return reduce(fn, kids, base)
            
            case _:
                if node.op == "not":
                    assert node.is_unary()
                    assert len(kids) == 1
                    return z3.Not(kids[0])

                fn = None
                base = None
                if node.op == "and":
                    fn = lambda x, y: z3.And(x, y)
                    base = z3.BoolVal(True)
                elif node.op == "or":
                    fn = lambda x, y: z3.Or(x, y)
                    base = z3.BoolVal(False)

                assert fn is not None
                return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None
        if node.op == "+":
            fn = lambda x, y: x + y
        elif node.op == "-":
            fn = lambda x, y: x - y
        elif node.op == "*":
            fn = lambda x, y: x * y
        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return kwargs["state"]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        return kwargs["state"]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        st.symEnv[node.lhs.name] = self.visit(node.rhs, *args, state=st)
        st.conEnv[node.lhs.name] = self.visit(node.rhs, *args, state=st)
        return st
        

    def visit_IfStmt(self, node, *args, **kwargs):
        zero=0
        states = kwargs['state']
        cond = self.visit(node.cond, *args, **kwargs)
        fst=list()
        conds=list()
        state1,state2=states[i].fork()
        i=0
        while i<len(states):
            conds.append(self.visit(node.cond, *args, state=states[i])) 
        one=1
        if self.is_empty(conds[1])==True: 
            state1.add_pc(conds[0])
            state1.execType="con"
            fst.append(self.visit(node.then_stmt, *args, state=[state1]))

        if self.is_empty(Not(conds[0]))==True:
            state2.add_pc(Not(conds[0]))
            if node.has_else()==True:
                state2.execType="sym"
                fst.append(self.visit(node.else_stmt, *args, state=[state2]))
        return fst

    def visit_WhileStmt(self, node, *args, **kwargs):
        states = []

        cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']

        st.push()
        st.add_pc(z3.Not(cond))
        if not st.is_empty():
            states.extend([st])
        st.pop()
        # print(f"in no-while:{states}")
        st.push()
        st.add_pc(cond)
        if not st.is_empty():
            start_states = [st]
            print(f"Start state:{start_states}")
            for i in range(0, 11):
                finish_states = []
                for each_state in start_states:
                    print(f"Current state:{each_state}")
                    cond = self.visit(node.cond, state=each_state)

                    if i != 0:
                        each_state.push()
                        each_state.add_pc(z3.Not(cond))
                        if not each_state.is_empty():
                            states.extend([each_state])
                        each_state.pop()
                        print(f"i!=0:{states}")

                    if i == 0:
                        st = self.visit(node.body, state=each_state)
                        finish_states.extend(st)
                        print(f"i==0:{finish_states}")

                    elif 0 < i < 10:
                        cond = self.visit(node.cond, state=each_state)
                        each_state.push()
                        each_state.add_pc(cond)
                        if not each_state.is_empty():
                            st = self.visit(node.body, state=each_state)
                            finish_states.extend(st)
                        each_state.pop()
                        print(f"0<i<10:{finish_states}")

                start_states = finish_states
        st.pop()

        return states


    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated
        
        st = kwargs['state']
        last=list()
        zero=0
        i=0
        cond = self.visit(node.cond, *args, state=st[i])
        st[i].add_pc(cond)
        last.append(st[i])
        i+=1
        return last

    def visit_AssumeStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs["state"]
        last=list()
        cond = self.visit(node.cond, *args, state=st)
        st.add_pc(cond)
        last.append(st)
        return last
    
    def visit_HavocStmt(self, node, *args, **kwargs):
        one=1
        st = kwargs['state']
        st.symEnv[node.vars.name]=z3.FreshInt("X")
        st.conEnv[node.vars.name]=randomizer()
        st1=kwargs["state"]
        return st1
    
    def visit_StmtList(self, node, *args, **kwargs):
        
        states = [kwargs['state']]
        print(kwargs["state"])
        temp=dict(kwargs)
        for stmt in node.stmts:
            temp["state"] = states
            states = self.visit(stmt, *args, **temp)
              
        return states

def randomizer():
    return randint(1,42)

def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = DynState()
    sym = DynExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
