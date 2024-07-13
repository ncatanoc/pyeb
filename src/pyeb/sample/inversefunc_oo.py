from z3 import * 

# from lib.utils import *
# from lib.assignment import *
# from lib.event import *
# from lib.context import *
# from lib.machine import *

from pyeb.lib.utils import *
from pyeb.lib.assignment import *
from pyeb.lib.event import *
from pyeb.lib.context import *
from pyeb.lib.machine import *


class Context:
    def __init__(self):
        self.f = Function('f', IntSort(), IntSort()) # the array of values
        self.n = Const('n',IntSort()) # the size of the array f
        self.a = Int('a')
        self.b = Int('b')

    def axiom_axm1(self):
        return (self.n>=0)

    def axiom_axm2(self):
        x = Int('x')
        return ForAll(x, Implies(And(x>=1, x<=self.n), self.f(x)>=0))

    def axiom_axm3(self):
        i = Int('i')
        j = Int('j')
        return ForAll([i,j],Implies(And(i>=1,i<=self.n,j>=1,j<=self.n,i<j),self.f(i)<self.f(j))) # f is sorted

    def axiom_axm4(self):
        return (self.a>=0)

    def axiom_axm5(self):
        return (self.b>=0)

    def axiom_axm6(self):
        return (self.f(self.a)<=self.n)

    def axiom_axm7(self):
        return (self.n<self.f(self.b+1))

    def axiom_axm8(self):
        return (self.a<self.b)

class Machine_BinarySearch_ref0(object) :
    def __init__(self,context:Context):
        self.r = Int('r')
        self.context = context
        
    def event_initialisation(self):
        guard = {} # empty dictionary
        init = BAssignment({self.r},prime(self.r) >= 0) # r :IN NAT
        return BEvent('initialisation',Status.Ordinary,[],guard,init)

    def event_final(self):
        guard = {'grd1': And(self.context.f(self.r)<=self.context.n, self.context.n<self.context.f(self.r+1))}
        ba = skip({self.r})
        return  BEvent('final',Status.Ordinary,[],guard,ba)

    def event_progress(self):
        guard = {} # empty dictionary
        ba =  BAssignment({self.r},prime(self.r) >= 0) # r :IN NAT
        return BEvent('progress',Status.Anticipated,[],guard,ba)
    
    def invariant_inv1(self):
        return (self.r>=0)

    
class Machine_BinarySearch_ref1(Machine_BinarySearch_ref0):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref0,context:Context):
        super().__init__(abstract_machine.context)
        self.context = context
        self.abstract_machine = abstract_machine
        self.q = Int('q')
        self.variant = (self.q - self.r)
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.q,self.r},And(prime(self.r) == self.context.a, prime(self.q) == self.context.b))
        init = BEventRef('initialisation',super().event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init

    def ref_event_final(self):
        guard = {'grd1': (self.r == self.q)}
        ba = skip({self.r, self.q})
        final = BEventRef('final',super().event_final())
        final.set_status(Status.Ordinary)
        final.add_guards(guard)
        final.add_bassg(ba)
        return final

    def ref_event_inc(self):
        x = Int('x')
        guard = {'grd1': (x>=0),
                    'grd2': (self.r!=self.q),
                    'grd3': (x>=(self.r+1)),
                    'grd4': (x<=self.q),
                    'grd5': (self.context.f(x)<=self.context.n)}
        ba = BAssignment({self.q,self.r},And(prime(self.r) == x, prime(self.q) == self.q))
        inc = BEventRef('inc',super().event_progress())
        inc.set_status(Status.Convergent)
        inc.add_guards(guard)
        inc.add_bassg(ba)
        return inc

    def ref_event_dec(self):
        x = Int('x')
        guard = {'grd1': (x>=0),
                    'grd2': (x>=(self.r+1)),
                    'grd3': (x<=self.q),
                    'grd4': (self.r!=self.q),
                    'grd5': (self.context.n<self.context.f(x))}
        ba = BAssignment({self.q,self.r},And(prime(self.q) == x-1, prime(self.r) == self.r))
        dec = BEventRef('dec',super().event_progress())
        dec.set_status(Status.Convergent)
        dec.add_guards(guard)
        dec.add_bassg(ba)
        return dec
    
    def invariant_inv1(self):
        return (self.q>=0) # q IN NAT
    
    def invariant_inv2(self):
        return (self.r<=self.q) # r <= q
    
    def invariant_inv3(self):
        return (self.context.f(self.r)<=self.context.n) # f(r) <= n
    
    def invariant_inv4(self):
        return (self.context.n<self.context.f(self.q+1)) # n < f(q+1)
