from z3 import * 

# from lib.utils import *
# from lib.assignment import *
# from lib.event import *
# from lib.context import *
# from lib.machine import *

from lib.utils import *
from lib.assignment import *
from lib.event import *
from lib.context import *
from lib.machine import *


class Context:
    def __init__(self):
        self.f = Function('f', IntSort(), IntSort()) # the array of values
        self.n = Const('n',IntSort()) # the size of the array f
        self.v = Const('v',IntSort()) # the value we are looking for

    def axiom_axm1(self):
        return (self.n>=1)

    def axiom_axm2(self):
        x = Int('x')
        return ForAll(x, Implies(And(x>=1, x<=self.n), self.f(x)>=0))

    def axiom_axm3(self):
        x = Int('x')
        return Exists(x,And(And(x>=1,x<=self.n),self.f(x) == self.v)) # v IN ran(f)

    
class Machine_BinarySearch_ref0(object) :
    def __init__(self,context:Context):
        self.r = Int('r')
        self.context = context
        
    def event_initialisation(self):
        guard = {} # empty dictionary
        init = BAssignment({self.r},prime(self.r) >= 0) # r :IN NAT
        return BEvent('initialisation',Status.Ordinary,[],guard,init)

    def event_final(self):
        guard = {'grd1_m0': And(self.r>=1,self.r<=self.context.n),
                     'grd2_m0': (self.context.f(self.r) == self.context.v)}
        ba = skip({self.r})
        return  BEvent('final',Status.Ordinary,[],guard,ba)

    def event_progress(self):
        guard = {} # empty dictionary
        ba =   BAssignment({self.r},prime(self.r)>=0) # r :IN NAT
        return BEvent('progress',Status.Anticipated,[],guard,ba)
    
    def invariant_inv1(self):
        return (self.r>=0)


class Machine_BinarySearch_ref1(Machine_BinarySearch_ref0):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref0,context:Context):
        super().__init__(abstract_machine.context)
        self.context = context
        self.abstract_machine = abstract_machine
        self.variant = (self.context.n - self.r)
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.r},prime(self.r) == 1)
        init = BEventRef('initialisation',super().event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init
    
    def ref_event_final(self):
        guard = {'grd1_m1': (self.context.f(self.r) == self.context.v)}
        ba = skip({self.r})
        final = BEventRef('final',super().event_final())
        final.set_status(Status.Ordinary)
        final.add_guards(guard)
        final.add_bassg(ba)
        return final
    
    def ref_event_progress(self):
        guard = {'grd1_m1': (self.context.f(self.r) != self.context.v)}
        ba = BAssignment({self.r}, prime(self.r) == (self.r+1))
        progress = BEventRef('inc',super().event_progress())
        progress.set_status(Status.Convergent)
        progress.add_guards(guard)
        progress.add_bassg(ba)
        return progress
    
    def invariant_inv1(self):
        return  And(self.r>=1,self.r<=self.context.n) # r IN 1..n
        
    def invariant_inv2(self):
        x = Int('x')
        return ForAll(x,Implies(And(x>=1,x<=(self.r-1)),
                                    self.context.f(x)!=self.context.v)) # v NOT-IN f[1..r-1]
