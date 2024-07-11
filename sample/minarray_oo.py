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

    def axiom_axm1(self):
        return (self.n>0)

    def axiom_axm2(self):
        x = Int('x')
        return ForAll(x, Implies(And(x>=1, x<=self.n), self.f(x)>=0))

    
class Machine_BinarySearch_ref0(object) :
    def __init__(self,context:Context):
        self.m = Int('m')
        self.context = context
        
    def event_initialisation(self):
        guard = {} # empty dictionary
        init = BAssignment({self.m},prime(self.m) == 0) # m := 0
        return BEvent('initialisation',Status.Ordinary,[],guard,init)

    def event_mini(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.m}, prime(self.m) >= 0) # m :IN NAT
        return  BEvent('mini',Status.Ordinary,[],guard,ba)

    def event_progress(self):
        guard = {} # empty dictionary
        ba =  BAssignment({self.m},prime(self.m) >= 0) # m :IN NAT
        return BEvent('progress',Status.Anticipated,[],guard,ba)
    
    def invariant_inv1(self):
        return (self.m>=0)


class Machine_BinarySearch_ref1(Machine_BinarySearch_ref0):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref0,context:Context):
        super().__init__(abstract_machine.context)
        self.context = context
        self.abstract_machine = abstract_machine
        self.p = Int('p')
        self.q = Int('q')
        self.variant = (self.q - self.p)
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.m,self.p,self.q},And(prime(self.m) == 0,
                                                        prime(self.p) == 1,
                                                        prime(self.q) == self.context.n))
        init = BEventRef('initialisation',super().event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init

    def ref_event_mini(self):
        guard = {'grd1': (self.p == self.q)}
        ba = BAssignment({self.m,self.p,self.q},And(prime(self.m) == self.context.f(self.p),
                                                        prime(self.p) == self.p,
                                                        prime(self.q) == self.q))
        mini = BEventRef('mini',super().event_mini())
        mini.set_status(Status.Ordinary)
        mini.add_guards(guard)
        mini.add_bassg(ba)
        return mini

    def ref_event_inc(self):
        guard = {'grd1': (self.p<self.q), 'grd2': (self.context.f(self.p)>self.context.f(self.q))}
        ba = BAssignment({self.m,self.p,self.q},
                             And(prime(self.p) == self.p+1,
                                     prime(self.m) == self.m,
                                     prime(self.q) == self.q))
        inc = BEventRef('inc',super().event_progress())
        inc.set_status(Status.Convergent)
        inc.add_guards(guard)
        inc.add_bassg(ba)
        return inc

    def ref_event_dec(self):
        guard = {'grd1': (self.p<self.q), 'grd2': (self.context.f(self.p)<=self.context.f(self.q))}
        ba = BAssignment({self.m,self.p,self.q},
                             And(prime(self.q) == self.q-1,
                                     prime(self.m) == self.m,
                                     prime(self.p) == self.p))
        dec = BEventRef('dec',super().event_progress())
        dec.set_status(Status.Convergent)
        dec.add_guards(guard)
        dec.add_bassg(ba)
        return dec
    
    def invariant_inv1(self):
        return  And(self.p>=1,self.p<=self.context.n) # p IN 1..n
    
    def invariant_inv2(self):
        return And(self.q>=1,self.q<=self.context.n) # q IN 1..n
    
    def invariant_inv3(self):
        return (self.p<=self.q) # p <= q
