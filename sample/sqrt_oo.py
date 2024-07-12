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
        self.n = Const('n',IntSort()) # the size of the array f

    def axiom_axm0(self):
        return (self.n>=0)

class Machine_BinarySearch_ref0(object) :
    def __init__(self,context:Context):
        self.r = Int('r')
        self.context = context
        
    def event_initialisation(self):
        guard = {} # empty dictionary
        init = BAssignment({self.r},prime(self.r) >= 0) # r :IN NAT
        return BEvent('initialisation',Status.Ordinary,[],guard,init)

    def event_progress(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.r},prime(self.r) >= 0) # r :IN NAT
        return BEvent('progress',Status.Anticipated,[],guard,ba)

    def event_final(self):
        guard = {'grd1': And(self.r*self.r<=self.context.n,
                                 self.context.n < (self.r+1)*(self.r+1))}
        ba = skip({self.r})
        return BEvent('final',Status.Ordinary,[],guard,ba)
    
    def invariant_inv1(self):
        return (self.r>=0) # r IN NAT
        

class Machine_BinarySearch_ref1(Machine_BinarySearch_ref0):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref0,context:Context):
        super().__init__(abstract_machine.context)
        self.context = context
        self.abstract_machine = abstract_machine
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.r},prime(self.r) == 0)
        init = BEventRef('initialisation',super().event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init

    def ref_event_final(self):
        guard = {'grd1': (self.context.n < (self.r+1)*(self.r+1))}
        ba = skip({self.r})
        final = BEventRef('final',super().event_final())
        final.set_status(Status.Ordinary)
        final.add_guards(guard)
        final.add_bassg(ba)
        return final

    def ref_event_progress(self):
        guard = {'grd1': ((self.r+1)*(self.r+1) <= self.context.n)}
        ba =  BAssignment({self.r}, prime(self.r) == (self.r+1))
        progress = BEventRef('progress',super().event_progress())
        progress.set_status(Status.Convergent)
        progress.add_guards(guard)
        progress.add_bassg(ba)
        return progress
    
    def invariant_inv1(self):
        return (self.r*self.r<=self.context.n) # r*r <= n


class Machine_BinarySearch_ref2(Machine_BinarySearch_ref1):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref1,context:Context):
        super().__init__(abstract_machine,context)
        self.context = context
        self.abstract_machine = abstract_machine
        self.a = Int('a')
        self.b = Int('b')
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.a,self.b,self.r},
                             And(prime(self.r) == 0, prime(self.a) == 1, prime(self.b) == 3))
        init = BEventRef('initialisation',super().ref_event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init
        
    def ref_event_final(self):
        guard = {'grd1': (self.context.n<self.a)}
        ba = skip({self.a,self.b,self.r})
        final = BEventRef('final',super().ref_event_final())
        final.set_status(Status.Ordinary)
        final.add_guards(guard)
        final.add_bassg(ba)
        return final
        
    def ref_event_progress(self):
        guard = {'grd1': ((self.r+1)*(self.r+1) <= self.context.n)}
        ba = BAssignment({self.r,self.a,self.b}, And(prime(self.r) == (self.r+1),
                                          prime(self.a) == self.a+self.b,
                                          prime(self.b) == self.b+2))
        progress = BEventRef('progress',super().ref_event_progress())
        progress.set_status(Status.Ordinary)
        progress.add_guards(guard)
        progress.add_bassg(ba)
        return progress
