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
        self.v = Const('v',IntSort()) # the value we are looking for

    def axiom_axm0(self):
        return (self.n>=0)

    def axiom_axm1(self):
        x = Int('x')
        return (ForAll(x, Implies(And(x>=1, x<=self.n), self.f(x)>=0)))

    def axiom_axm2(self):
        i = Int('i')
        j = Int('j')
        return ForAll([i,j],Implies(And(i>=1,i<=self.n,j>=1,j<=self.n,i<=j),self.f(i)<=self.f(j))) # f is sorted

    def axiom_axm3(self):
        x = Int('x')
        return Exists(x,And(And(x>=1,x<=self.n),self.f(x) == self.v)) # v IN ran(f)

    def theorem_thm1(self):
        return (self.n>0)

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
        guard = {'grd1_m0': And(self.r>=1,self.r<=self.context.n),
                     'grd2_m0': (self.context.f(self.r) == self.context.v) }
        ba = skip({self.r})
        return BEvent('final',Status.Ordinary,[],guard,ba)
    
    def invariant_inv1(self):
        return (self.r>=0)

class Machine_BinarySearch_ref1(Machine_BinarySearch_ref0):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref0,context:Context):
        super().__init__(abstract_machine.context)
        self.context = context
        self.abstract_machine = abstract_machine
        self.p = Int('p')
        self.q = Int('q')
        self.variant = (self.p - self.q)
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.p,self.q,self.r},
                             And(prime(self.p) == 1,
                                     prime(self.q) == self.context.n,
                                     prime(self.r) >= 1,
                                     prime(self.r) <= self.context.n))
        init = BEventRef('initialisation',super().event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init

    def ref_event_final(self):
        guard = {'grd': (self.context.f(self.r) == self.context.v)}
        ba = skip({self.p, self.q})
        final = BEventRef('final',super().event_final())
        final.set_status(Status.Ordinary)
        final.add_guards(guard)
        final.add_bassg(ba)
        return final

    def ref_event_inc(self):
        guard = {'grd1': (self.context.f(self.r) < self.context.v)}
        ba = BAssignment({self.p, self.q, self.r},
                                 And(prime(self.p) == self.r+1,prime(self.r) >= (self.r+1),
                                         prime(self.r) <= self.q, prime(self.q) == self.q))
        inc = BEventRef('inc',super().event_progress())
        inc.set_status(Status.Convergent)
        inc.add_guards(guard)
        inc.add_bassg(ba)
        return inc

    def ref_event_dec(self):
        guard = {'grd1': (self.context.f(self.r) > self.context.v)}
        ba = BAssignment({self.p, self.q, self.r},
                                 And(prime(self.q) == self.r-1, prime(self.r) >= self.p,
                                         prime(self.r) <= self.r-1, prime(self.p) == self.p))
        dec = BEventRef('dec',super().event_progress())
        dec.set_status(Status.Convergent)
        dec.add_guards(guard)
        dec.add_bassg(ba)
        return dec
    
    def invariant_inv1(self):
        return And(self.p>=1,self.p<=self.context.n) # p IN 1..n
    
    def invariant_inv2(self):
        return  And(self.q>=1,self.q<=self.context.n) # q IN 1..n
    
    def invariant_inv3(self):
        return And(self.r>=self.p,self.r<=self.q) # r IN p..q
    
    def invariant_inv4(self):
        x = Int('x')
        return Exists(x,And(x>=self.p,x<=self.q,self.context.f(x) == self.context.v)) # v IN f[p..q]


class Machine_BinarySearch_ref2(Machine_BinarySearch_ref1):
    def __init__(self,abstract_machine:Machine_BinarySearch_ref1,context:Context):
        super().__init__(abstract_machine,context)
        self.context = context
        self.abstract_machine = abstract_machine
        
    def ref_event_initialisation(self):
        guard = {} # empty dictionary
        ba = BAssignment({self.p,self.q,self.r},
                             And(prime(self.p) == 1,
                                     prime(self.q) == self.context.n,
                                     prime(self.r) == ((self.context.n+1)/2)))
        init = BEventRef('initialisation',super().ref_event_initialisation())
        init.set_status(Status.Ordinary)
        init.add_guards(guard)
        init.add_bassg(ba)
        return init
        
    def ref_event_final(self):
        guard = {'grd1': (self.context.f(self.r) == self.context.v)}
        ba = skip({self.p,self.q,self.r})
        final = BEventRef('final',super().ref_event_final())
        final.set_status(Status.Ordinary)
        final.add_guards(guard)
        final.add_bassg(ba)
        return final
        
    def ref_event_inc(self):
        guard = {'grd1': (self.context.f(self.r) < self.context.v)}
        ba = BAssignment({self.p,self.q,self.r},
                             And(prime(self.p) == self.r+1,
                                     prime(self.r) == ((self.r+1+self.q)/2),
                                     prime(self.q) == self.q))
        inc = BEventRef('inc',super().ref_event_inc())
        inc.set_status(Status.Ordinary)
        inc.add_guards(guard)
        inc.add_bassg(ba)
        return inc
        
    def ref_event_dec(self):
        guard = {'grd1': (self.context.f(self.r) > self.context.v)}
        ba = BAssignment({self.p,self.q,self.r},
                             And(prime(self.q) == self.r-1,
                                     prime(self.r) ==((self.p+self.r-1)/2),
                                     prime(self.p) == self.p))
        dec = BEventRef('dec',super().ref_event_dec())
        dec.set_status(Status.Ordinary)
        dec.add_guards(guard)
        dec.add_bassg(ba)
        return dec

# context = Context()
# bs = Machine_BinarySearch_ref0(context)
# bs.event_initialisation()
# bs.event_progress()
# bs.event_final()

# context1 = Context()
# bs1 = Machine_BinarySearch_ref1(bs,context1)
# bs1.event_initialisation()
# bs1.event_final()
# bs1.event_inc()
# bs1.event_dec()

# context2 = Context()
# bs2 = Machine_BinarySearch_ref2(bs1,context2)
# bs2.event_initialisation()
# bs2.event_final()
# bs2.event_inc()
# bs2.event_dec()
