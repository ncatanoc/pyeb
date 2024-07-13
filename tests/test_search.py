
# Usage: pytest -x test_search.py

from pyeb.lib.utils import *
from pyeb.lib.assignment import *
from pyeb.lib.event import *
from pyeb.lib.context import *
from pyeb.lib.machine import *
#
import pytest
#

# context definition
context0 = BContext()
f = Function('f', IntSort(), IntSort()) # the array of values
n, v = Consts('n v',IntSort()) # n is the size of the array f, v is the value we are looking for
ctx0_constants = {'f': f, 'n': n, 'v': v}
context0.add_constants(ctx0_constants)

x = Int('x')
i,j = Ints('i j')

axm0 = (n>=1)
axm1 = ForAll(x, Implies(And(x>=1, x<=n), f(x)>=0))
axm2 = Exists(x,And(And(x>=1,x<=n),f(x) == v)) # v IN ran(f)

ctx_axioms = {'axm0': axm0, 'axm1': axm1, 'axm2': axm2}
context0.add_axioms(ctx_axioms)

# definition of machine m0
m0 = BMachine(context0) # machine 0, the abstract machine
r = Int('r') # m0 variables
# machine variables
m0.add_variable(r)

# adding machine invariants to m0
inv1_m0 = (r>=0) # r IN NAT
m0_invariants = {'inv1_m0': inv1_m0}
m0.add_invariants(m0_invariants)

# adding the initialisation event
guard_init_m0 = {} # empty dictionary
ba_init_m0 = BAssignment({r},prime(r) >= 0) # r :IN NAT
event_init_m0 = BEvent('initialisation',Status.Ordinary,[],guard_init_m0,ba_init_m0)
m0.add_initevt(event_init_m0)

# definition of event 'final'
guard_final_m0 = {'grd1_m0': And(r>=1,r<=n), 'grd2_m0': (f(r) == v)}
ba_final_m0 = skip(m0.get_variables())
event_final_m0 = BEvent('final',Status.Ordinary,[],guard_final_m0,ba_final_m0)

# definition of event 'progress'
guard_progress_m0 = {} # empty dictionary
ba_progress_m0 = BAssignment({r},prime(r)>=0) # r :IN NAT
event_progress_m0 = BEvent('progress',Status.Anticipated,[],guard_progress_m0,ba_progress_m0)

m0_events = {'final':event_final_m0, 'progress':event_progress_m0}
# adding the machine events to m0
m0.add_events(m0_events)

po_initialisation_invs_INV = m0.initialisation_invs_INV()
po_evts_invs_INV = m0.evts_invs_INV()
po_evts_acts_FIS = m0.evts_acts_FIS()
po_thms_THM = m0.get_context().thms_THM()

# definition of machine m1
m1 = BMachineRefines(m0,context0)

# adding machine invariants to m1
inv1_m1 = And(r>=1,r<=n) # r IN 1..n
inv2_m1 = ForAll(x,Implies(And(x>=1,x<=(r-1)),f(x)!=v)) # v NOT-IN f[1..r-1]
m1_invariants = {'inv1_m1':inv1_m1, 'inv2_m1':inv2_m1}
m1.add_invariants(m1_invariants)

# adding m1's machine variant
m1.add_variant(n-r)

# m1's initialisation event
guard_init_m1 = {} # empty dictionary
ba_init_m1 = BAssignment({r},prime(r) == 1)
event_init_m1 = BEventRef('initialisation',event_init_m0)
event_init_m1.set_status(Status.Ordinary)
event_init_m1.add_guards(guard_init_m1)
event_init_m1.add_bassg(ba_init_m1)
m1.add_ref_initevt(event_init_m1)

# event final in m1
guard_final_m1 = {'grd1_m1': (f(r) == v)}
ba_final_m1 = skip(m1.get_variables())
event_final_m1 = BEventRef('final',event_final_m0)
event_final_m1.set_status(Status.Ordinary)
event_final_m1.add_guards(guard_final_m1)
event_final_m1.add_bassg(ba_final_m1)

# event progress in m1
guard_progress_m1 = {'grd1_m1': (f(r) != v)}
ba_progress_m1 = BAssignment({r}, prime(r) == (r+1))
event_progress_m1 = BEventRef('progress',event_progress_m0)
event_progress_m1.set_status(Status.Convergent)
event_progress_m1.add_guards(guard_progress_m1)
event_progress_m1.add_bassg(ba_progress_m1)

m1.add_ref_event(event_final_m1)
m1.add_ref_event(event_progress_m1)

__machine__ = m1

def test_initialisation_invs_INV():
    """
    proof obligation: invariants preservation for initialisation event. 
    """
    po = __machine__.initialisation_invs_INV() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: initialisation events adhere to machine invariants')
        print(s.model())
    else:
        print('sat: initialisation events adhere to machine invariants')
    assert s.check() == unsat
    
    
def test_evts_invs_INV():
    """
    proof obligation: machine invariants preservation.
    """
    po = __machine__.evts_invs_INV() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: machines invariants hold')
        print(s.model())
    else:
        print('sat: machine invariants hold')
    assert s.check() == unsat
    
    
def test_evts_acts_FIS():
    """
    proof obligation: feasibility of non-deterministic event actions. 
    """
    po = __machine__.evts_acts_FIS() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: non-deterministic event actions are feasible')
        print(s.model())
    else:
        print('sat: non-deterministic event actions are feasible')
    assert s.check() == unsat
    
    
def test_thms_THM():
    """
    proof obligation: theorems must hold.
    """
    po = __machine__.get_context().thms_THM() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: theorems hold')
        print(s.model())
    else:
        print('sat: theorems hold')
    assert s.check() == unsat
    
    
def test_evts_grd_GRD():
    """
    proof obligation: concrete event guards must be stronger than abstract event guards.
    """
    po = __machine__.evts_grd_GRD() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: concrete event guards are stronger than abstract event guards')
        print(s.model())
    else:
        print('sat: concrete event guards are stronger than abstract event guards')
    assert s.check() == unsat
    
    
def test_evts_act_SIM():
    """
    proof obligation: concrete event guards simulate abstract event guards.
    """
    po = __machine__.evts_act_SIM() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: concrete event guards simulate abstract event guards')
        print(s.model())
    else:
        print('sat: concrete event guards simulate abstract event guards')
    assert s.check() == unsat
    
    
def test_evts_VAR():
    """
    Proof obligation: Convergent events must decrease machine variants.
    """
    
    po = __machine__.evts_VAR() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: converging events decrease machine variants')
        print(s.model())
    else:
        print('sat: converging events decrease machine variants')
    assert s.check() == unsat
    
    
def test_evts_WFIS():
    """
    proof obligation: feasibility of event guard witnesses.
    """
    po = __machine__.evts_WFIS() # proof obligation
    s = Solver()
    s.add(Not(po)) # we add the negation of the formula to the solver
    #
    if s.check() == sat:
        print('unsat: event witnesses are feasible')
        print(s.model())
    else:
        print('sat: event witnesses are feasible')
    assert s.check() == unsat

