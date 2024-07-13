
# Usage: pytest -x test_minarray.py

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
n = Const('n',IntSort()) # size of f
ctx0_constants = {'f': f, 'n': n}
context0.add_constants(ctx0_constants)

x = Int('x')

axm1_ctx0 = (n>0)
axm2_ctx0 = ForAll(x, Implies(And(x>=1, x<=n), f(x)>=0))

ctx0_axioms = {'axm1_ctx0': axm1_ctx0, 'axm2_ctx0': axm2_ctx0}

context0.add_axioms(ctx0_axioms)

# definition of machine m0
m0 = BMachine(context0) # machine 0, the abstract machine
m = Int('m') # m0's variables
# m0's variables
m0.add_variable(m)

# adding the initialisation event
guard_init_m0 = {} # empty dictionary
ba_init_m0 = BAssignment({m},prime(m) == 0) # m := 0
event_init_m0 = BEvent('initialisation',Status.Ordinary,[],guard_init_m0,ba_init_m0)
m0.add_initevt(event_init_m0)

# adding event mini to m0
guard_mini_m0 = {} # empty dictionary
ba_mini_m0 = BAssignment({m}, prime(m) >= 0) # m :IN NAT
event_mini_m0 = BEvent('mini',Status.Ordinary,[],guard_mini_m0,ba_mini_m0)

# adding event progress to m0
guard_progress_m0 = {} # empty dictionary
ba_progress_m0 = BAssignment({m},prime(m) >= 0) # m :IN NAT
event_progress_m0 = BEvent('progress',Status.Anticipated,[],guard_progress_m0,ba_progress_m0)

m0_events = {'mini':event_mini_m0,
 'progress':event_progress_m0}
# adding machine events to m0
m0.add_events(m0_events)

# adding machine invariants to m0
inv1_m0 = (m>=0) # m IN NAT
m0_invariants = {'inv1_m0':inv1_m0}
m0.add_invariants(m0_invariants)

# definition of machine m1
context1 = BContext()
context1 = m0.get_context()

m1 = BMachineRefines(m0,context1)
p, q = Ints('p q') # m1's variables
# adding variables to m1
m1.add_variables(p,q)

# adding m1's machine invariants
inv1_m1 = And(p>=1,p<=n) # p IN 1..n
inv2_m1 = And(q>=1,q<=n) # q IN 1..n
inv3_m1 = (p<=q) # p <= q
# inv4 min(ran(f)) IN f[p..q]

m1_invariants = {'inv1_m1':inv1_m1, 'inv2_m1':inv2_m1, 'inv3_m1':inv3_m1}
m1.add_invariants(m1_invariants)

# adding m1's machine variant
m1.add_variant(q-p)

# m1's initialisation event
guard_init_m1 = {} # the empty set
ba_init_m1 = BAssignment({m,p,q},And(prime(m) == 0, prime(p) == 1, prime(q) == n))
event_init_m1 = BEventRef('initialisation',event_init_m0)
event_init_m1.set_status(Status.Ordinary)
event_init_m1.add_guards(guard_init_m1)
event_init_m1.add_bassg(ba_init_m1)
m1.add_ref_initevt(event_init_m1)

# event mini in m1
guard_mini_m1 = {'grd1': (p == q)}
ba_mini_m1 = BAssignment({m,p,q},And(prime(m) == f(p), prime(p) == p, prime(q) == q))
event_mini_m1 = BEventRef('mini',event_mini_m0)
event_mini_m1.set_status(Status.Ordinary)
event_mini_m1.add_guards(guard_mini_m1)
event_mini_m1.add_bassg(ba_mini_m1)

# event inc in m1
guard_inc_m1 = {'grd1': (p<q), 'grd2': (f(p)>f(q))}
ba_inc_m1 = BAssignment({m,p,q},And(prime(p) == p+1, prime(m) == m, prime(q) == q))
event_inc_m1 = BEventRef('inc',event_progress_m0)
event_inc_m1.set_status(Status.Convergent)
event_inc_m1.add_guards(guard_inc_m1)
event_inc_m1.add_bassg(ba_inc_m1)

# event dec in m1
guard_dec_m1 = {'grd1': (p<q), 'grd2': (f(p)<=f(q))}
ba_dec_m1 = BAssignment({m,p,q},And(prime(q) == q-1, prime(m) == m, prime(p) == p))
event_dec_m1 = BEventRef('dec',event_progress_m0)
event_dec_m1.set_status(Status.Convergent)
event_dec_m1.add_guards(guard_dec_m1)
event_dec_m1.add_bassg(ba_dec_m1)

m1.add_ref_event(event_mini_m1)
m1.add_ref_event(event_inc_m1)
m1.add_ref_event(event_dec_m1)

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
