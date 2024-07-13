
# Usage: pytest -x test_inversefunc.py

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
n = Const('n',IntSort()) # n is the size of the array f
ctx0_constants = {'f': f, 'n': n}
context0.add_constants(ctx0_constants)

x = Int('x')
i,j = Ints('i j')

axm1_ctx0 = (n>=0)
axm2_ctx0 = ForAll(x, Implies(And(x>=1, x<=n), f(x)>=0))
axm3_ctx0 = ForAll([i,j],Implies(And(i>=1,i<=n,j>=1,j<=n,i<j),f(i)<f(j))) # f is sorted

ctx0_axioms = {'axm1_ctx0': axm1_ctx0,
                 'axm2_ctx0': axm2_ctx0,
                 'axm3_ctx0': axm3_ctx0}

context0.add_axioms(ctx0_axioms)

# definition of machine m0
m0 = BMachine(context0) # machine 0, the abstract machine
r = Int('r') # m0's variables
# m0's variables
m0.add_variable(r)

# adding the initialisation event
guard_init_m0 = {} # empty dictionary
ba_init_m0 = BAssignment({r},prime(r) >= 0) # r :IN NAT
event_init_m0 = BEvent('initialisation',Status.Ordinary,[],guard_init_m0,ba_init_m0)
m0.add_initevt(event_init_m0)

# adding event final to m0
guard_final_m0 = {'grd1': And(f(r)<=n, n<f(r+1))}
ba_final_m0 = skip(m0.get_variables())
event_final_m0 = BEvent('final',Status.Ordinary,[],guard_final_m0,ba_final_m0)

# adding event progress to m0
guard_progress_m0 = {} # empty dictionary
ba_progress_m0 = BAssignment({r},prime(r) >= 0) # r :IN NAT
event_progress_m0 = BEvent('progress',Status.Anticipated,[],guard_progress_m0,ba_progress_m0)

m0_events = {'final':event_final_m0, 'progress':event_progress_m0}
# adding machine events to m0
m0.add_events(m0_events)

# adding machine invariants to m0
inv1_m0 = (r>=0) # r IN NAT
m0_invariants = {'inv1_m0':inv1_m0}
m0.add_invariants(m0_invariants)

# definition of machine m1
context1 = BContext()
context1 = m0.get_context()

a, b = Ints('a b')
axm1_ctx1 = (a>=0)
axm2_ctx1 = (b>=0)
axm3_ctx1 = (f(a)<=n)
axm4_ctx1 = (n<f(b+1))
axm5_ctx1 = (a<b)

ctx1_axioms = {'axm1_ctx1': axm1_ctx1,
                   'axm2_ctx1': axm2_ctx1,
                   'axm3_ctx1': axm3_ctx1,
                   'axm4_ctx1': axm4_ctx1,
                   'axm5_ctx1': axm5_ctx1}
context1.add_axioms(ctx1_axioms)

m1 = BMachineRefines(m0,context1)
q = Int('q') # m1 variables
# adding m1 variables
m1.add_variable(q)

# adding m1's machine invariants
inv1_m1 = (q>=0) # q IN NAT
inv2_m1 = (r<=q) # r <= q
inv3_m1 = (f(r)<=n) # f(r) <= n
inv4_m1 = (n<f(q+1)) # n < f(q+1)

m1_invariants = {'inv1_m1':inv1_m1,
                     'inv2_m1':inv2_m1,
                     'inv3_m1':inv3_m1,
                     'inv4_m1':inv4_m1}
m1.add_invariants(m1_invariants)

# adding m1's machine variant
m1.add_variant(q-r)

# m1's initialisation event
guard_init_m1 = {} # empty dictionary
ba_init_m1 = BAssignment({q,r},And(prime(r) == a, prime(q) == b))
event_init_m1 = BEventRef('initialisation',event_init_m0)
event_init_m1.set_status(Status.Ordinary)
event_init_m1.add_guards(guard_init_m1)
event_init_m1.add_bassg(ba_init_m1)
m1.add_ref_initevt(event_init_m1)

# event final in m1
guard_final_m1 = {'grd1': (r == q)}
ba_final_m1 = skip(m1.get_variables())
event_final_m1 = BEventRef('final',event_final_m0)
event_final_m1.set_status(Status.Ordinary)
event_final_m1.add_guards(guard_final_m1)
event_final_m1.add_bassg(ba_final_m1)

# event inc in m1
x_inc_m1 = Int('x_inc_m1')
guard_inc_m1 = {'grd1': (x_inc_m1>=0),
                    'grd2': (r!=q),
                    'grd3': (x_inc_m1>=(r+1)),
                    'grd4': (x_inc_m1<=q),
                    'grd5': (f(x_inc_m1)<=n)}
ba_inc_m1 = BAssignment({q,r},And(prime(r) == x_inc_m1, prime(q) == q))
event_inc_m1 = BEventRef('inc',event_progress_m0)
event_inc_m1.set_status(Status.Convergent)
event_inc_m1.add_guards(guard_inc_m1)
event_inc_m1.add_bassg(ba_inc_m1)

# event dec in m1
x_dec_m1 = Int('x_dec_m1')
guard_dec_m1 = {'grd1': (x_dec_m1>=0),
                    'grd2': (x_dec_m1>=(r+1)),
                    'grd3': (x_dec_m1<=q),
                    'grd4': (r!=q),
                    'grd5': (n<f(x_dec_m1))}
ba_dec_m1 = BAssignment({q,r},And(prime(q) == x_dec_m1-1, prime(r) == r))
event_dec_m1 = BEventRef('dec',event_progress_m0)
event_dec_m1.set_status(Status.Convergent)
event_dec_m1.add_guards(guard_dec_m1)
event_dec_m1.add_bassg(ba_dec_m1)

# adding events to the m1
m1_ref_chain = {'final': 'final',
                    'inc': 'progress',
                    'dec': 'progress'} # refinement chain: concrete_event -> abstract_event

m1_events = {'final': event_final_m1,
                 'inc': event_inc_m1,
                 'dec': event_dec_m1}
m1.add_ref_event(event_final_m1)
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


