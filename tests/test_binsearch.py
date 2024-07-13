
# Usage: pytest -x test_binsearch.py

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
axm0 = (n>=0)
x = Int('x')
axm1 = ForAll(x, Implies(And(x>=1, x<=n), f(x)>=0))
i,j = Ints('i j')
axm2 = ForAll([i,j],Implies(And(i>=1,i<=n,j>=1,j<=n,i<=j),f(i)<=f(j))) # f is sorted
axm3 = Exists(x,And(And(x>=1,x<=n),f(x) == v)) # v IN ran(f)
thm1 = (n>0)

ctx_axioms = {'axm0': axm0, 'axm1': axm1,'axm2': axm2, 'axm3': axm3}

ctx_theorems = {'thm1':thm1}

context0.add_axioms(ctx_axioms)
context0.add_theorems(ctx_theorems)

# definition of machine m0
m0 = BMachine(context0) # machine 0, the abstract machine
r = Int('r') # m0 variables
# machine variables
m0.add_variable(r)

# adding the initialisation event
guard_init_m0 = {} # empty dictionary
ba_init_m0 = BAssignment({r},prime(r) >= 0) # r :IN NAT
event_init_m0 = BEvent('initialisation',Status.Ordinary,[],guard_init_m0,ba_init_m0)
m0.add_initevt(event_init_m0)

# adding event progress to m0
guard_progress_m0 = {} # empty dictionary
ba_progress_m0 = BAssignment({r},prime(r) >= 0) # r :IN NAT
event_progress_m0 = BEvent('progress',Status.Anticipated,[],guard_progress_m0,ba_progress_m0)

# adding event final to m0
guard_final_m0 = {'grd1_m0': And(r>=1,r<=n), 'grd2_m0': (f(r) == v) }
ba_final_m0 = skip(m0.get_variables())
event_final_m0 = BEvent('final',Status.Ordinary,[],guard_final_m0,ba_final_m0)

m0_events = {'final':event_final_m0,
 'progress':event_progress_m0}
# adding machine events to m0
m0.add_events(m0_events)

# adding machine invariants to m0
inv1_m0 = (r>=0) # r IN NAT
m0_invariants = {'inv1_m0':inv1_m0}
m0.add_invariants(m0_invariants)

# definition of machine m1
context1 = BContext()
context1 = m0.get_context()
m1 = BMachineRefines(m0,context1)
p, q = Ints('p q') # m1 variables
# adding m1 variables
m1.add_variables(p,q)

# adding m1's machine invariants
inv1_m1 = And(p>=1,p<=n) # p IN 1..n
inv2_m1 = And(q>=1,q<=n) # q IN 1..n
inv3_m1 = And(r>=p,r<=q) # r IN p..q
inv4_m1 = Exists(x,And(x>=p,x<=q,f(x) == v)) # v IN f[p..q]

m1_invariants = {'inv1_m1':inv1_m1,
                     'inv2_m1':inv2_m1,
                     'inv3_m1':inv3_m1,
                     'inv4_m1':inv4_m1}
m1.add_invariants(m1_invariants)

# adding m1's machine variant
m1.add_variant(q-p)

# m1's initialisation event
guard_init_m1 = {} # empty dictionary
ba_init_m1 = BAssignment({p,q,r},And(prime(p) == 1, prime(q) == n, prime(r) >= 1, prime(r) <= n))
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

# event inc in m1
guard_inc_m1 = {'grd1_m1': (f(r) < v)}
ba_inc_m1 = BAssignment({p,q,r},
And(prime(p) == r+1,prime(r) >= (r+1), prime(r) <= q,
prime(q) == q))
event_inc_m1 = BEventRef('inc',event_progress_m0)
event_inc_m1.set_status(Status.Convergent)
event_inc_m1.add_guards(guard_inc_m1)
event_inc_m1.add_bassg(ba_inc_m1)

# event dec in m1
guard_dec_m1 = {'grd1_m1': (f(r) > v)}
ba_dec_m1 = BAssignment({p,q,r},And(prime(q) == r-1,
prime(r) >= p, prime(r) <= r-1,
prime(p) == p))
event_dec_m1 = BEventRef('dec',event_progress_m0)
event_dec_m1.set_status(Status.Convergent)
event_dec_m1.add_guards(guard_dec_m1)
event_dec_m1.add_bassg(ba_dec_m1)

# m1.add_ref_events(m1_events,m1_ref_chain)
m1.add_ref_event(event_final_m1)
m1.add_ref_event(event_inc_m1)
m1.add_ref_event(event_dec_m1)

# definition of machine m2
context2 = BContext()
context2 = m1.get_context()
m2 = BMachineRefines(m1,context2)

# m2's initialisation event
guard_init_m2 = {} # empty dictionary
ba_init_m2 = BAssignment({p,q,r},And(prime(p) == 1, prime(q) == n,
 prime(r) == ((n+1)/2)))
event_init_m2 = BEventRef('initialisation',event_init_m1)
event_init_m2.set_status(Status.Ordinary)
event_init_m2.add_guards(guard_init_m2)
event_init_m2.add_bassg(ba_init_m2)
m2.add_ref_initevt(event_init_m2)

# event final in m2
guard_final_m2 = {'grd1_m2': (f(r) == v)}
ba_final_m2 = skip(m2.get_variables())
event_final_m2 = BEventRef('final',event_final_m1)
event_final_m2.set_status(Status.Ordinary)
event_final_m2.add_guards(guard_final_m2)
event_final_m2.add_bassg(ba_final_m2)

# event inc in m2
guard_inc_m2 = {'grd1_m2': (f(r) < v)}
ba_inc_m2 = BAssignment({p,q,r},And(prime(p) == r+1,
prime(r) == ((r+1+q)/2),
prime(q) == q))
event_inc_m2 = BEventRef('inc',event_inc_m1)
event_inc_m2.set_status(Status.Ordinary)
event_inc_m2.add_guards(guard_inc_m2)
event_inc_m2.add_bassg(ba_inc_m2)

# event dec in m2
guard_dec_m2 = {'grd1_m2': (f(r) > v)}
ba_dec_m2 = BAssignment({p,q,r},And(prime(q) == r-1,
prime(r) ==((p+r-1)/2),
prime(p) == p))
event_dec_m2 = BEventRef('dec',event_dec_m1)
event_dec_m2.set_status(Status.Ordinary)
event_dec_m2.add_guards(guard_dec_m2)
event_dec_m2.add_bassg(ba_dec_m2)

m2.add_ref_event(event_final_m2)
m2.add_ref_event(event_inc_m2)
m2.add_ref_event(event_dec_m2)

__machine__ = m2


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

