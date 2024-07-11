from z3 import *

#from pyeb.lib.utils import *
from .utils import *
from .assignment import *
from .event import *
from .context import *

def skip(v):
    """ returns the skip statement for v, where v is a set of machine variables. """
    bassg = conjunct_lst([ (prime(elm) == elm) for elm in v])
    res = BAssignment(v,bassg)
    return res

class BMachine:
    """
    Event-B machine.
    """
    def __init__(self,context):
      """ BMachine class constructor. """
      self.events = {} # dictionary of events
      self.v = set() # set of machine variables
      self.invariants = {} # dictionary of invariants
      self.theorems = {} # dictionary of theorems
      self.context = context # machine context
      self.variant = None # machine variant
      self.initialisation = None # the machine initialisation event

    def __copy__(self):
      """ returns a copy of the self object. """
      ctx = BContext()
      ctx = self.get_context()
      obj = BMachine(ctx)
      obj.add_events(self.events)
      obj.add_varset(self.v)
      obj.add_invariants(self.invariants)
      obj.add_theorems(self.theorems)
      if self.variant != None:
        obj.add_variant(self.variant)
      obj.add_initevt(self.initialisation)
      return obj

    """ getters. """

    def get_events(self):
      """ returns a copy of the machine events. """
      return self.events.copy()

    def get_event(self, evt_key):
      """ returns a copy of a particular event. """
      assert evt_key in self.events.keys() # it checks that evt_key really exists
      return self.events[evt_key].__copy__()

    def get_variables(self):
      """ returns a copy of the machine variables. """
      return self.v.copy()

    def get_invariants(self):
      """ returns a coipy of the machine invariants. """
      return self.invariants.copy()

    def get_theorems(self):
      """ returns a coipy of the machine theorems. """
      return self.theorems.copy()

    def get_context(self):
      """ returns the machine context. """
      return self.context.__copy__()

    def get_initevt(self):
      """ returns the machine initialisation event. """
      return self.initialisation.__copy__()

    def get_variant(self):
      """ returns the machine variant. """
      return self.variant

    # def skip(self):
    #   """ returns skip. """
    #   v = self.v
    #   bassg = conjunct_lst([ (prime(elm) == elm) for elm in v])
    #   res = BAssignment(v,bassg)
    #   return res


    """ setters. """

    def add_initevt(self,initevt):
      """ it adds an initialisation event. """
      assert initevt.get_status() == Status.Ordinary
      assert initevt.get_name() == 'initialisation'
      
      self.initialisation = initevt

    def add_event(self,e):
      """ it adds event e to the machine. """
      # abcs
      k = e.get_name() # k is the event's name
      self.events[k] = e

    def add_events(self,events):
      """ it adds a dictionary of events to the machine. """
      for e in events.values():
        self.add_event(e) 

    def add_variable(self,elm):
      self.v.add(elm)

    def add_variables(self,*vars):
      """ it adds a tuple of variables to the machine. """
      for elm in vars:
        self.add_variable(elm)

    def add_varset(self,s):
      """ it adds a set of variables to the machine. """
      for elm in s:
        self.add_variable(elm)

    def add_invariant(self,k,i):
      """ it adds an invariant to the dictionary of invariants. """
      self.invariants[k] = i

    def add_invariants(self,invariants):
      """ it adds a dictionary of invariants to the machine. """
      for k,i in invariants.items():
        self.add_invariant(k,i)

    def add_theorem(self,k,th):
      """ it adds a theorem to the dictionary of theorems. """
      self.theorems[k] = th

    def add_theorems(self,theorems):
      """ it adds a dictionary of theorems to the machine. """
      for k,th in theorems.items():
        self.add_theorem(k,th)

    def add_context(self,cxt):
      """ it sets the machine context. """
      self.context = cxt

    def add_variant(self,n):
      """ it sets the machine variant. """
      self.variant = n


    """ proof obligations. """

    def modified_invariant(self,vlst,inv):
      """ it takes invariant inv and replaces v in vlst with prime(v). """
      # checking that vlst <: self.vlst
      assert all(v in self.get_variables() for v in vlst)

      primed_asgs = [(v,prime(v)) for v in vlst] # it substitutes v with prime(v)
      proof_obligation = substitute(inv,primed_asgs) # it performs the substitutions for inv
      return proof_obligation

    # proof obligation: invariant preservation for event evt
    # the EB Book, Section 5.2.2, Page 188
    def evt_inv_INV(self,evt_key,inv_key):
      """ Proof obligation: invariant preservation. """
      evt = self.events[evt_key]
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())

      invariants = conjunct_dict(self.get_invariants())
      theorems = conjunct_dict(self.get_theorems())

      guard = evt.get_zed_guards()
      ba = evt.get_bassg().get_ba() # a Z3 predicate
      vlst = evt.get_bassg().get_v() # variables involved in the ba predicate
      inv_prime = self.modified_invariant(vlst,self.invariants[inv_key])

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(axioms,ctx_theorems,C,
                        invariants,theorems,
                        guard,
                        ba),inv_prime)

    # proof obligation: invariant preservation for event events[evt_key] against ALL the invs
    def evt_invs_INV(self,evt_key):
      """ Proof obligation: invariant preservation (ALL invariants). """
      po = And(True)
      if len(self.get_invariants()):
        po = conjunct_lst([self.evt_inv_INV(evt_key,inv_key) for  inv_key, inv in self.get_invariants().items()])
      return po

    # proof obligation: invariant preservation for ALL the events against ALL the invs
    def evts_invs_INV(self):
      """ Proof obligation: invariant preservation (ALL events and ALL invariants). """
      po = And(True)
      if len(self.get_invariants()):
        po = conjunct_lst([self.evt_invs_INV(evt_key) for  evt_key, evt in self.events.items()])
      return po

    # proof obligation: invariant preservation for initialisation event
    # the EB Book, Section 5.2.2
    def initialisation_inv_INV(self,inv_key):
      """ Proof obligation: invariant preservation for initialisation event. """
      initevt = self.get_initevt()
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())

      ba = initevt.get_bassg().get_ba() # a Z3 predicate
      vlst = initevt.get_bassg().get_v() # ba's left-hand variables
      inv_prime = self.modified_invariant(vlst,self.invariants[inv_key])

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(axioms,ctx_theorems,C,
                         ba),inv_prime)

    # proof obligation: invariant preservation for initialisation event and all the invariants
    def initialisation_invs_INV(self):
      """ Proof obligation: invariant preservation for initialisation event. """
      po = And(True)
      if len(self.get_invariants()):
        po = And([self.initialisation_inv_INV(inv_key) for inv_key,inv in self.get_invariants().items()])
      return po

    # proof obligation: non-deterministic actions are feasible
    # the EB Book, Section 5.2.2
    def evt_act_FIS(self,evt_key):
      """ Proof obligation: non-deterministic event actions are feasible. """
      evt = self.events[evt_key]
      #
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())
      A = And(axioms,ctx_theorems)

      invariants = conjunct_dict(self.get_invariants())
      theorems = conjunct_dict(self.get_theorems())
      I = And(invariants,theorems)

      guard = evt.get_zed_guards()
      ba = evt.get_bassg().get_ba()
      vlst = evt.get_bassg().get_v() # ba's left-hand variables

      # create fresh constants for each element in vlst
      freshvars = [FreshConst(v.sort(), prefix=str(v) ) for v in vlst]
      # replace primed variables with fresh variables
      ba_fresh = substitute(ba, [(prime(v),freshvar) for v,freshvar in zip(vlst,freshvars) ] )

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(A,I,C,
                         guard),
                     Exists(freshvars,ba_fresh))

    # machine theorem proof obligation
    # the EB Book, Section 5.2.2
    def evts_acts_FIS(self):
      """ Proof obligation: feasibility for event's before-after predicates. """
      po = And(True)
      if len(self.events):
        po = conjunct_lst([self.evt_act_FIS(evt_key) for  evt_key, evt in self.events.items()])
      return po

    # machine theorem proof obligation
    # the EB Book, Section 5.2.2
    def evt_thm_THM(self,th_key):
      """ Proof obligation: theorems must hold. """
      # checking out that th_key is a valid theorem
      theorems_dict = self.get_theorems()
      assert th_key in theorems_dict.keys()

      th = self.theorems[th_key]
      theorems_dict.pop(th_key)

      theorems = conjunct_dict(theorems_dict)
      invariants = conjunct_dict(self.get_invariants())

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(theorems,invariants,C),th)

    # machine theorem proof obligation
    # the EB Book, Section 5.2.2
    def evt_thms_THM(self):
      """ Proof obligation: theorems must hold. """
      po = And(True)
      if len(self.get_theorems()):
        po = conjunct_lst([self.evt_thm_THM(th_key) for  th_key, th in self.get_theorems().items()])
      return po

    
class BMachineRefines(BMachine):
    """
    EB machine refinement.
    """

    def __init__(self,abs_machine,concrete_ctx):
      """ Class constructor. """
      # abc
      super().__init__(abs_machine.get_context()) # calling BMachine's class constructor
      #
      self.events = {} # dictionary of events
      self.v = abs_machine.get_variables() # list of machine variables
      self.invariants = abs_machine.get_invariants() # dictionary of invariants
      self.theorems = abs_machine.get_theorems() # dictionary of theorems
      self.context = concrete_ctx # concrete machine context
      self.initialisation = None # the machine initialisation event
      self.abstract_machine = abs_machine.__copy__() # the abstract machine
      self.ref_chain = {} # concrete_event -> abstract_event
      
      # extending the initialisation event
      self.add_initevt(abs_machine.get_initevt())


    """ getters. """

    def get_abstract_machine(self):
      """ Proof obligation: it returns a reference to the abstract machine. """
      return self.abstract_machine

    """ setters. """    
    def add_ref_event(self,ref_event):
      """ It adds a refinement event. """
      # abc
      abstract_evt_key = ref_event.get_abstract_event().get_name()      
      concrete_evt_key = ref_event.get_name()
      assert abstract_evt_key in self.abstract_machine.get_events().keys() # checking that the abstract event exists
      ##self.events[concrete_evt_key] = ref_events[concrete_evt_key]
      self.ref_chain[concrete_evt_key] = abstract_evt_key
      self.events[concrete_evt_key] = ref_event
      self.events[concrete_evt_key].add_bassg(self.abstract_machine.get_event(abstract_evt_key).get_bassg())
      self.events[concrete_evt_key].add_guards(self.abstract_machine.get_event(abstract_evt_key).get_guards())

    def add_ref_initevt(self,ref_initevt):
      """ it adds an initialisation event for the refinement machine. """
      self.initialisation = self.abstract_machine.get_initevt()
      self.initialisation.add_bassg(ref_initevt.get_bassg())

    def merge_rule_WHILE(self,S_evt_key,T_evt_key,S_chain,T_chain):
      """ merging rules: the WHILE rule. """
      assert S_evt_key in self.events.keys()
      assert T_evt_key in self.events.keys()

      S_evt_key_abs = self.ref_chain[S_evt_key]
      assert S_evt_key_abs in self.abstract_machine.get_events().keys() # checking that the abstract event key exists
      assert self.abstract_machine.get_event(S_evt_key_abs).get_status() == Status.Anticipated # the abstract event S must be Anticipated
      assert self.events[S_evt_key].get_status() == Status.Convergent # the concrete event S must be Convergent

      # events S and T are to be merged
      S_evt = self.events[S_evt_key] # the first event
      T_evt = self.events[T_evt_key] # the second event
      #
      P_lbl_S = S_chain['P'] # the P label in event S
      Q_lbl = S_chain['Q'] # the Q label in event S
      #
      P_lbl_T = T_chain['P'] # the P label in event T
      not_Q_lbl = T_chain['~Q'] # the ~Q label in event T
      #
      P_S = S_evt.get_guard(P_lbl_S) # Z3 predicate
      Q = S_evt.get_guard(Q_lbl) # Z3 predicate
      #
      P_T = T_evt.get_guard(P_lbl_T) # Z3 predicate
      not_Q = T_evt.get_guard(not_Q_lbl) # Z3 predicate
      #
      S = S_evt.get_bassg()
      T = T_evt.get_bassg()
      #
      res = '\nwhen ' +str(P_S) +"\n" \
              +" then" +"\n" \
              +"  while " +str(Q) +" then" +"\n" \
              +"    " +str(S) +"\n" \
              +"  else " +"\n" \
              +"    " +str(T) +"\n" \
              +"  end" \
              +" end"
      return res

    def merge_rule_IF(self,S_evt_key,T_evt_key,S_chain,T_chain):
      """ merging rules: the IF rule. """
      assert S_evt_key in self.events.keys()
      assert T_evt_key in self.events.keys()

      # events S and T are to be merged
      S_evt = self.events[S_evt_key] # the first event
      T_evt = self.events[T_evt_key] # the second event
      #
      P_lbl_S = S_chain['P'] # the P label in event S
      Q_lbl = S_chain['Q'] # the Q label in event S
      #
      P_lbl_T = T_chain['P'] # the P label in event T
      not_Q_lbl = T_chain['~Q'] # the ~Q label in event T
      #
      P_S = S_evt.get_guard(P_lbl_S) # Z3 predicate
      Q = S_evt.get_guard(Q_lbl) # Z3 predicate
      #
      P_T = T_evt.get_guard(P_lbl_T) # Z3 predicate
      not_Q = T_evt.get_guard(not_Q_lbl) # Z3 predicate
      #
      S = S_evt.get_bassg()
      T = T_evt.get_bassg()
      #
      res = '\nwhen ' +str(P_S) +"\n" \
              +" then" +"\n" \
              +"  if " +str(Q) +" then" +"\n" \
              +"    " +str(S) +"\n" \
              +"  else " +"\n" \
              +"    " +str(T) +"\n" \
              +"  end" \
              +" end"
      return res



    """ proof obligations. """

    # proof obligation: guard strengthening in refinements
    # the EB Book, Section 5.2.2
    def evt_grd_GRD(self,concrete_evt_key):
      """
      proof obligation: concrete event guards must be stronger than abstract event guards. 
      """
      # checking that evt_key exists
      abstract_evt_key = self.ref_chain[concrete_evt_key]
      assert abstract_evt_key in self.abstract_machine.get_events().keys()
      assert concrete_evt_key in self.events.keys()

      concrete_evt = self.events[concrete_evt_key] # concrete event
      abstract_evt = self.abstract_machine.get_event(abstract_evt_key) # abstract event
      #
      abstract_guard = abstract_evt.get_zed_guards() # a Z3 predicate
      concrete_guard = concrete_evt.get_zed_guards() # a Z3 predicate
      #
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())
      A = And(axioms,ctx_theorems)

      abstract_invariants = conjunct_dict(self.get_abstract_machine().get_invariants())
      abstract_theorems = conjunct_dict(self.get_abstract_machine().get_theorems())
      I = And(abstract_invariants,abstract_theorems)

      concrete_invariants = conjunct_dict(self.get_invariants())
      concrete_theorems = conjunct_dict(self.get_theorems())
      J = And(concrete_invariants,concrete_theorems)

      # witness predicate
      W = conjunct_dict(self.events[concrete_evt_key].get_witnesses())

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(A,I,J,C,
                         concrete_guard,
                         W),abstract_guard)


    # proof obligation: guard strengthening in refinements
    # the EB Book, Section 5.2.2
    def evts_grd_GRD(self):
      """
      proof obligation: concrete event guards must be stronger than abstract event guards. 
      """
      po = And(True)
      if len(self.events):
        po = conjunct_lst([self.evt_grd_GRD(concrete_evt_key) for concrete_evt_key, evt in self.events.items()])
      return po


    # proof obligation: simulation proof obligation
    # the EB Book, Section 5.2.2
    def evt_act_SIM(self,concrete_evt_key):
      """ Proof obligation: simulation.  
      The execution of the concrete event does not contradict what the abstract event does. 
      """
      # checking that evt_key exists
      abstract_evt_key = self.ref_chain[concrete_evt_key]
      assert abstract_evt_key in self.abstract_machine.get_events().keys()
      assert concrete_evt_key in self.events.keys()

      concrete_evt = self.events[concrete_evt_key] # concrete event
      abstract_evt = self.abstract_machine.get_event(abstract_evt_key) # abstract event
      #
      concrete_ba = concrete_evt.get_bassg().get_ba() # concrete before-after predicate, a Z3 predicate
      concrete_v = concrete_evt.get_bassg().get_v() # variables involved in the concrete before-after predicate
      #
      abstract_ba = abstract_evt.get_bassg().get_ba() # abstract before-after predicate, a Z3 predicate
      abstract_v = abstract_evt.get_bassg().get_v() # variables involved in the abstract before-after predicate
      #
      concrete_guard = concrete_evt.get_zed_guards() # a Z3 predicate
      #
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())
      A = And(axioms,ctx_theorems)

      abstract_invariants = conjunct_dict(self.get_abstract_machine().get_invariants())
      abstract_theorems = conjunct_dict(self.get_abstract_machine().get_theorems())
      I = And(abstract_invariants,abstract_theorems)

      concrete_invariants = conjunct_dict(self.get_invariants())
      concrete_theorems = conjunct_dict(self.get_theorems())
      J = And(concrete_invariants,concrete_theorems)

      # witness predicate
      W = conjunct_dict(self.events[concrete_evt_key].get_witnesses())

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(A,I,J,C,
                         concrete_guard,
                         W,
                         concrete_ba),abstract_ba)


    # proof obligation: simulation proof obligation
    # the EB Book, Section 5.2.2
    def evts_act_SIM(self):
      """ Proof obligation: concrete event guards simulate abstract event guards. 
      """
      po = And(True)
      if len(self.events):
        po = conjunct_lst([self.evt_act_SIM(concrete_evt_key) for  concrete_evt_key, evt in self.events.items()])
      return po


    # proof obligation: numeric variant decreasing proof obligation
    # the EB Book, Section 5.2.2
    def evt_VAR(self,concrete_evt_key):
      """ Proof obligation: decreasing of numeric variant.
      Every convergent event decreases the numeric variant.  
      """
      concrete_evt = self.events[concrete_evt_key] # concrete event
      
      assert self.variant != None
      assert concrete_evt.get_status() == Status.Convergent # only convergent events should make progress

      concrete_guard = concrete_evt.get_zed_guards() # a Z3 predicate
      concrete_ba = concrete_evt.get_bassg().get_ba() # concrete before-after predicate, a Z3 predicate
      #
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())
      A = And(axioms,ctx_theorems)

      abstract_invariants = conjunct_dict(self.get_abstract_machine().get_invariants())
      abstract_theorems = conjunct_dict(self.get_abstract_machine().get_theorems())
      I = And(abstract_invariants,abstract_theorems)

      concrete_invariants = conjunct_dict(self.get_invariants())
      concrete_theorems = conjunct_dict(self.get_theorems())
      J = And(concrete_invariants,concrete_theorems)

      w = self.get_variables() # set of concrete machine variables
      n = self.get_variant() # machine variant
      n_w = get_vars(n) # set of variables in n
      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #

      assert n_w <= w | constants # elements in n_w are either machine variables or constants
      #
      n_w_asgs = [(w,prime(w)) for w in n_w] # replace w with w'
      n_primed = substitute(n,n_w_asgs) # perform substitutions in n
      modified_variant = n_primed < n

      return Implies(And(A,I,J,C,
                         concrete_guard,
                         concrete_ba),modified_variant)


    # proof obligation: machine variant decreases
    # the EB Book, Section 5.2.2
    def evts_VAR(self):
      """
      Proof obligation: Convergent events must decrease machine variants.
      """      
      po = And(True)

      if len(self.events) :
        events = list(filter(lambda concrete_evt_key: self.events[concrete_evt_key].get_status() == Status.Convergent, \
                        self.events.keys())) # filtering convergent events
                        
        if len(events):
          po = conjunct_lst([self.evt_VAR(evt_key) for evt_key in events])
      return po


    # proof obligation: witnesses are feasible.
    # the EB Book, Section 5.2.2
    def evt_WFIS(self,concrete_evt_key):
      """ Proof obligation: feasibility of event guard witnesses. """

      # checking that evt_key exists
      abstract_evt_key = self.ref_chain[concrete_evt_key]
      assert abstract_evt_key in self.abstract_machine.get_events().keys()
      assert concrete_evt_key in self.events.keys()

      concrete_evt = self.events[concrete_evt_key] # concrete event
      abstract_evt = self.abstract_machine.get_event(abstract_evt_key) # abstract

      concrete_guard = concrete_evt.get_zed_guards() # a Z3 predicate

      #
      axioms = conjunct_dict(self.get_context().get_axioms())
      ctx_theorems = conjunct_dict(self.get_context().get_theorems())
      A = And(axioms,ctx_theorems)

      abstract_invariants = conjunct_dict(self.get_abstract_machine().get_invariants())
      abstract_theorems = conjunct_dict(self.get_abstract_machine().get_theorems())
      I = And(abstract_invariants,abstract_theorems)

      concrete_invariants = conjunct_dict(self.get_invariants())
      concrete_theorems = conjunct_dict(self.get_theorems())
      J = And(concrete_invariants,concrete_theorems)

      # witness predicate
      W = conjunct_dict(self.events[concrete_evt_key].get_witnesses())
      x = abstract_evt.get_x()

      #
      constants = self.get_context().get_constants_set() # set of machine constants
      C = list(filter(lambda c: is_markable(c), constants)) # is_markable(c) if c is either a variable or a constant
      C = conjunct_lst([(prime(c) == c) for c in C]) # constants don't change from pre- to post-state
      #
      return Implies(And(A,I,J,C,
                         concrete_guard),Exists(x,W))


    # proof obligation: witnesses are feasible.
    # the EB Book, Section 5.2.2
    def evts_WFIS(self):
      """ Proof obligation: witnesses are feasible. """
      po = And(True)
      if len(self.events):
        events = list(filter(lambda concrete_evt_key: len(self.events[concrete_evt_key].get_witnesses())>0,\
                        self.events.keys())) # filtering events with a witness clause
        if len(events):
          po = conjunct_lst([self.evt_WFIS(concrete_evt_key) for  concrete_evt_key, evt in events])
      return po
