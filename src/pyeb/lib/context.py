from z3 import *

#from pyeb.lib.utils import *
from .utils import *
from .assignment import *
from .event import *

class BContext:
    """
    Event-B machine context.
    """

    def __init__(self):
      """ class constructor. """
      self.constants = {} # dictionary of machine constants
      self.axioms = {} # dictionary of axioms
      self.theorems = {} # dictionary of theorems

    def __copy__(self):
      """ returns a copy of the self object. """
      obj = BContext()
      obj.add_constants(self.get_constants().copy())
      obj.add_axioms(self.get_axioms().copy())
      obj.add_theorems(self.get_theorems().copy())
      return obj

    """ getters """

    def get_axioms(self):
      """ it returns a copy of the dictionary of axioms. """
      return self.axioms.copy()

    def get_theorems(self):
      """ it returns a copy of the dictionary of theorems. """
      return self.theorems.copy()

    def get_constant(self,key):
      """ it returns a constant in the dictionary of constants. """
      assert key in self.constants.keys()
      return self.constants[key]

    def get_constants(self):
      """ it returns a copy of the dictionary of constants. """
      return self.constants.copy()

    def get_constants_set(self):
      """ it returns a copy of the dictionary of constants as a set. """
      dict = self.constants.copy()     
      arr = []
      for key in dict:
        arr.append(dict[key])
      res = set(arr)    
      return res

    """ setters """
    def add_constant(self,key,c):
      """ it adds a constant to the context. """
      self.constants[key] = c

    def add_constants(self,constants):
      """ it adds a dictionary of constants to the context. """
      for cnt_key, cnt in constants.items():
        self.add_constant(cnt_key,cnt)

    # def add_constants(self,*constants):
    #   """ it adds a tuple of constants to the context. """
    #   for c in constants:
    #     self.constants.add(c)

    # def add_constants_set(self,s):
    #   """ it adds a set of constants to the context. """
    #   for c in s:
    #     self.constants.add(c)

    def add_axiom(self,axm_key,axm):
      """ it adds an axiom to the context. """
      self.axioms[axm_key] = axm

    def add_axioms(self,axioms):
      """ it adds a dictionary of axioms to the context. """
      for axm_key, axm in axioms.items():
        self.add_axiom(axm_key,axm)

    def add_theorem(self,th_key,th):
      """ it adds a theorem to the context. """
      self.theorems[th_key] = th

    def add_theorems(self,theorems):
      """ it adds a dictionary of theorems to the context. """
      for th_key,th in theorems.items():
        self.add_theorem(th_key,th)

    # Context theorem proof obligation
    # the EB Book, Section 5.2.2
      """ Proof obligation: context theorem proof-obligation. """
    def thm_THM(self,th_key):
      # checking that th_key is a valid theorem
      theorems_dict = self.get_theorems()
      assert th_key in theorems_dict.keys()

      th = self.theorems[th_key]
      theorems_dict.pop(th_key)

      axioms = conjunct_dict(self.get_axioms())
      theorems = conjunct_dict(theorems_dict)

      return Implies(And(axioms,theorems),th)

    # Context theorem proof obligation
    # the EB Book, Section 5.2.2
    def thms_THM(self):
      """ Proof obligation: context theorem proof-obligation. """
      po = And(True)
      if len(self.get_theorems()):
        po = conjunct_lst([self.thm_THM(th_key) for  th_key, th in self.get_theorems().items()])
      return po

      
    def __str__(self):
        """ string class representation. """
        res = str(self.constants)
        return res
