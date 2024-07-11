from z3 import *

#from pyeb.lib.utils import *
from .utils import *

class BAssignment:
    """
    An EB action.
    """
    def __init__(self,v,ba):
      self.v = v # set of left-hand variables
      self.ba = ba # a before-after predicate in Z3

    """ getters. """

    def get_ba(self):
      """ It returns the before-after predicate. """
      return self.ba

    def get_v(self):
      """ It returns the set of left-hand side variables. """
      return self.v.copy()

    def __copy__(self):
      """ returns a copy of the self object.  """
      v = self.v.copy()
      ba = self.ba
      return BAssignment(v,ba)


    """ setters. """

    def __add__(self,bassg):
      """ definition of Python's + magic method. """
      left_hand = self.get_v().union(bassg.get_v())
      right_hand = And(self.get_ba(),bassg.get_ba())
      return BAssignment(left_hand,right_hand)

    def add_ba(self,bassg):
      """ It adds a before-after predicate clause. It calls __add__(bassg) on self. """
      self.ba = self.ba + bassg

    def __str__(self):
      """ string class representation. """
      res = str(self.v) + " := " + str(self.ba)
      return res
