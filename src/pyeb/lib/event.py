from z3 import *

#from pyeb.lib.utils import *
from .utils import *
from .assignment import *

class BEvent:
    """
    It encodes an event in Python.
    """

    def __init__(self,evtname,status,x,grds,bassg):
      """ Class constructor, event name = any x where grd then ba end. """
      self.evtname = evtname
      self.status = status # event status
      self.x = x.copy()    # list of guard variables
      self.guards = grds.copy()  # dictionary of guards
      self.bassg = copy.copy(bassg) # BAssignment
    def __copy__(self):
      """ returns a copy of the self object.  """
      return BEvent(self.evtname,self.status, self.x.copy(), self.guards.copy(), copy.copy(self.bassg))


    """ getters """
    def get_name(self):
      """ returns the event name.  """
      return self.evtname

    def get_x(self):
      """ returns the event parameters. """
      return self.x.copy()

    def get_guards(self):
      """ returns the event guards as a dictionary. """
      return self.guards

    def get_zed_guards(self):
      """ returns the event guards as a Z predicate. """
      return conjunct_dict(self.guards)

    def get_guard(self, grd_key):
      """ returns a particular event guard. """
      return self.guards[grd_key]

    def get_bassg(self):
      """ returns the Event-B assignment. """
      return self.bassg

    def get_status(self):
      """ returns the event status. """
      return self.status


    """ setters """

    def set_name(self, name):
      """ it sets the event name. """
      self.evtname = name

    def add_guard(self, grd_key, grd):
      """ it adds a fresh event guard. """
      self.guards[grd_key] = grd

    def add_guards(self, dict):
      """ it adds a dictionary of event guards. """
      for grd_key, grd in dict.items() :
        self.guards[grd_key] = grd

    def set_bassg(self,bassg):
      """ it sets self.bassg. """
      self.bassg = bassg

    def add_bassg(self,bassg):
      """ it sets self.bassg . """
      self.bassg = self.bassg + bassg

    def add_var(self,k):
      """ it adds an event parameter. """
      self.x.append(k)

    def add_vars(self,*y):
      """ it adds a tuple of event parameters. """
      self.x.extend(y)

    def del_var(self,k):
      """ it deletes an event parameter. """
      self.x.remove(k)

    def set_status(self,s):
      """ it returns the event status. """
      self.status = s
      
    def __str__(self):
        """ string class representation. """
        res = self.evtname + " = " + str(self.status) +"\n"
        if len(self.x):
          res = ''.join(map(str,self.x))
          res = "any" + res +"\n"
        g = str(self.get_guards())
        res = res + "where " + g +"\n"
        if len(self.get_bassg().get_v()):
          res = res + "then" +"\n"
          res = res + str(self.bassg) +"\n"
        res = res + "end" +"\n"
        return res

    
class BEventRef(BEvent):
    """
    Event refinement.
    """

    # event = any x where grd then bassg end
    def __init__(self,evt_name,abs_evt):
      """ Class constructor. It takes two arguments, namely, the name of the refinement event,
      and the abstract event. """
      super().__init__(evt_name,Status.Ordinary,abs_evt.get_x(),abs_evt.get_guards().copy(),abs_evt.get_bassg())
      self.abstract_event = abs_evt # reference to the abstract event
      self.witnesses = {} # dictionary of witness clauses


    """ getters. """

    def get_abstract_event(self):
      """ It returns the abstract event. """
      return self.abstract_event

    def get_witness(self,k):
      """ It returns the event witness for k. """
      return self.witnesses[k]

    def get_witnesses(self):
      """ It returns the dictionary of event witnesses. """
      return self.witnesses


    """ setters. """

    def set_abstract_event(self,abs_evt):
      """ It sets the abstract event. """
      self.abstract_event = abs_evt

    def add_witness(self,k,witness):
      """ It adds a witness for a disappearing event variable k. """
      self.witness[k] = witness
      self.del_x(k) # it deletes variable k from the list of event variables
      self.ba = substitute(self.ba, (k,witness)) # it replaces k with the witness in self.ba
