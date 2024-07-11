from z3 import *

def is_markable(x):
  """ returns if x can change its value from pre- to post-state. """
  return (is_const(x) or is_var(x))


# It encodes x' as prime(x)
def prime(x):
  """ it represents the value of x in the next-state. """
  assert is_markable(x) # it checks if primed(x) exists
  s = x.sort()
  return Function("prime", s, s)(x)


# collects up all the variable from a formula f
# https://stackoverflow.com/questions/14080398/z3py-how-to-get-the-list-of-variables-from-a-formula
def get_vars(f):
  """ it collects and returns the variables of a formula. """
  r = set()
  def collect(f):
    if is_const(f):
        if f.decl().kind() == Z3_OP_UNINTERPRETED:
          r.add(f)
    else:
      for c in f.children():
        collect(c)
  collect(f)
  return r

def conjunct_lst(lst):
  """ returns the logical-and of the elements of a list. """

  res = And(True)
  if len(lst):
    res = And([l for l in lst])
  return res

def conjunct_dict(_dict):
  """ returns the logical-and of the members of a dictionary. """
  res = And(True)
  if len(_dict):
    res = And([pred for key,pred in _dict.items()])
  return res


from enum import Enum
Status = Enum('Status', ['Ordinary', 'Convergent', 'Anticipated'])
