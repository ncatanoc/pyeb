from z3 import *

import argparse
import sys, re

from pyeb.lib.machine import *
#
from antlr4 import *
from pyeb.poporo_translator.Python3Lexer import Python3Lexer
from pyeb.poporo_translator.Python3Parser import Python3Parser
from pyeb.poporo_translator.Python3ParserVisitor import Python3ParserVisitor
from pyeb.poporo_translator.translator import translator
#

def test_initialisation_invs_INV(__machine__):
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
    
    
def test_evts_invs_INV(__machine__):
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
    
    
def test_evts_acts_FIS(__machine__):
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
    
    
def test_thms_THM(__machine__):
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
    
    
def test_evts_grd_GRD(__machine__):
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
    
    
def test_evts_act_SIM(__machine__):
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
    
    
def test_evts_VAR(__machine__):
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
    
    
def test_evts_WFIS(__machine__):
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'python_file',
        help='Python file to verify')

    args = parser.parse_args()

    file_name = args.python_file
    input_stream = FileStream(file_name)
    lexer = Python3Lexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = Python3Parser(stream)
    tree = parser.file_input()
    #
    if parser.getNumberOfSyntaxErrors() > 0:
        print("syntax errors")
    else:
        t = translator()
        obj_file_txt, obj_dict = t.visit(tree)

        # we write the object code produced by the traslator t into
        # an file_name_obj.py file
        obj_file_name =  file_name.replace('.py','_obj.py')
        with open(obj_file_name, 'w') as file:
            file.write(obj_file_txt)

        # we load/run the code in the file_name_obj module
        # which is then used to calculate the proof obligations
        # of the file_name_oo.py program
        module_name = obj_file_name.replace('/','.').replace('.py','')
        sys.path.insert(0,'.')
        __import__(module_name)
        mod = sys.modules[module_name]

        __machine__ = mod.__machine__

        for class_name , obj in obj_dict.items():
            __machine__ == obj
            pattern = r'\w+ref\d+'
            if re.match(pattern,class_name):
                pattern1 = r'\w+ref0' 
                if re.match(pattern1,class_name):  # abstract machine proof obligations  
                    print('--- Proof obligations for ', class_name, '---')
                    test_evts_invs_INV(__machine__)
                    test_evts_acts_FIS(__machine__)
                    test_thms_THM(__machine__)
                else:  # refinement machine proof obligations 
                    print('--- Proof obligations for ', class_name, '---')
                    test_initialisation_invs_INV(__machine__)
                    test_evts_invs_INV(__machine__)
                    test_evts_acts_FIS(__machine__)
                    test_thms_THM(__machine__)
                    test_evts_grd_GRD(__machine__)
                    test_evts_act_SIM(__machine__)
                    test_evts_VAR(__machine__)    
                    test_evts_WFIS(__machine__)        
    
if __name__ == '__main__':
    main()
