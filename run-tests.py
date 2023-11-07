import os
import sys

sys.path.append('../E513_compiler')
sys.path.append('../E513_compiler/interp_x86')

import tuple
import interp_Ltup
import interp_Ctup
import type_check_Ctup
import type_check_Ltup
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = tuple.Compiler()

typecheck_Ltup = type_check_Ltup.TypeCheckLtup().type_check
typecheck_Ctup = type_check_Ctup.TypeCheckCtup().type_check
typecheck_dict = {
    'source': typecheck_Ltup,
    'shrink': typecheck_Ltup,
    'expose_allocation': typecheck_Ltup,
    'remove_complex_operands': typecheck_Ltup,
    'explicate_control': typecheck_Ctup,
}
interpLtup = interp_Ltup.InterpLtup().interp
interpCtup = interp_Ctup.InterpCtup().interp
interp_dict = {
    'shrink': interpLtup,
    'expose_allocation': interpLtup,
    'remove_complex_operands': interpLtup,
    'explicate_control': interpCtup,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

if True:
    run_tests('var', compiler, 'tup',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/var/zero.py',
                 'var',
                 compiler,
                 'var',
                 typecheck_dict,
                 interp_dict)

