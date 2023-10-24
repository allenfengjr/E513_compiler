import os
import sys

sys.path.append('../E513_compiler')
sys.path.append('../E513_compiler/interp_x86')

import compiler
import interp_Lvar
import interp_Lwhile
import interp_Cif
import type_check_Lvar
import type_check_Lwhile
import type_check_Cif
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

typecheck_Lwhile = type_check_Lwhile.TypeCheckLwhile().type_check
typecheck_Cif = type_check_Cif.TypeCheckCif().type_check
typecheck_dict = {
    'source': typecheck_Lwhile,
    'shrink': typecheck_Lwhile,
    'uniquify': typecheck_Lwhile,
    'remove_complex_operands': typecheck_Lwhile,
    'explicate_control': typecheck_Cif,
}
interpLwhile = interp_Lwhile.InterpLwhile().interp
interpCif = interp_Cif.InterpCif().interp
interp_dict = {
    'shrink': interpLwhile,
    'uniquify': interpLwhile,
    'remove_complex_operands': interpLwhile,
    'explicate_control': interpCif,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
}

if True:
    run_tests('var', compiler, 'if',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/var/zero.py',
                 'var',
                 compiler,
                 'var',
                 typecheck_dict,
                 interp_dict)

