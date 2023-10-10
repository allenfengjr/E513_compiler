import os
import sys

sys.path.append('../E513_compiler')
sys.path.append('../E513_compiler/interp_x86')

import compiler
import interp_Lvar
import interp_Lif
import interp_Cif
import type_check_Lvar
import type_check_Lif
import type_check_Cif
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

typecheck_Lif = type_check_Lif.TypeCheckLif().type_check
typecheck_Cif = type_check_Cif.TypeCheckCif().type_check

typecheck_dict = {
    'source': typecheck_Lif,
    'remove_complex_operands': typecheck_Lif,
    'explicate_control': typecheck_Cif
}
interpLif = interp_Lif.InterpLif().interp
interpCif = interp_Cif.InterpCif().interp
interp_dict = {
    'shrink': interpLif,
    'remove_complex_operands': interpLif,
    'explicate_control': interp_Cif,
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

