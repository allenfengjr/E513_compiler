import cond
from ast import *
from utils import *
from x86_ast import *
from graph import UndirectedAdjList, DirectedAdjList, transpose, topological_sort
import var
from var import Temporaries
import register_allocator
from register_allocator import byte_to_full_reg
import sys
import os
from typing import List, Dict, Set, Tuple
import interp_Lif
import type_check_Lif
import interp_Cif
import type_check_Cif
from eval_x86 import interp_x86

class Loop(cond.Conditionals):
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case While(test, body, orelse):
                return If(self.shrink_exp(test),
                          [self.shrink_stmt(s) for s in body],
                          [self.shrink_stmt(s) for s in orelse])
            case _:
                return super().shrink_stmt(s)
            
    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case While(test, body, orelse):
                (test, bs) = self.rco_exp(test, False)
                sss1 = [self.rco_stmt(s) for s in body]
                sss2 = [self.rco_stmt(s) for s in orelse]
                return self.gen_assigns(bs) + \
                       [If(test, sum(sss1.append(self.gen_assigns(bs)), []), sum(sss2, []))]
            case _:
                return super().rco_stmt(s)