# Language L_Tuple

# Concrete Syntax

# stmt ::= ... | `while` exp `:` stmt+

# Abstract Syntax

#  stmt ::= ... | While(exp, stmt+, [])

from ast import *
from ast import Dict, List, Tuple, expr, stmt
from utils import *
from utils import Dict, List, expr, stmt
from var import Temporaries
from x86_ast import *
import cond
import loop
from dataflow_analysis import analyze_dataflow
from typing import List, Dict, Set
from typing import Tuple as Tup
from graph import DirectedAdjList, transpose
import type_check_Lwhile
import interp_Lwhile
import interp_Cif
import type_check_Cwhile
from eval_x86 import interp_x86
from x86_ast import Variable

class Compiler(loop.WhileLoops):
    
    ############################################################################
    # Shrink: No new stmt, just use previous `shrink`
    ############################################################################
    def shrink_exp(self, e: expr) -> expr:
        match e:
            case Tuple(elts, Load()):
                # elts: list[expr] ctx: expr_context
                exprs = [self.shrink_exp(i) for i in elts]
                return Tuple(exprs, Load())
            case Subscript(value, slice, Load()):
                # value: expr slice: _Slice
                v = self.shrink_exp(value)
                return Subscript(v, slice, Load())
            case _:
                return super().shrink_exp(e)
    
    ############################################################################
    # Expose Allocation
    ############################################################################\

    def expose_allocation(self, p: Module):
        # Transform the program to make allocations explicit
        new_stmts = []
        # new_stmts.append(Call(Name('initialize'), [rootstack_size, heap_size]))
        for stmt in p.body:
            new_stmts.append(self.expose_alloc_stmt(stmt))
        return Module(new_stmts)
    
    def expose_alloc_stmt(self, s:stmt):
        match s:
            case Assign(targets, value):
                return Assign([self.expose_alloc_exp(i) for i in targets], self.expose_alloc_exp(value))
            case Expr(Call(Name('print'),exps)):
                return Expr(Call(Name('print'),[self.expose_alloc_exp(i) for i in exps]))
            case Expr(exp):
                return Expr(self.expose_alloc_exp(exp))
            case If(test, body, orelse):
                return If(self.expose_alloc_exp(test),
                          [self.expose_alloc_stmt(i) for i in body],
                          [self.expose_alloc_stmt(i) for i in orelse])
            case While(test, body, orelse):
                return While(self.expose_alloc_exp(test),
                          [self.expose_alloc_stmt(i) for i in body],
                          [self.expose_alloc_stmt(i) for i in orelse])
            case _:
                raise("No such a stmt")
    
    def expose_alloc_exp(self, e):
        match e:
            case Tuple(es, Load()):
                temp_vars = []
                init_stmts = []
                # Step 1: Create temporary variables for initializing expressions
                for exp in es:
                    temp_var = Name(generate_name('init'))
                    temp_vars.append(temp_var)
                    init_stmts.append(Assign([temp_var], exp))

                # Step 2: Call to collect
                len_tuple = len(es)
                bytes_needed = 8 + len_tuple * 8  # 8 bytes for the tag + len * 8 bytes for elements
                '''
                need to check if need collect, 
                if need, call collect, else just move free_ptr forward,
                I personally think Allocate will move free_ptr
                I finally understand why in c, I can not write code like `int arr[num]`, because I must know
                `num` at compile time, rather than runtime.
                '''
                test_exp = Compare(BinOp(GlobalValue("free_ptr"), Add(), Constant(bytes_needed)), [GtE()], [GlobalValue("fromspace_end")])
                collect_call = Collect(size=bytes_needed)
                # ptr_update = Assign([GlobalValue("free_ptr")], Add(GlobalValue("free_ptr"), Immediate(bytes_needed)))
                init_stmts.append(If(test_exp, [collect_call], [Expr(Constant(0))]))

                # Step 3: Call to allocate
                tuple_type = e.has_type  # Assuming this is set by the has_type
                alloc_var = Name(generate_name('alloc'))
                init_stmts.append(Assign([alloc_var], Allocate(length=len_tuple, ty=tuple_type)))
                # Step 4: Initialize the tuple
                for i, temp_var in enumerate(temp_vars):
                    init_stmts.append(Assign([Subscript(alloc_var, Constant(i), Store())], temp_var))

                # Combine all the statements
                return Begin(init_stmts, alloc_var)
            case Subscript(exp, index, ctx):
                return Subscript(self.expose_alloc_exp(exp), index, ctx)
            case _:
                # Handle other statements that do not involve tuple creation
                return e



    ############################################################################
    # Remove Complex Operands: After Expose Allocation, there is no Tuple, but only Allocate&Collect
    ############################################################################
    def rco_exp(self, e: expr, need_atomic: bool) -> Tup[expr, Temporaries]:
        match e:
            case GlobalValue(name):
                # GlobalValue is already atomic, but if we need an atomic context, we must assign it to a temporary variable
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, [(tmp, GlobalValue(name))]
                else:
                    return GlobalValue(name), []
            case Allocate(length, ty):
                # Allocate is already atomic, but if we need an atomic context, we must assign it to a temporary variable
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, [(tmp, Allocate(length, ty))]
                else:
                    return Allocate(length, ty), []
            case Subscript(exp, idx, Load()):
                # Both exp and idx must be atomic
                (rco_sub, tmp_exp) = self.rco_exp(exp, True)
                (rco_idx, tmp_idx) = self.rco_exp(idx, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, tmp_exp + tmp_idx + [(tmp, Subscript(rco_sub, rco_idx, Load()))]
                else:
                    return Subscript(rco_sub, rco_idx, Load()), tmp_exp + tmp_idx
            case Call(Name('len'), [exp]):
                # The expression for len must be atomic
                (rco_len, tmp_exp) = self.rco_exp(exp, True)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return tmp, tmp_exp + [(tmp, Call(Name('len'), [rco_len]))]
                else:
                    return Call(Name('len'), [rco_len]), tmp_exp
            case _:
                return super().rco_exp(e, need_atomic)

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Collect(size):
                # Collect is already a statement and doesn't need transformation
                return [Collect(size)]
            case _:
                return super().rco_stmt(s)


    ############################################################################
    # Explicate Control
    ############################################################################
    def explicate_assign(self, e: expr, x: Variable, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Tuple(es, Load()):
                pass
            case _:
                return super().explicate_assign(e, x, cont, basic_blocks)
    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Collect(size):
                pass
            case _:
                return super().explicate_stmt(s, cont, blocks)

    ############################################################################
    # Uncover Live
    ############################################################################

    def uncover_live_block(self, label : str,
                           ss : List[stmt],
                           live : Set[location],
                           live_before : Dict[instr, Set[location]],
                           live_after : Dict[instr, Set[location]]) -> Set[location]:
        for i in reversed(ss):
            self.uncover_live_instr(i, live, live_before, live_after)
            live = live_before[i]
        return live

    # This is a method so it can be overridden (e.g. in functions.py)
    def liveness_transfer(self, blocks : Dict[str, List[instr]],
                          cfg : DirectedAdjList,
                          live_before : Dict[instr, Set[location]],
                          live_after : Dict[instr, Set[location]]) -> Set[location]:
        def live_xfer(label, live_before_succ):
            if label == label_name('conclusion'):
                return {Reg('rax'), Reg('rsp')}
            else:
                return self.uncover_live_block(label, blocks[label], live_before_succ,
                                               live_before, live_after)
        return live_xfer

    def uncover_live_blocks(self, blocks):
        live_before = {}
        live_after = {}
        cfg = self.blocks_to_graph(blocks)
        transfer = self.liveness_transfer(blocks, cfg, live_before, live_after)
        bottom = set()
        join = lambda s, t: s.union(t)
        # liveness is a backward analysis, so we transpose the CFG
        analyze_dataflow(transpose(cfg), transfer, bottom, join)
        return live_before, live_after
    
    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(blocks):
                (live_before, live_after) = self.uncover_live_blocks(blocks)
                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after
                
