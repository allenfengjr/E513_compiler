from ast import *
from ast import List, Module, expr, stmt
from math import floor
from utils import *
from utils import List, Module, expr, stmt
from x86_ast import *
from var import Temporaries
import tuples
import typing
from typing import List, Dict, Set
from graph import UndirectedAdjList
from register_allocator \
    import registers, registers_for_alloc, callee_save_for_alloc
import type_check_Ltup
import type_check_Ctup
import interp_Ltup
import interp_Ctup

class Compiler(tuples.Tuples):
    ###########################################################################
    # Shrink
    ###########################################################################
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, args, body, decorator_list, returns):
                new_body = [self.shrink_stmt(stmt) for stmt in body]
                return FunctionDef(name, args, new_body, decorator_list, returns)
            case Return(value):
                return Return(self.shrink_exp(value))
            case _:
                # Handle other statement types if necessary
                return super().shrink_stmt(s)
            
    ###########################################################################
    # Reveal Functions
    ###########################################################################
    # record arity of the function
    function_arity_map = {}
    def reveal_functions(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module([self.reveal_function_stmt(s) for s in body])

    def reveal_function_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, args_obj, body, _, returns, _):
                self.function_arity_map[name] = len(args_obj)
                new_body = [self.reveal_function_stmt(stmt) for stmt in body]
                return FunctionDef(name, args_obj, new_body, None, returns, None)
            case Expr(value):
                return Expr(self.reveal_function_exp(value))
            case Return(value):
                return Return(self.reveal_function_exp(value))
            case _:
                return s
                # raise Exception('reveal_function_stmt: unexpected ' + repr(s))

    def reveal_function_exp(self, e: expr) -> expr:
        match e:
            case Name(id):
                if id in self.function_arity_map:
                    return FunRef(id, self.function_arity_map[id])
                else:
                    return e
            case Call(func, args):
                new_func = self.reveal_function_exp(func)
                new_args = [self.reveal_function_exp(arg) for arg in args]
                return Call(new_func, new_args)
            case _:
                return e
                # raise Exception('reveal_function_exp: unexpected ' + repr(e))

    ###########################################################################
    # Limit Functions
    ###########################################################################
    def limit_functions(self, p: Module) -> Module:
        match p:
            case Module(body):
                return Module([self.limit_function_stmt(s) for s in body])

    def limit_function_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, args_obj, body, _, returns, _):
                if len(args_obj) > 6:
                    # Update arguments

                    # THERE is a bug about the type of "args_obj"
                    # SHOULD be a 'argument', now is a 'list'
                    new_args = args_obj[:5]
                    rest_args = args_obj[5:]
                    tuple_arg = arg('tup', TupleType([annotation for _, annotation in rest_args]))
                    new_args.append(tuple_arg)

                    # Update body
                    new_body = [self.limit_function_stmt_in_body(stmt, rest_args) for stmt in body]
                    return FunctionDef(name, new_args, new_body, None, returns, None)
                else:
                    new_body = [self.limit_function_stmt(stmt) for stmt in body]
                    return FunctionDef(name, args_obj, new_body, None, returns, None)
            case _:
                return s  # Other statements remain unchanged

    def limit_function_stmt_in_body(self, s: stmt, rest_args: List[arg]) -> stmt:
        match s:
            case Return(value):
                return Return(self.limit_function_exp(value, rest_args))
            case Expr(value):
                return Expr(self.limit_function_exp(value, rest_args))
            # Add other cases as needed
            case _:
                return s

    def limit_function_exp(self, e: expr, rest_args: List[arg]) -> expr:
        match e:
            case Name(id):
                for i, arg in enumerate(rest_args):
                    if arg.arg == id:
                        return Subscript(Name('tup'), Constant(i), Load())
                return e
            case Call(func, args):
                if len(args) > 6:
                    new_args = args[:5] + [Tuple(args[5:], Load())]
                    return Call(self.limit_function_exp(func, rest_args), new_args)
                else:
                    return Call(self.limit_function_exp(func, rest_args), args)
            # Add other cases as needed
            case _:
                return e
            
    ###########################################################################
    # Expose Allocation
    ###########################################################################
    def expose_alloc_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, args, body, decorator_list, returns, type_comment):
                new_body = [self.expose_alloc_stmt(stmt) for stmt in body]
                return FunctionDef(name, args, new_body, decorator_list, returns, type_comment)
            case Return(value):
                return Return(self.expose_alloc_exp(value))
            case _:
                return super().expose_alloc_stmt(s)

    ###########################################################################
    # RCO
    ###########################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case FunRef(name, arity):
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, [(tmp, e)])
                else:
                    return (e, [])
            case Call(func, args):
                new_args = []
                temporaries = []
                for arg in args:
                    new_arg, temps = self.rco_exp(arg, True)
                    new_args.append(new_arg)
                    temporaries.extend(temps)
                new_e = Call(func, new_args)
                if need_atomic:
                    tmp = Name(generate_name('tmp'))
                    return (tmp, temporaries + [(tmp, new_e)])
                else:
                    return (new_e, temporaries)
            # Handle other cases as needed
            case _:
                return super().rco_exp(e, need_atomic)

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case FunctionDef(name, args, body, _, returns, _):
                new_body = [stmt for b in body for stmt in self.rco_stmt(b)]
                return [FunctionDef(name, args, new_body, None, returns, None)]
            case Return(value):
                new_value, temporaries = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in temporaries] + [Return(new_value)]
            # Handle other cases as needed
            case _:
                return super().rco_stmt(s)

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                new_body = [stmt for b in body for stmt in self.rco_stmt(b)]
                return Module(new_body)
            
    ############################################################################
    # Explicate Control
    ############################################################################
    def explicate_assign(self, e: expr, x: Variable, cont: List[stmt],
                         basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e: 
            case Call(func, args):
                return [Assign([x], Call(func, args))] + cont
            case FunRef(name, arity):
                return [Assign([x], FunRef(name, arity))] + cont
            case _:
                return super().explicate_assign(e, x, cont, basic_blocks)

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Call(func, args):
                return [If(Call(func, args), self.create_block(thn, basic_blocks), self.create_block(els, basic_blocks))]
            case _:
                return super().explicate_pred(cnd, thn, els, basic_blocks)
            
    def explicate_tail(self, e: expr, basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Call(func, args):
                return [TailCall(func, args)]
            case IfExp(test, body, orelse):
                goto_body = self.create_block(self.explicate_tail(body, basic_blocks), basic_blocks)
                goto_orelse = self.create_block(self.explicate_tail(orelse, basic_blocks), basic_blocks)
                return self.explicate_pred(test, goto_body, goto_orelse, basic_blocks)
            case Begin(body, result):
                ss = self.explicate_tail(result, basic_blocks)
                for s in reversed(body):
                    ss = self.explicate_stmt(s, ss, basic_blocks)
                return ss
            case _:
                return self.explicate_effect(e, [Return(Constant(0))], basic_blocks) # recursively find the subexpression?
            
    def process_function_def(self, fdef: FunctionDef, basic_blocks: Dict[str, List[stmt]]) -> FunctionDef:
        new_body = []
        for s in reversed(fdef.body):
            new_body = self.explicate_stmt(s, new_body, basic_blocks)
        label = label_name(fdef.name)
        basic_blocks[label] = new_body
        return FunctionDef(label, fdef.args, basic_blocks, return_type=fdef.returns)
    
    def explicate_stmt(self, s: stmt, cont, basic_blocks):
        match s:
            case FunctionDef(name, params, body, dl, returns, comment):
                # Process the function definition and its body
                # processed_fdef = self.process_function_def(s, basic_blocks)
                new_body = []
                for stmt in reversed(body):
                    new_body = self.explicate_stmt(stmt, new_body, basic_blocks)
                # Create a new FunctionDef with the processed body
                return [FunctionDef(name, params, new_body, dl, returns, comment)] + cont
                # return [processed_fdef] + cont
            
            case Return(value):
                return self.explicate_tail(value, basic_blocks) + cont
            
            case _:
                return super().explicate_stmt(s, cont, basic_blocks)
            
    def explicate_control(self, p: Module) -> CProgramDefs:
        match p:
            case CProgramDefs(defs):
                basic_blocks = {}
                new_defs = [self.process_function_def(fdef, basic_blocks) for fdef in defs]
                return CProgramDefs(new_defs)
            case _:
                return super().explicate_control(p)
            
    ###########################################################################
    # Select Instructions
    ###########################################################################
    arg_registers: List[str] = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
    
    def select_stmt(self, s: stmt) -> List[instr]:
        match s: 
            case Assign([lhs], Call(func, args)):
                instrs = []
                for arg, reg in zip(args, self.arg_registers[:len(args)]):
                    instrs.append(Instr('movq', [self.select_arg(arg), Reg(reg)]))
                instrs.append(IndirectCallq(self.select_arg(func), len(args)))
                instrs.append(Instr('movq', [Reg('rax'), self.select_arg(lhs)]))
            case TailCall(func, args):
                instrs = []
                for arg, reg in zip(args, self.arg_registers[:len(args)]):
                    instrs.append(Instr('movq', [self.select_arg(arg), Reg(reg)]))
                instrs.append(TailJump(self.select_arg(func), len(args)))
                return instrs
            case Assign([lhs], FunRef(name, arity)):
                return [Instr('leaq', [Global(name), self.select_arg(lhs)])]
            case _:
                return super().select_stmt(s)
    
    def process_func_def(self, fdef: FunctionDef) -> FunctionDef:
        # Create start and conclusion blocks for the function
        start_label = f"{fdef.name}_start"
        conclusion_label = f"{fdef.name}_conclusion"
        blocks = {start_label: [], conclusion_label: [Instr('retq', [])]}
        # Move arguments to local variables
        for i, param in enumerate(fdef.params):
            arg_reg = self.arg_registers[i]
            local_var = param[0]
            blocks[start_label].append(Instr('movq', [Reg(arg_reg), Reg(local_var)]))
        
        # Add the rest of the blocks
        for label, block in fdef.blocks.items():
            if label != 'start':
                blocks[label] = block
            else:
                blocks[start_label].extend(block)
        return FunctionDef(fdef.name, [], blocks, return_type=fdef.returns)
    
    def select_instructions(self, p: CProgramDefs) -> X86ProgramDefs:
        match p:
            case CProgramDefs(defs):
                new_defs = [self.process_func_def(def_) for def_ in defs]
                return X86ProgramDefs(new_defs)
            case _:
                return super().select_instructions(p)
    
    ###########################################################################
    # Uncover Live
    ###########################################################################
    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case IndirectCallq(func, arity):
                read = {func}.union(set(Reg(r) for r in self.arg_registers[:arity]))
                return read
            case TailJump(func, arity):
                read = {func}.union(set(Reg(r) for r in self.arg_registers[:arity]))
                return read
            case _:
                return super().vars_arg(a)
            
    callee_save: Set[str] = {'rsp', 'rbp', 'rbx', 'r12', 'r13', 'r14', 'r15'}
    
    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case IndirectCallq(func, arity):
                write = set(Reg(r) for r in self.callee_save)
                return write
            case TailJump(func, arity):
                return set()
            case _:
                return super().write_vars(i)
            
    ###########################################################################
    # Build Interference
    ###########################################################################
    
    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86ProgramDefs(defs):
                graphs = {}
                for func_def in defs:
                    live_after = self.uncover_live(func_def)
                    graph = self.build_interference_blocks(func_def.blocks, live_after)
                    graphs[func_def.name] = graph
                return super().build_interference(p, live_after)
    
    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                    live_after: Dict[instr, Set[location]]):
        match i: 
            case Callq(func, arity) | IndirectCallq(func, arity):
                live_vars = live_after[i]
                for v in live_vars:
                    if self.is_root_type(self.var_types[v.id]):
                        for u in callee_save_for_alloc:
                            graph.add_edge(Reg(u), v)
                    for d in self.write_vars(i):
                        if v != d:
                            graph.add_edge(d, v)
                super().interfere_instr(i, graph, live_after)
            case _:
                super().interfere_instr(i, graph, live_after)
                
    ###########################################################################
    # Allocate Registers
    ###########################################################################
    
    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86ProgramDefs(defs):
                new_defs = []
                for func_def in defs:
                    graph = self.build_interference(func_def)
                    new_blocks, used_callee, num_callee, stack_spills, root_spills = \
                    self.alloc_reg_blocks(func_def.blocks, graph, func_def.var_types)
                    new_def = FunctionDef(func_def.name, new_blocks, ...)
                    new_defs.append(new_def)
                return super().allocate_registers(p, graph)
            
    ############################################################################
    # Patch Instructions
    ############################################################################
    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case Instr('leaq', [s, t]) if not isinstance(t, Reg):
            # Ensure destination of 'leaq' is a register
                return [Instr('leaq', [s, Reg('rax')]), Instr('movq', [Reg('rax'), t])]
            case TailJump(func, arity) if arg != Reg('rax'):
                return [Instr('movq', [arg, Reg('rax')]), TailJump(Reg('rax'), arity)]
            case _:
                return super().patch_instr(i)
            
    ############################################################################
    # Prelude and Conclusion
    ############################################################################
    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                new_body = {}
                for label, instrs in body.items():
                    # Check if this is a function definition or main
                    if label.endswith('_start'):
                        function_name = label[:-6]  # Remove '_start' suffix to get the function name
                        save_callee_reg = [Instr('pushq', [Reg(r)]) for r in p.used_callee]
                        restore_callee_reg = [Instr('popq', [Reg(r)]) for r in reversed(p.used_callee)]
                        prelude = ([Instr('pushq', [Reg('rbp')]), 
                                    Instr('movq', [Reg('rsp'), Reg('rbp')])] 
                                    + save_callee_reg 
                                    + [Instr('subq', [Immediate(p.stack_space), Reg('rsp')])])
                        conclusion = ([Instr('addq', [Immediate(p.stack_space), Reg('rsp')])] 
                                    + restore_callee_reg 
                                    + [Instr('popq', [Reg('rbp')]),
                                    Instr('retq', [])])
                        if function_name == 'main':
                            rootstack_size = 2 ** 16
                            heap_size = 2 ** 4
                            initialize_heaps = \
                                [Instr('movq', [Immediate(rootstack_size), Reg('rdi')]), 
                                Instr('movq', [Immediate(heap_size), Reg('rsi')]),
                                Callq(label_name('initialize'), 2),
                                Instr('movq', [Global(label_name('rootstack_begin')),
                                                Reg('r15')])]
                            prelude += initialize_heaps
                        new_body[function_name + '_prelude'] = prelude
                        new_body[label] = instrs
                        new_body[function_name + '_conclusion'] = conclusion
                    else:
                        new_body[label] = instrs
                return X86Program(new_body)