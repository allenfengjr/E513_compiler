import ast
from ast import *
from utils import *
from x86_ast import *
import arrays
import typing
from typing import List, Dict, Set
from var import Temporaries
from register_allocator import arg_registers, caller_save_for_alloc, \
    registers, callee_save_for_alloc
from graph import UndirectedAdjList
import type_check_Lfun
import type_check_Cfun
import interp_Lfun
import interp_Cfun

class Functions(arrays.Arrays):

    '''
    The first two resolve
    '''

    ###########################################################################
    # Type-based Resolution
    ###########################################################################

    def resolve_exp(self, e: expr) -> expr:
      match e:
        case FunRef(name, arity):
          return FunRef(name, arity)
        case _:
          return super().resolve_exp(e)

    
    def resolve_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, params, body, _, returns, _):
                new_body = [self.resolve_stmt(s) for s in body]
                return FunctionDef(name, params, new_body, None, returns, None)
            case Return(value):
                return Return(self.resolve_exp(value))
            case _:
                return super().resolve_stmt(s)
    
    ###########################################################################
    # Bounds Checking
    ###########################################################################

    def check_bounds_exp(self, e: expr) -> expr:
      match e:
        case FunRef(name, arity):
          return FunRef(name, arity)
        case _:
          return super().check_bounds_exp(e)
    
    def check_bounds_stmt(self, s: stmt) -> stmt:
        match s:
          case FunctionDef(name, params, body, _, returns, _):
              new_bodys = [self.check_bounds_stmt(s) for s in body]
              return [FunctionDef(name, params, sum(new_bodys, []), None,
                                  returns, None)]
          case Return(value):
              return [Return(self.check_bounds_exp(value))]
          case _:
              return super().check_bounds_stmt(s)
            
    ############################################################################
    # Shrink
    ############################################################################
    
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, params, body, _, returns, _):
                new_body = [self.shrink_stmt(s) for s in body]
                return FunctionDef(name, params, new_body, None, returns, None)
            case Return(value):
                return Return(self.shrink_exp(value))
            case _:
                return super().shrink_stmt(s)

    # create a main function
    def shrink(self, p: Module) -> Module:
        match p:
            case Module(body):
                new_body = [self.shrink_stmt(s) for s in body]
                main_body = []
                funs = []
                for s in new_body:
                    if isinstance(s, FunctionDef):
                        funs.append(s)
                    else:
                        main_body.append(s)
                main = FunctionDef('main',
                                   [],
                                   main_body + [Return(Constant(0))],
                                   None, IntType(), None)
                return Module(funs + [main])

    ############################################################################
    # Reveal Functions
    ############################################################################

    def reveal_funs_exp(self, e: expr, funs) -> expr:
        match e:
            case Name(id):
              if id in funs.keys():
                return FunRef(id, funs[id])
              else:
                return e
            case Constant(value):
                return e
            case BinOp(left, op, right):
                l = self.reveal_funs_exp(left, funs)
                r = self.reveal_funs_exp(right, funs)
                return BinOp(l, op, r)
            case UnaryOp(op, operand):
                rand = self.reveal_funs_exp(operand, funs)
                return UnaryOp(op, rand)
            case Call(func, args):
                new_func = self.reveal_funs_exp(func, funs)
                new_args = [self.reveal_funs_exp(arg, funs) for arg in args]
                return Call(new_func, new_args)
            case IfExp(test, body, orelse):
                tst = self.reveal_funs_exp(test, funs)
                bod = self.reveal_funs_exp(body, funs)
                els = self.reveal_funs_exp(orelse, funs)
                return IfExp(tst, bod, els)
            case Compare(left, [op], [right]):
                l = self.reveal_funs_exp(left, funs)
                r = self.reveal_funs_exp(right, funs)
                return Compare(l, [op], [r])
            case ast.Tuple(es, kind):
                new_es = [self.reveal_funs_exp(e, funs) for e in es]
                return ast.Tuple(new_es, kind)
            case ast.List(es, kind):
                new_es = [self.reveal_funs_exp(e, funs) for e in es]
                return ast.List(new_es, kind)
            case Subscript(tup, index, kind):
                return Subscript(self.reveal_funs_exp(tup, funs),
                                 self.reveal_funs_exp(index, funs),
                                 kind)
            case _:
                raise Exception('reveal_funs_exp: unexpected: ' + repr(e))
      
    def reveal_funs_stmt(self, s: stmt, funs) -> stmt:
        match s:
            case Assign(targets, value):
                return Assign([self.reveal_funs_exp(e, funs) for e in targets],
                              self.reveal_funs_exp(value, funs))
            case Expr(value):
                return Expr(self.reveal_funs_exp(value, funs))
            case If(test, body, orelse):
                return If(self.reveal_funs_exp(test, funs),
                          [self.reveal_funs_stmt(s, funs) for s in body],
                          [self.reveal_funs_stmt(s, funs) for s in orelse])
            case While(test, body, []):
                return While(self.reveal_funs_exp(test, funs),
                             [self.reveal_funs_stmt(s, funs) for s in body],
                             [])
            case FunctionDef(name, params, body, None, returns, None):
                new_body = [self.reveal_funs_stmt(s, funs) for s in body]
                return FunctionDef(name, params, new_body, None, returns, None)
            case Return(value):
                return Return(self.reveal_funs_exp(value, funs))
            case _:
                raise Exception('reveal_funs_stmt: unexpected: ' + repr(s))
        
    def reveal_functions(self, p: Module) -> Module:
        match p:
          case Module(body):
            funs = dict()
            for s in body:
              if isinstance(s, FunctionDef):
                funs[s.name] = len(s.args)
            return Module([self.reveal_funs_stmt(s, funs) for s in body])
    
    ############################################################################
    # Limit Functions
    ############################################################################

    def limit_type(self, t):
        match t:
          case TupleType(ts):
            return TupleType([self.limit_type(t) for t in ts])
          case FunctionType(ps, rt):
            new_ps = [self.limit_type(t) for t in ps]
            new_rt = self.limit_type(rt)
            n = len(arg_registers)
            if len(new_ps) > n:
                front = new_ps[0 : n-1]
                back = new_ps[n-1 :]
                return FunctionType(front + [TupleType(back)], new_rt)
            else:
                return FunctionType(new_ps, new_rt)
          case _:
            return t

    def limit_funs_exp(self, e, param_env):
        match e:
          case Name(id):
            if id in param_env:
              (typ1, typ2, tup, ind) = param_env[id]
              return Subscript(tup, Constant(ind), Load())
            else:
              return Name(id)
          case FunRef(id, arity):
            return FunRef(id, arity)
          case Constant(value):
            return Constant(value)
          case BinOp(left, op, right):
            return BinOp(self.limit_funs_exp(left, param_env), op,
                         self.limit_funs_exp(right, param_env))
          case UnaryOp(op, operand):
            return UnaryOp(op, self.limit_funs_exp(operand, param_env))
          case Begin(body, result):
            new_body = [self.limit_funs_stmt(s, param_env) for s in body]
            new_result = self.limit_funs_exp(result, param_env)
            return Begin(new_body, new_result)
          case Call(func, args):
            n = len(arg_registers)
            new_func = self.limit_funs_exp(func, param_env)
            new_args = [self.limit_funs_exp(arg, param_env) for arg in args]
            if len(args) <= n:
                return Call(new_func, new_args)
            else:
                front = new_args[0 : n-1]
                back = new_args[n-1 :]
                return Call(new_func, front + [Tuple(back, Load())])
          case IfExp(test, body, orelse):
            return IfExp(self.limit_funs_exp(test, param_env),
                         self.limit_funs_exp(body, param_env),
                         self.limit_funs_exp(orelse, param_env))
          case Compare(left, [op], [right]):
            return Compare(self.limit_funs_exp(left, param_env), [op],
                           [self.limit_funs_exp(right, param_env)])
          case ast.Tuple(es, kind):
            return ast.Tuple([self.limit_funs_exp(e, param_env) for e in es], kind)
          case ast.List(es, kind):
            return ast.List([self.limit_funs_exp(e, param_env) for e in es], kind)
          case Subscript(tup, index, kind):
            return Subscript(self.limit_funs_exp(tup, param_env),
                             self.limit_funs_exp(index, param_env), kind)
          case _:
            raise Exception('limit_funs_exp: unexpected: ' + repr(e))

    def limit_funs_arg(self, a):
        x = a.arg
        t = a.annotation
        return ast.arg(arg = x, annotation = self.limit_type(t))
        
    def limit_funs_stmt(self, s, param_env):
      match s:
        case Assign(targets, value):
            return Assign([self.limit_funs_exp(e, param_env) for e in targets],
                          self.limit_funs_exp(value, param_env))
        case Expr(value):
            return Expr(self.limit_funs_exp(value, param_env))
        case If(test, body, orelse):
            return If(self.limit_funs_exp(test, param_env),
                      [self.limit_funs_stmt(s, param_env) for s in body],
                      [self.limit_funs_stmt(s, param_env) for s in orelse])
        case While(test, body, []):
            return While(self.limit_funs_exp(test, param_env),
                         [self.limit_funs_stmt(s, param_env) for s in body],
                         [])
        case FunctionDef(name, params, body, None, returns, None):
            n = len(arg_registers)
            new_params = [(x, self.limit_type(t)) for (x,t) in params]
            if len(new_params) <= n:
                new_body = [self.limit_funs_stmt(s, {}) for s in body]
                return FunctionDef(name, new_params, new_body, None,
                                   returns, None)
            else:
                front = new_params[0 : n-1]
                back = new_params[n-1 :]
                tup_var = generate_name('tup')
                tup_type = TupleType([t for (x,t) in back])
                param_env = {}
                i = 0
                for (x,t) in back:
                    param_env[x] = (t, tup_type, Name(tup_var), i)
                    i += 1
                new_body = [self.limit_funs_stmt(s, param_env) for s in body]
                return FunctionDef(name, front + [(tup_var, tup_type)],
                                   new_body, None, self.limit_type(returns), None)
        case Return(value):
            return Return(self.limit_funs_exp(value, param_env))
        case _:
            raise Exception('limit_funs_stmt: unexpected: ' + repr(s))

    def limit_functions(self, p: Module) -> Module:
        match p:
            case Module(body):
              return Module([self.limit_funs_stmt(s, {}) for s in body])

    ###########################################################################
    # Expose Allocation
    ###########################################################################

    def expose_alloc_stmt(self, s: stmt) -> stmt:
        match s:
            case FunctionDef(name, params, body, _, returns, _):
                new_body = [self.expose_alloc_stmt(s) for s in body]
                return FunctionDef(name, params, new_body, None, returns, None)
            case Return(value):
                return Return(self.expose_alloc_exp(value))
            case _:
                return super().expose_alloc_stmt(s)
          
    def expose_alloc_exp(self, e: expr) -> expr:
        match e:
            case FunRef(id, arity):
                return e
            case _:
                return super().expose_alloc_exp(e)
            
    ###########################################################################
    # Remove Complex Operands
    ###########################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr,Temporaries]:
      match e:
        case FunRef(id, arity):
          if need_atomic:
              tmp = Name(generate_name('fun'))
              return tmp, [(tmp, FunRef(id, arity))]
          else:
              return e, []
        case _:
          return super().rco_exp(e, need_atomic)
      
    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case FunctionDef(name, params, body, _, returns, _):
                new_body = sum([self.rco_stmt(s) for s in body], [])
                return [FunctionDef(name, params, new_body,None,returns,None)]
            case Return(value):
                new_value, bs = self.rco_exp(value, False)
                return [Assign([lhs], rhs) for (lhs, rhs) in bs] \
                    + [Return(new_value)]
            case _:
                return super().rco_stmt(s)

  ############################################################################
  # Explicate Control
  ############################################################################

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt],
                       basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match cnd:
            case Call(func, args): # functions can return bool now
                tmp = generate_name('call')
                return [Assign([Name(tmp)], cnd),
                        If(Compare(Name(tmp), [Eq()], [Constant(False)]),
                           self.create_block(els, basic_blocks),
                           self.create_block(thn, basic_blocks))]
            
            case _:
                return super().explicate_pred(cnd, thn, els, basic_blocks)

    def explicate_tail(self, e : expr,
                       blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case Begin(ss, e):
              result = self.explicate_tail(e, blocks)
              for s in reversed(ss):
                  result = self.explicate_stmt(s, result, blocks)
              return result
            case IfExp(test, body, orelse):
              new_body = self.explicate_tail(body, blocks)
              new_orelse = self.explicate_tail(orelse, blocks)
              return self.explicate_pred(test, new_body, new_orelse, blocks)
            case Call(Name(f), args) if f in builtin_functions:
              return [Return(e)]
            case Call(func, args):
              return [TailCall(func,args)]
            case _:
              return [Return(e)]
            
    def explicate_stmt(self, s: stmt, cont: List[stmt],
                       blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Return(value):
                return self.explicate_tail(value, blocks)
            case _:
                return super().explicate_stmt(s, cont, blocks)

    def explicate_def(self, d) -> stmt:
        match d:
            case FunctionDef(name, params, body, _, returns, _):
                new_body = []
                blocks = {}
                if isinstance(returns, VoidType):
                    body = body + [Return(Constant(None))]
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, blocks)
                blocks[label_name(name + '_start')] = new_body
                return FunctionDef(name, params, blocks,
                                   None, returns, None)
            case _:
                raise Exception('explicate_def: unexpected ' + d)
            
    def explicate_control(self, p: Module) -> CProgram:
        match p:
            case Module(defs):
                return CProgramDefs([self.explicate_def(d) for d in defs])
            case _:
                raise Exception('explicate_control: unexpected ' + repr(p))

    ###########################################################################
    # Select Instructions
    ###########################################################################

    def select_stmt(self, s: stmt) -> List[instr]:
      match s:
        case TailCall(func, args):
            new_func = self.select_arg(func)
            new_args = [self.select_arg(arg) for arg in args]
            move_args = [Instr('movq', [arg, Reg(reg)]) \
                         for (arg,reg) in zip(new_args, arg_registers)]
            return move_args + [TailJump(new_func, len(args))]
        case Return(value):
            mov_rax = self.select_stmt(Assign([Reg('rax')], value))
            return mov_rax + [Jump(label_name(self.current_function \
                                              + '_conclusion'))]
        case Assign([lhs], Constant(None)):
            new_lhs = self.select_arg(lhs)
            return [Instr('movq', [Immediate(0), new_lhs])]
        case Assign([lhs], FunRef(f, arity)):
            new_lhs = self.select_arg(lhs)
            return [Instr('leaq', [Global(label_name(f)), new_lhs])]
        case Assign([lhs], Call(Name(f), args)) if f in builtin_functions:
            return super().select_stmt(s)
        case Assign([lhs], Call(func, args)):
            new_lhs = self.select_arg(lhs)
            new_func = self.select_arg(func)
            new_args = [self.select_arg(arg) for arg in args]
            move_args = [Instr('movq', [arg, Reg(reg)]) \
                         for (arg,reg) in zip(new_args, arg_registers)]
            return move_args + [IndirectCallq(new_func, len(args)),
                                Instr('movq', [Reg('rax'), new_lhs])]
        case Expr(Call(Name(f), args)) if f in builtin_functions:
            return super().select_stmt(s)
        case Expr(Call(func, args)): # regular call
            new_func = self.select_arg(func)
            new_args = [self.select_arg(arg) for arg in args]
            move_args = [Instr('movq', [arg, Reg(reg)]) \
                         for (arg,reg) in zip(new_args, arg_registers)]
            return move_args + [IndirectCallq(new_func, len(args))]
        case _:
            return super().select_stmt(s)

    def select_def(self, d):
      match d:
        case FunctionDef(name, params, blocks, _, returns, _):
            self.current_function = name
            new_blocks = {}
            for (l,ss) in blocks.items():
                sss = [self.select_stmt(s) for s in ss]
                new_blocks[l] = sum(sss, [])
            param_moves = [Instr('movq', [Reg(reg), Variable(x)]) \
                           for ((x,t),reg) in zip(params, arg_registers)]
            start = label_name(name + '_start')
            new_blocks[start] = param_moves + new_blocks[start]
            f = FunctionDef(label_name(name), [], new_blocks,
                            None, returns, None)
            f.var_types = d.var_types

            # print cfg to a file
            # cfg = self.blocks_to_graph(new_blocks)
            # dotfilename = './cfgs/' + name + '.dot'
            # dotfile = open(dotfilename, 'w')
            # print(cfg.show(), file=dotfile)
            # dotfile.close()
            
            return f
        case _:
            raise Exception('select_def: unexpected ' + d)
        
    def select_instructions(self, p: CProgram) -> X86Program:
        match p:
            case CProgramDefs(defs):
                return X86ProgramDefs([self.select_def(d) for d in defs])

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case FunRef(id, arity): # todo: delete? changed to Global
                return {}
            case _:
                return super().vars_arg(a)
            
    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('leaq', [s, t]):
                return self.vars_arg(s)
            case IndirectCallq(func, arity):
                return self.vars_arg(func) \
                    | set([Reg(r) for r in arg_registers[0:arity]])
            case TailJump(func, arity):
                return self.vars_arg(func) \
                    | set([Reg(r) for r in arg_registers[0:arity]])
            case _:
                return super().read_vars(i)

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('leaq', [s, t]): # being extra explicit here -Jeremy
                return self.vars_arg(t)
            case IndirectCallq(func, arity):
                return set([Reg(r) for r in caller_save_for_alloc])
            case TailJump(func, arity):
                return set([Reg(r) for r in caller_save_for_alloc])
            case _:
                return super().write_vars(i)
            
    def liveness_transfer(self, blocks, cfg, live_before, live_after):
        def live_xfer(label, live_before_succ):
            if label == self.current_function + '_conclusion':
                return {Reg('rax'), Reg('rsp')}
            else:
                return self.uncover_live_block(label, blocks[label], live_before_succ,
                                               live_before, live_after)
        return live_xfer
    
    ###########################################################################
    # Build Interference
    ###########################################################################

    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case IndirectCallq(func, n) if func not in builtin_functions:
                for v in live_after[i]:
                    if not (v.id in registers) and self.is_root_type(self.var_types[v.id]):
                        for u in callee_save_for_alloc:
                            graph.add_edge(Reg(u), v)
                super().interfere_instr(i, graph, live_after)
            case Callq(func, n) if func not in builtin_functions:
                for v in live_after[i]:
                    if not (v.id in registers) and self.is_root_type(self.var_types[v.id]):
                        for u in callee_save_for_alloc:
                            graph.add_edge(Reg(u), v)
                super().interfere_instr(i, graph, live_after)
            case _:
                super().interfere_instr(i, graph, live_after)
    
    ############################################################################
    # Assign Homes
    ############################################################################

    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case FunRef(id, arity):
                return set()
            case _:
                return super().collect_locals_arg(a)
            
    def collect_locals_instr(self, i: instr) -> Set[location]:
        match i:
            case IndirectCallq(func, arity):
                return set()
            case TailJump(func, arity):
                return set()
            case _:
                return super().collect_locals_instr(i)
            
    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case FunRef(id, arity):
                return FunRef(id, arity)
            case _:
                return super().assign_homes_arg(a, home)
            
    def assign_homes_instr(self, i: instr, home: Dict[location, arg]) -> instr:
        match i:
            case IndirectCallq(func, arity):
                new_func = self.assign_homes_arg(func, home)
                return IndirectCallq(new_func, arity)
            case TailJump(func, arity):
                new_func = self.assign_homes_arg(func, home)
                return TailJump(new_func, arity)
            case _:
                return super().assign_homes_instr(i, home)
            
    def assign_homes_def(self, d):
      match d:
        case FunctionDef(name, params, blocks, _, returns, _):
            self.current_function = name
            self.var_types = d.var_types
            (live_before, live_after) = self.uncover_live_blocks(blocks)
            self.trace_live_blocks(blocks, live_before, live_after)
            
            graph = self.build_interference_blocks(blocks, live_after)
            (new_blocks, used_callee, num_callee, stack_spills, root_spills) = \
                self.alloc_reg_blocks(blocks, graph, d.var_types)
            trace('register allocation ' + name + ' root_spills: ' + repr(root_spills))
            new_f = FunctionDef(name, params, new_blocks, None, returns, None)
            new_f.stack_space = align(8 * (num_callee + len(stack_spills)), 16)\
                                    - 8 * num_callee
            new_f.used_callee = used_callee
            new_f.num_root_spills = len(root_spills)
            new_f.var_types = d.var_types
            return new_f
        case _:
            raise Exception('assign_homes_def: unexpected ' + d)
      
    def assign_homes(self, x86: X86ProgramDefs) -> X86ProgramDefs:
      match x86:
        case X86ProgramDefs(defs):
          return X86ProgramDefs([self.assign_homes_def(d) for d in defs])
    
    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case TailJump(Reg('rax'), arity):
                return [TailJump(Reg('rax'), arity)]
            case TailJump(target, arity):
                return [Instr('movq', [target, Reg('rax')]),
                        TailJump(Reg('rax'), arity)]
            case Instr('leaq', [s,t]) if self.in_memory(t):
                return [Instr('leaq', [s, Reg('rax')]),
                        Instr('movq', [Reg('rax'), t])]
            case _:
                return super().patch_instr(i)
            
    def patch_def(self, d):
        match d:
          case FunctionDef(name, params, blocks, _, returns, _):
            new_blocks = {l: self.patch_instrs(ss) \
                          for (l, ss) in blocks.items()}
            new_f = FunctionDef(name, params, new_blocks, None, returns, None)
            new_f.stack_space = d.stack_space
            new_f.used_callee = d.used_callee
            new_f.num_root_spills = d.num_root_spills
            return new_f
          case _:
            raise Exception('patch_def: unexpected ' + repr(d))
        
    def patch_instructions(self, p: X86ProgramDefs) -> X86ProgramDefs:
        match p:
          case X86ProgramDefs(defs):
            return X86ProgramDefs([self.patch_def(d) for d in defs])
          case _:
            raise Exception('patch_instructions: unexpected ' + repr(p))
            
    
    ############################################################################
    # Prelude and Conclusion
    ############################################################################

    def p_and_c_instr(self, i):
        match i:
          case TailJump(func, arity):
            return self.epilogue + [IndirectJump(func)]
          case _:
            return [i]
        
    def p_and_c_def(self, d):
        match d:
          case FunctionDef(name, params, blocks, _, returns, _):
                save_callee_reg = []
                for r in d.used_callee:
                    save_callee_reg.append(Instr('pushq', [Reg(r)]))
                restore_callee_reg = []
                for r in reversed(d.used_callee):
                    restore_callee_reg.append(Instr('popq', [Reg(r)]))
                rootstack_size = 2 ** 16
                heap_size = 2 ** 16
                if name == label_name('main'):
                  initialize_heaps = \
                      [Instr('movq', [Immediate(rootstack_size), Reg('rdi')]), 
                       Instr('movq', [Immediate(heap_size), Reg('rsi')]),
                       Callq(label_name('initialize'), 2),
                       Instr('movq', [Global(label_name('rootstack_begin')),
                                      Reg('r15')])]
                else:
                  initialize_heaps = []
                initialize_roots = []
                for i in range(0, d.num_root_spills):
                    initialize_roots += \
                        [Instr('movq', [Immediate(0), Deref('r15', 0)]),
                         Instr('addq', [Immediate(8), Reg('r15')])]
                prelude = [Instr('pushq', [Reg('rbp')]), \
                        Instr('movq', [Reg('rsp'), Reg('rbp')])] \
                        + save_callee_reg \
                        + [Instr('subq',[Immediate(d.stack_space),Reg('rsp')])]\
                        + initialize_heaps \
                        + initialize_roots \
                        + [Jump(name + '_start')]
                epilogue = [Instr('subq', [Immediate(8 * d.num_root_spills),
                                        Reg('r15')])] \
                      + [Instr('addq', [Immediate(d.stack_space),Reg('rsp')])] \
                      + restore_callee_reg \
                      + [Instr('popq', [Reg('rbp')])]
                self.epilogue = epilogue
                new_blocks = {}
                for (l,ss) in blocks.items():
                    new_blocks[l] = sum([self.p_and_c_instr(s) for s in ss], [])
                new_blocks[name] = prelude
                new_blocks[name + '_conclusion'] = epilogue + [Instr('retq', [])]
                return new_blocks
          case _:
            raise Exception('p_and_c_def: unexpected ' + repr(d))
    
    def prelude_and_conclusion(self, p: X86ProgramDefs) -> X86ProgramDefs:
      match p:
        case X86ProgramDefs(defs):
          # combine functions
          blocks = {}
          for d in defs:
              bs = self.p_and_c_def(d)
              for (l,ss) in bs.items():
                  blocks[l] = ss
          return X86Program(blocks)


typecheck_Lfun = type_check_Lfun.TypeCheckLfun().type_check
typecheck_Cfun = type_check_Cfun.TypeCheckCfun().type_check
typecheck_dict = {
    'source': typecheck_Lfun,
    'resolve': typecheck_Lfun,
    'check_bounds': typecheck_Lfun,
    'shrink': typecheck_Lfun,
    'reveal_functions': typecheck_Lfun,
    'convert_assignments': typecheck_Lfun,
    'convert_to_closures': typecheck_Lfun,
    'limit_functions': typecheck_Lfun,
    'expose_allocation': typecheck_Lfun,
    'remove_complex_operands': typecheck_Lfun,
    'explicate_control': typecheck_Cfun,
}
interpLfun = interp_Lfun.InterpLfun().interp
interpCfun = interp_Cfun.InterpCfun().interp
interp_dict = {
    'resolve': interpLfun,
    'check_bounds': interpLfun,
    'shrink': interpLfun,
    'reveal_functions': interpLfun,
    'convert_assignments': interpLfun,
    'convert_to_closures': interpLfun,
    'limit_functions': interpLfun,
    'expose_allocation': interpLfun,
    'remove_complex_operands': interpLfun,
    'explicate_control': interpCfun,
}
