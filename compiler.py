import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:
      
    ###########################################################################
    #Remove Complex Operands
    ###########################################################################
    @staticmethod
    def gen_assigns(bs: Temporaries) -> List[stmt]:
        return [Assign([lhs], rhs) for (lhs, rhs) in bs]

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        if isinstance(e, Constant):
            return e, []
        elif isinstance(e, Name):
            # I still do not understand what 'Name' means
            # Does it means a variable simply?
            return e, []
        elif isinstance(e, BinOp):
            lhs, lhs_temporaries = self.rco_exp(e.left, True)
            rhs, rhs_temporaries = self.rco_exp(e.right, True)
            if need_atomic:
                temp = Name(generate_name("temp"))
                return temp, lhs_temporaries + rhs_temporaries + [(temp, BinOp(lhs, e.op, rhs))]
            else:
                return BinOp(lhs, e.op, rhs), lhs_temporaries + rhs_temporaries
        elif isinstance(e, UnaryOp):
            operand, operand_temporaries = self.rco_exp(e.operand, True)
            if need_atomic:
                temp = Name(generate_name("temp"))
                return temp, operand_temporaries + [(temp, UnaryOp(e.op, operand))]
            else:
                return UnaryOp(e.op, operand), operand_temporaries  
        elif isinstance(e, Call):
            new_func, func_temp = self.rco_exp(e.func, True)
            new_args = []
            arg_temp = []
            for a in e.args:
                t_exp, t_temp = self.rco_exp(a, True)
                new_args += [t_exp]
                arg_temp += t_temp
            if need_atomic:
                temp = Name(generate_name("temp"))
                return (temp, func_temp + arg_temp + [(temp, Call(new_func, new_args, []))])
            else: 
                return Call(new_func, new_args, []), func_temp + arg_temp
        else:
            raise Exception('rco_exp not implemented')  

    def rco_stmt(self, s: stmt) -> List[stmt]:
        if isinstance(s, Assign):
            # Since the target is typically a simple variable, it doesn't need RCO.
            # Just ensure it's in the proper format (a list with a single Name).
            # Apply RCO to the source of the assignment.
            # need_atomic should be False because it only need an Expr, not an Atm

            new_value, bs = self.rco_exp(s.value, False)
            return self.gen_assigns(bs) + [Assign(s.targets, new_value)]

        elif isinstance(s, Expr):
            new_value, bs = self.rco_exp(s.value, False)
            return self.gen_assigns(bs) + [Expr(new_value)]
    
    def remove_complex_operands(self, p: Module) -> Module:
        transformed_statements = []
        for stmt in p.body:
            rco_statements = self.rco_stmt(stmt)
            transformed_statements += rco_statements
        #Create a new Module with the transformed statements.
        transformed_program = Module(transformed_statements)
        return transformed_program
        

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
    # Implement the logic to select an argument for the target architecture.
        if isinstance(e, Name):
            return Variable(e.id)
        elif isinstance(e, Constant):
            return Immediate(e.value)
        # Errors for unhandled cases:
        else:
            raise Exception('select_arg not implemented')

    def select_op(self, op: operator) -> str:
        match op:
            case Add():
                return 'addq'
            case Sub():
                return 'subq'
            case USub():
                return 'negq'
            case _:
                raise Exception('select_op unhandled: ' + repr(op))

    def select_stmt(self, s: stmt) -> List[instr]:
        match s:
            case Expr(Call(Name('input_int'), [])):
                return [Callq(label_name('read_int'), 0)]
            case Expr(Call(Name('print'), [operand])):
                return [Instr('movq', [self.select_arg(operand), Reg('rdi')]),
                        Callq(label_name('print_int'), 1)]
            case Expr(value):
                return []
            case Assign([lhs], Name(id)):
                new_lhs = self.select_arg(lhs)
                if Name(id) != lhs:
                    return [Instr('movq', [Variable(id), new_lhs])]
                else:
                    return []
            case Assign([lhs], Constant(value)):
                new_lhs = self.select_arg(lhs)
                rhs = self.select_arg(Constant(value))
                return [Instr('movq', [rhs, new_lhs])]
            case Assign([lhs], UnaryOp(USub(), Constant(i))):
                new_lhs = self.select_arg(lhs)
                # not just an optimization; needed to handle min-int
                return [Instr('movq',[Immediate(neg64(i)),new_lhs])]
            case Assign([lhs], UnaryOp(op, operand)):
                new_lhs = self.select_arg(lhs)
                rand = self.select_arg(operand)
                return [Instr('movq', [rand, new_lhs]),
                        Instr(self.select_op(op), [new_lhs])]
            case Assign([lhs], BinOp(left, Add(), right)) if left == lhs:
                new_lhs = self.select_arg(lhs)
                r = self.select_arg(right)
                return [Instr('addq', [r, new_lhs])]
            case Assign([lhs], BinOp(left, Add(), right)) if right == lhs:
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                return [Instr('addq', [l, new_lhs])]
            case Assign([lhs], BinOp(left, Sub(), right)) if right == lhs:
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                # why not use subq?
                return [Instr('negq', [new_lhs]),
                        Instr('addq', [l, new_lhs])]
            case Assign([lhs], BinOp(left, op, right)):
                new_lhs = self.select_arg(lhs)
                l = self.select_arg(left)
                r = self.select_arg(right)
                return [Instr('movq', [l, new_lhs]),
                        Instr(self.select_op(op), [r, new_lhs])]
            case Assign([lhs], Call(Name('input_int'), [])):
                new_lhs = self.select_arg(lhs)
                return [Callq(label_name('read_int'), 0),
                        Instr('movq', [Reg('rax'), new_lhs])]
            case Assign([lhs], Call(Name('print'), [operand])):
                return [Instr('movq', [self.select_arg(operand), Reg('rdi')]),
                        Callq(label_name('print_int'), 1)]
            case _:
                raise Exception('error in select_stmt, unknown: ' + repr(s))
    

    def select_instructions(self, p: Module) -> X86Program:
        # Implement the logic to select instructions for a program
        selected_instructions = []
        for stmt in p.body:
            selected_stmt = self.select_stmt(stmt)
            selected_instructions += selected_stmt
        # Create a new X86Program with the selected instructions.
        x86_program = X86Program(selected_instructions)
        return x86_program       

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        # We define every arg, but what does 'home' do?
        # I think currently, arg could be a Variable or other arg.
        if isinstance(a, Variable):
            return home[a]
        return a

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        # YOUR CODE HERE
        # create a new Instr
        new_a = []
        if isinstance(i, Instr):
            for a in i.args:
                new_a.append(self.assign_homes_arg(a, home))
            return Instr(i.instr, new_a)
        else:
            return i

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        # YOUR CODE HERE
        new_instrs = []
        # second iteration, replace all variable
        for s in ss:
            new_instrs.append(self.assign_homes_instr(s, home))
        return new_instrs

    def assign_homes(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        if isinstance(p.body, dict):
            assign_home_instrs = {}
            for label, instrs in p.body.items():
                assign_home_instrs[label] = self.assign_homes_instrs(instrs)
        else:
            home = {}
            # first iteration, build a dict to save all variable and corresponding deref as key-value pairs
            # I actually combine the `collect_local_instrs and gen_stack_access`
            # This could be wraped into function later
            # TODO: Refactor code
            num_varibale = 0
            for s in p.body:
                if isinstance(s, Instr):
                    for a in s.args:
                        if isinstance(a, Variable) and a not in home:
                            num_varibale += 1
                            home[a] = Deref("rbp", -8 * num_varibale)
            assign_home_instrs = self.assign_homes_instrs(p.body, home)
            new_x86_program = X86Program(assign_home_instrs)
            new_x86_program.stack_space = align(8 * len(home.keys()), 16)
        return new_x86_program

    ############################################################################
    # Patch Instructions
    ############################################################################
    def big_constant(self, c:arg) -> bool:
        # To check if an immediate is too big to store in a register
        # The size limit is not for Reg or Deref, it is for immediate
        return isinstance(c, Immediate) and (c.value > (2**32) or c.value < -2**32)
    
    def in_memory(self, a:arg) -> bool:
        # To check if this variable in memory
        return isinstance(a, Deref)
    
    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
        res = []
        match i:
            case Instr(inst, [source, target]):
                if (self.in_memory(source) and self.in_memory(target)) or self.big_constant(source):
                    # two memory access, do patch instration operation
                    # build two instration and add into list
                    # I assume %rax as a intermediate register and always available
                    # but how to check if it is in use?
                    mov_instr = Instr("movq", [i.source(), Reg("rax")])
                    # for movq, addq, subq, second operation should be same as original operation
                    op_instr = Instr(inst, [Reg("rax"), i.target()])
                    res.append(mov_instr)
                    res.append(op_instr)
                else:
                    res.append(i)
            case _:
                # add instration into list
                res.append(i)
        return res

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        # YOUR CODE HERE
        res = []
        for s in ss:
            instr_res = self.patch_instr(s)
            print(f"instr is {s}, patched instrs are {instr_res}")
            res += instr_res
        return res

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        if isinstance(p.body, dict):
            patched_instrs = {}
            for label, instrs in p.body.items():
                patched_instrs[label] = self.patch_instrs(instrs)
        else:
            patched_instrs = self.patch_instrs(p.body)
        new_x86_program = X86Program(patched_instrs)
        new_x86_program.stack_space = p.stack_space
        return new_x86_program

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        # The problem is that how to know the size I need to allocate.
        # iterate on this program and 
        # If we have multiple functions (with labels)
        if isinstance(p.body, dict):
            new_body = {}
            for label, instrs in p.body.items():
                # instructions for stack allocations
                prelude = [
                    Instr("pushq", [Reg("rbp")]),
                    Instr("movq", [Reg("rsp"), Reg("rbp")]),
                    Instr("subq", [Immediate(p.stack_space), Reg("rsp")])
                ]
                # instructions for restore stack allocations
                conclusion = [
                    Instr("addq", Immediate(p.stack_space), Reg("rsp")),
                    # Instr("mov", ["%rbp", "%rsp"]), # is equal to addq if %rbp 's value is not changed
                    Instr("popq", [Reg("rbp")]),
                    Instr("retq", [])
                ]
                
                new_body[label] = prelude + instrs + conclusion          
        else:  
            # If we have a single main function
            prelude = [
                Instr("pushq", [Reg("rbp")]),
                Instr("movq", [Reg("rsp"), Reg("rbp")]),
                Instr("subq", [Immediate(p.stack_space), Reg("rsp")])
            ]
            
            conclusion = [
                Instr("addq", [Immediate(p.stack_space), Reg("rsp")]),
                Instr("popq", [Reg("rbp")]),
                Instr("retq", [])
            ]
            
            new_body = prelude + p.body + conclusion

        return X86Program(new_body)

    # challenge, exercise 2.7
    '''
    def pe_exp(e):
        match e:
            case BinOp(left, Add(), right):
                return pe_add(pe_exp(left), pe_exp(right))
            case BinOp(left, Sub(), right):
                return pe_sub(pe_exp(left), pe_exp(right))
            case UnaryOp(USub(), v):
                return pe_neg(pe_exp(v))
            case Constant(value):
                return e
            case Call(Name('input_int'), []):
                return e
    def pe_stmt(s):
        match s:
            case Expr(Call(Name('print'), [arg])):
                return Expr(Call(Name('print'), [pe_exp(arg)]))
            case Expr(value):
                return Expr(pe_exp(value))
    '''
