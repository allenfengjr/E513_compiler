import ast
from ast import *
from utils import *
from x86_ast import *
from typing import List, Tuple, Set, Dict
from graph import *
from queue import *
from priority_queue import *
Binding = Tuple[Name, expr]
Temporaries = List[Binding]

# Register global variables
caller_save: Set[str] = {'rax','rcx','rdx','rsi','rdi','r8','r9','r10','r11'}
callee_save: Set[str] = {'rsp', 'rbp', 'rbx', 'r12', 'r13', 'r14', 'r15'}
reserved_registers: Set[str] = {'rax', 'r11', 'r15', 'rsp', 'rbp', '__flag'}  # Register that cannot be used for allocation (for negetive intergers)
general_registers: List[str] = ['rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', # Register for allocation
                     'rbx', 'r12', 'r13', 'r14']
registers_for_alloc: List[str] = general_registers
arg_registers: List[str] = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9'] # Create the argument-passing registers

registers = set(general_registers).union(reserved_registers)

caller_save_for_alloc = caller_save.difference(reserved_registers) \
                                   .intersection(set(registers_for_alloc))
callee_save_for_alloc = callee_save.difference(reserved_registers) \
                                   .intersection(set(registers_for_alloc))

byte_to_full_reg = \
    {'ah': 'rax', 'al': 'rax',
     'bh': 'rbx', 'bl': 'rbx',
     'ch': 'rcx', 'cl': 'rcx',
     'dh': 'rdx', 'dl': 'rdx'}

register_color = {'rax': -1, 'rsp': -2, 'rbp': -3, 'r11': -4, 'r15': -5, '__flag': -6}

for i, r in enumerate(registers_for_alloc):
    register_color[r] = i

extra_arg_registers = list(set(arg_registers) - set(registers_for_alloc))
for i, r in enumerate(extra_arg_registers):
    register_color[r] = -i - 6

# L_if global variables
C_if_block = {}

class Compiler:
    ###########################################################################
    # Shrink if
    ###########################################################################
    # type-checker will not handle if operand is a `IfExp`, so any potinal expression will have to go shrink_exp
    def shrink_exp(self, e: expr) -> expr:
        # print(f"The expression I need to modify is, {e}")
        match e:
            case IfExp(test, body, orelse):
                res = self.shrink_exp(test)
                body_exp = self.shrink_exp(body)
                orelse_exp = self.shrink_exp(orelse)
                return IfExp(res, body_exp, orelse_exp)
            case BoolOp(And(), values):
                left, right = values[0], values[1]
                l = self.shrink_exp(left)
                r = self.shrink_exp(right)
                return IfExp(l, r, Constant(False))
            case BoolOp(Or(), values):
                left, right = values[0], values[1]
                l = self.shrink_exp(left)
                r = self.shrink_exp(right)
                return IfExp(l, Constant(True), r)
            case UnaryOp(op, operand):
                return UnaryOp(op, self.shrink_exp(operand))
            case BinOp(left, op, right):
                return BinOp(self.shrink_exp(left), op, self.shrink_exp(right))
            case Compare(left, ops, comparators):
                comparators_exp = [self.shrink_exp(i) for i in comparators]
                return Compare(self.shrink_exp(left), ops, comparators_exp)
            case Call(func, args, keywords):
                args_exp = [self.shrink_exp(i) for i in args]
                return Call(func, args_exp, keywords)
            case Constant():
                return e
            case Name():
                return e
            case Compare(left, cmp, comparators):
                shrink_left = self.shrink_exp(left)
                shrink_comp = [self.shrink_exp(i) for i in comparators]
                return Compare(shrink_left, cmp, shrink_comp)
            case _:
                # Begin should not appear at this pass
                raise Exception("The missing expression I do not handle")
            
    def shrink_stmt(self, s:stmt) -> stmt:
        match s:
            case Assign(targets, value):
                shrink_targets = [self.shrink_exp(i) for i in targets]
                shrink_value = self.shrink_exp(value)
                return Assign(shrink_targets, shrink_value)
            case Expr(value):
                return Expr(self.shrink_exp(value))
            case If(test, body, orelse):
                shrink_test = self.shrink_exp(test)
                shrink_body = [self.shrink_stmt(i) for i in body]
                shrink_orelse = [self.shrink_stmt(i) for i in orelse]
                return If(shrink_test, shrink_body, shrink_orelse)
            
    def shrink(self, p:Module) -> Module:
        transformed_statements = []
        for stmt in p.body:
            shrink_statement = self.shrink_stmt(stmt)
            transformed_statements.append(shrink_statement)
            # print(f"the stmts are, {[i.__class__ for i in rco_statements]}, value is {rco_statements}")
        #Create a new Module with the transformed statements.
        transformed_program = Module(transformed_statements)
        return transformed_program
                
    ###########################################################################
    #Remove Complex Operands
    ###########################################################################
    
    
    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        # print(f"the expression needs to rco is {e}, its type is {e.__class__}")
        match e:
            case Constant():
                # Question: how to deal with large constant here.
                return e, []
            case Name():
                # I still do not understand what 'Name' means
                # Does it means a variable simply?
                return e, []
            case BinOp(left, op, right):
                lhs, lhs_temporaries = self.rco_exp(left, True)
                rhs, rhs_temporaries = self.rco_exp(right, True)
                if need_atomic:
                    temp = Name(generate_name("temp"))
                    return temp, lhs_temporaries + rhs_temporaries + [(temp, BinOp(lhs, op, rhs))]
                else:
                    return BinOp(lhs, op, rhs), lhs_temporaries + rhs_temporaries
            case UnaryOp(op, oprd):
                operand, operand_temporaries = self.rco_exp(oprd, True)
                if need_atomic:
                    temp = Name(generate_name("temp"))
                    return temp, operand_temporaries + [(temp, UnaryOp(op, operand))]
                else:
                    return UnaryOp(op, operand), operand_temporaries  
            case Call(func, args, keywords):
                new_func, func_temp = self.rco_exp(func, True)
                new_args = []
                arg_temp = []
                for a in args:
                    t_exp, t_temp = self.rco_exp(a, True)
                    new_args += [t_exp]
                    arg_temp += t_temp
                if need_atomic:
                    temp = Name(generate_name("temp"))
                    return (temp, func_temp + arg_temp + [(temp, Call(new_func, new_args, []))])
                else: 
                    return Call(new_func, new_args, []), func_temp + arg_temp
            case IfExp(test, body, orelse):
                # all three does not need atomic
                rco_test, tmp_test = self.rco_exp(test, False)
                rco_body, tmp_body = self.rco_exp(body, False)
                rco_orelse, tmp_orelse = self.rco_exp(orelse, False)
                # make_begin will create stmt^* for IfExp, it will return a Begin
                new_body = make_begin(tmp_body, rco_body)
                new_orelse = make_begin(tmp_orelse, rco_orelse)
                if need_atomic:
                    # If need atomic, then I must return an atom
                    tmp = Name(generate_name("temp"))
                    return (tmp, tmp_test+[(tmp, IfExp(rco_test, new_body, new_orelse))])
                else:
                    # Otherwise, I can return an expression. 
                    # I have Assign in Begin, so no need to append temps here
                    return IfExp(rco_test, new_body, new_orelse), tmp_test
            case Compare(left, cmp, comparators):
                rco_left, tmp_test = self.rco_exp(left, True)
                rco_comparators = []
                tmp_comparators = []
                for ce in comparators:
                    rco_ce, tmp_ce = self.rco_exp(ce, True)
                    rco_comparators += [rco_ce]
                    tmp_comparators += tmp_ce
                if need_atomic:
                    tmp = Name(generate_name("temp"))
                    return (tmp, tmp_test + [(tmp, Compare(rco_left, cmp, rco_comparators))] + tmp_comparators)
                else:
                    return Compare(rco_left, cmp, rco_comparators), tmp_test + tmp_comparators
            case Begin(body, result):
                # print("I do have begin")
                new_result, tmp_res = self.rco_exp(result, False)
                return Begin(body, new_result), tmp_res
            case _:
                raise Exception('rco_exp not implemented')  

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign(targets, value):
                # Since the target is typically a simple variable, it doesn't need RCO.
                # Just ensure it's in the proper format (a list with a single Name).
                # Apply RCO to the source of the assignment.
                # need_atomic should be False because it only need an Expr, not an Atm
                new_value, bs = self.rco_exp(value, False)
                return make_assigns(bs) + [Assign(targets, new_value)]
            case Expr(value):
                new_value, bs = self.rco_exp(value, False)
                return make_assigns(bs) + [Expr(new_value)]
            case If(test, body, orelse):
                rco_exp_test, bs = self.rco_exp(test, False)
                rco_stmt_body = [self.rco_stmt(i) for i in body] # need flatten later
                rco_stmt_orelse = [self.rco_stmt(i) for i in orelse]
                return make_assigns(bs) + [If(rco_exp_test, sum(rco_stmt_body,[]), sum(rco_stmt_orelse, []))]
    
    def remove_complex_operands(self, p: Module) -> Module:
        transformed_statements = []
        for stmt in p.body:
            rco_statements = self.rco_stmt(stmt)
            transformed_statements += rco_statements
        #Create a new Module with the transformed statements.
        transformed_program = Module(transformed_statements)
        return transformed_program
    

    ############################################################################
    # Explicate Control
    ############################################################################
    def create_block(self, stmts, basic_blocks):
        match stmts:
            case [Goto(l)]:
                return stmts
            case _:
                label = label_name(generate_name('block'))
                basic_blocks[label] = stmts
                return [Goto(label)]
            
    # This will return a list of C_if stmts add to dictionary
    # How do I define cont? just use stmt[1:]?
    def explicate_effect(self, e, cont, basic_blocks) -> stmt:
        match e:
            case IfExp(test, body, orelse):                
                body_exp = self.explicate_effect(body, cont, basic_blocks)
                orelse_exp = self.explicate_effect(orelse, cont, basic_blocks)
                test_exp = self.explicate_pred(test, body_exp, orelse_exp, basic_blocks)
                return test_exp
            case Call(func, args):
                stmts = [Expr(e)] + cont
                call_block = self.create_block(stmts, basic_blocks)
                return call_block
            case Begin(body, result):
                # Begin is exactually a set of stmts and a result after these stmts
                # I want to have a cont_block that adding body's stmts
                # result is actually the original body/orelse itself
                # can we merge result? => result is dealed in explicate_pred part, so no need
                cont_block = self.create_block(cont, basic_blocks)
                cont_block = [Return(result)] + cont_block
                for b in reversed(body):
                    cont_block = self.explicate_stmt(b, cont_block, basic_blocks) # merge
                return cont_block
            case _:
                return [e] + cont # just merge
    
    def explicate_assign(self, rhs, lhs, cont, basic_blocks) -> stmt:
        match rhs:
            case IfExp(test, body, orelse):
                cont_block = self.create_block(cont, basic_blocks)
                #print(f"Assign body is {body}, orelse is {orelse}, test is {test}, test type is {test.__class__}")
                # two branch
                body_ass = self.explicate_assign(body, lhs, cont_block, basic_blocks)
                orelse_ass = self.explicate_assign(orelse, lhs, cont_block, basic_blocks)
                test_ass = self.explicate_pred(test, body_ass, orelse_ass, basic_blocks)
                return test_ass
            case Begin(body, result):
                # in what situation, Begin will on the rhs of Assign?
                # Anyway, if it is on the rhs, we deal with is reversely as above
                cont_block = self.create_block(cont, basic_blocks)
                for b in reversed(body):
                    cont_block = self.explicate_stmt(b, cont_block, basic_blocks) # merge  
                return cont_block
            case _:
                return [Assign([lhs], rhs)] + cont
    
    def explicate_pred(self, cnd, thn, els, basic_blocks) -> stmt:
        match cnd:
            case Compare(left, [op], [right]):
                thn_block = self.create_block(thn, basic_blocks)
                els_block = self.create_block(els, basic_blocks)
                return [If(cnd, thn_block, els_block)]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                return self.explicate_pred(operand, els, thn, basic_blocks)
            case IfExp(test, body, orelse):
                # remove nested if, use test instead of the whole IfExp to decide branch
                # print(f"Pred body is {body}, orelse is {orelse}, test is {test}, test type is {test.__class__}")
                thn_b = self.create_block(thn, basic_blocks)
                els_b = self.create_block(els, basic_blocks)
                thn_block = self.explicate_pred(body, thn_b, els_b,basic_blocks)
                els_block = self.explicate_pred(orelse, els_b, thn_b,basic_blocks)
                return self.explicate_pred(test, thn_block, els_block, basic_blocks)
            case Begin(body, result):
                # here "result" is the cnd(strange...)
                # still, we add body into cont(both thn and els?)
                for b in reversed(body):
                    thn_block = self.explicate_effect(b, thn, basic_blocks)
                    els_block = self.explicate_effect(b, els, basic_blocks)
                #return [If(result, thn_block, els_block)]
                return self.explicate_pred(result, thn_block, els_block, basic_blocks)

            case _:
                return [If(Compare(cnd, [Eq()], [Constant(False)]),
                        self.create_block(els, basic_blocks),
                        self.create_block(thn, basic_blocks))]
    
    def explicate_stmt(self, s, cont, basic_blocks):
        # print(f'stmt is {s}, type is {s.__class__}')
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                body_b = cont
                for b in reversed(body):
                    body_b = self.explicate_stmt(b, body_b, basic_blocks)
                orelse_b = cont
                for e in reversed(orelse):
                    orelse_b = self.explicate_stmt(e, orelse_b, basic_blocks)
                return self.explicate_pred(test, body_b, orelse_b, basic_blocks)
            case _:
                # print(f"stmt is {s}, type is {s.__class__}")
                raise Exception("Unhandle stmt in explicate control")
    
    def explicate_control(self, p):
        match p:
            case Module(body):
                new_body = [Return(Constant(0))]
                basic_blocks = {}
                for s in reversed(body):
                    new_body = self.explicate_stmt(s, new_body, basic_blocks)
                basic_blocks[label_name('start')] = new_body
                return CProgram(basic_blocks)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
    # Implement the logic to select an argument for the target architecture.
        if isinstance(e, Name):
            return Variable(e.id)
        elif isinstance(e, Constant):
            return Immediate(e.value)
        # Handle Boolean constants:
        elif isinstance(e, True):
            return Immediate(1)
        elif isinstance(e, False):
            return Immediate(0)
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
            # no need to deal with not() here, we will use the xorq instruction
            # case Not():
            #     return 'notq' 
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
                
            # deal with the UnaryOp(Not(),exp)
            case Assign([lhs], UnaryOp(Not(), operand)):
                new_lhs = self.select_arg(lhs)
                rand = self.select_arg(operand)
                # If the left-hand-side variable is the same as the argument as the argument of not
                if new_lhs == rand:
                    return [Instr('xorq', [Immediate(1), new_lhs])]
                else:
                    return [Instr('movq', [rand, new_lhs]),
                            Instr('xorq', [Immediate(1), new_lhs])]
                    
            # deal with the Compare(exp,[cmp],[exp]), cmp includes: Eq(), NotEq(), Lt(), LtE(), Gt(), GtE()
            case Assign([lhs], Compare(left, [Eq()], right)):
                new_lhs = self.select_arg(lhs)
                arg1 = self.select_arg(left)
                arg2 = self.select_arg(right[0])   
                return [Instr('movq', [arg2, arg1]),
                        Instr('sete', [ByteReg('al')]), # Set 'al' based on equality
                        Instr('movzbq', [ByteReg('al'), new_lhs]) # Zero-extend 'al' to 'var'
                       ]
            case Assign([lhs], Compare(left, [NotEq()], right)):
                new_lhs = self.select_arg(lhs)
                arg1 = self.select_arg(left)
                arg2 = self.select_arg(right)   
                return [Instr('movq', [arg2, arg1]),
                        Instr('setne'), [ByteReg('al')], # Set 'al' based on equality
                        Instr('movzbq', [ByteReg('al'), new_lhs]) # Zero-extend 'al' to 'var'
                       ]
            case Assign([lhs], Compare(left, [Lt()], right)):
                new_lhs = self.select_arg(lhs)
                arg1 = self.select_arg(left)
                arg2 = self.select_arg(right)   
                return [Instr('movq', [arg2, arg1]),
                        Instr('setl'), [ByteReg('al')], # Set 'al' based on equality
                        Instr('movzbq', [ByteReg('al'), new_lhs]) # Zero-extend 'al' to 'var'
                       ]
            case Assign([lhs], Compare(left, [LtE()], right)):
                new_lhs = self.select_arg(lhs)
                arg1 = self.select_arg(left)
                arg2 = self.select_arg(right)   
                return [Instr('movq', [arg2, arg1]),
                        Instr('setle'), [ByteReg('al')], # Set 'al' based on equality
                        Instr('movzbq', [ByteReg('al'), new_lhs]) # Zero-extend 'al' to 'var'
                       ]
            case Assign([lhs], Compare(left, [Gt()], right)):
                new_lhs = self.select_arg(lhs)
                arg1 = self.select_arg(left)
                arg2 = self.select_arg(right)   
                return [Instr('movq', [arg2, arg1]),
                        Instr('setg'), [ByteReg('al')], # Set 'al' based on equality
                        Instr('movzbq', [ByteReg('al'), new_lhs]) # Zero-extend 'al' to 'var'
                       ]     
            case Assign([lhs], Compare(left, [GtE()], right)):
                new_lhs = self.select_arg(lhs)
                arg1 = self.select_arg(left)
                arg2 = self.select_arg(right)   
                return [Instr('movq', [arg2, arg1]),
                        Instr('setge'), [ByteReg('al')], # Set 'al' based on equality
                        Instr('movzbq', [ByteReg('al'), new_lhs]) # Zero-extend 'al' to 'var'
                       ]     
            # deal with goto statement
            case Goto(label):
                return [Jump(label)]
            # deal with if statement  ???
            
            
            case If(test, [body], [orelse]) if isinstance(test, Compare):
                arg1 = self.select_arg(test.left)
                arg2 = self.select_arg(test.comparators[0])
                cmp_op = test.ops[0]

                if isinstance(cmp_op, Eq):
                    condition = 'je'  # Jump if equal
                elif isinstance(cmp_op, NotEq):
                    condition = 'jne'  # Jump if not equal
                elif isinstance(cmp_op, Lt):
                    condition = 'jl'  # Jump if less than
                elif isinstance(cmp_op, LtE):
                    condition = 'jle'  # Jump if less than or equal
                elif isinstance(cmp_op, Gt):
                    condition = 'jg'  # Jump if greater than
                elif isinstance(cmp_op, GtE):
                    condition = 'jge'  # Jump if greater than or equal
                else:
                    raise Exception(f'Unhandled comparison operator: {cmp_op}')
                
                print("create block here is, ", body.label, orelse.label)

                return [
                    Instr('cmpq', [arg2, arg1]),
                    #Instr(condition, [GlobalValue(body.label)]),  # Use the appropriate conditional jump
                    JumpIf(condition[1:], body.label),
                    #Instr('jmp', [GlobalValue(orelse.label)])
                    Jump(orelse.label)
                ]
            # deal with return:
            case Return(value):
                arg1 = self.select_arg(value)
                return [
                        Instr('movq', [arg1, Reg('rax')]),
                        Jump(label_name('conclusion'))
                        ]
            case _:
                print(f" unhandle stmt {s}")
                raise Exception('error in select_stmt, unknown: ' + repr(s))
    

    def select_instructions(self, p: Module) -> X86Program:
        # Implement the logic to select instructions for a program
        selected_instructions = {}
        for (label, block) in p.body.items():
            print("block is, ", block)
            selected_instructions[label] = []
            for stmt in block:
                selected_stmt = self.select_stmt(stmt)
                selected_instructions[label] += selected_stmt
        # Create a new X86Program with the selected instructions.
        x86_program = X86Program(selected_instructions)
        return x86_program       


  ###########################################################################
    # Uncover Live
    ###########################################################################
    def vars_arg(self, a: arg) -> Set[location]:
        match a :
            case Variable(id):
                return {a}
            case Reg(id):
                return {a}
            case Deref(reg, offset):
                return {Reg(reg)}
            case Immediate(value):
                return set()
            # add 'bytereg' arg var?
            case ByteReg(id):
                return {a}
            case _:
                raise Exception('error in vars_arg, unknown: ' + repr(a))

    def read_vars(self, i: instr) -> Set[location]:
        match i: 
            case Instr(instr, args):
                return set().union(*[self.vars_arg(arg) for arg in args])
            case Instr('movq', [s, t]):
                return self.vars_arg(s)
            case Callq(func, num_args):         # Callq should include all the arguments-passing registers in read_set
                return set([Reg(r) for r in arg_registers[0:num_args]])
            case Instr('xorq', [s, t]): # handle the new xorq, both s and t are readable
                return self.vars_arg(s) | self.vars_arg(t)
            case Instr('cmpq', [s, t]): # compare instrution
                return self.vars_arg(s) | self.vars_arg(t)
            case Instr('set', [cc, s]):  # cc is the condition code
                return self.vars_arg(s)
            case Instr('movzbq', [s, t]): #  s is single byte register, t is 64-bit register
                return self.vars_arg(s) | self.vars_arg(t)
            case JumpIf(cc, label): # What is the readable part of JumpIf
                return {} # both cc and label are readable?
            case Jump(label):
                return {}
            case _:
                raise Exception('error in read_vars, unexpected: ' + repr(i))

    def write_vars(self, i: instr) -> Set[location]:
        match i: 
            case Instr(instr, [t]):
                return self.vars_arg(t)
            case Instr('cmpq', [s1, s2]): # compare instru
                return set()
            case Instr(instr, [s, t]):
                return self.vars_arg(t)
            case Callq(func, num_args):         # Callq should include all the caller-saved registers in write_set
                return set([Reg(r) for r in caller_save_for_alloc])
            case Instr('xorq', [s, t]): # handle the new xorq,  t is writable
                return self.vars_arg(t)
            case Instr('set', [cc, s]): 
                return self.vars_arg(s)
            case Instr('movzbq',[s,t]):
                return self.vars_arg(t)
            case JumpIf(cc, label):
                return set() # JmpIf instruction does not modify or write to any variables or registers
            case Jump(label):
                return set()
            case _:
                print(f"uncatch instr is, {i}")
                raise Exception('error in write_vars, unexpected: ' + repr(i))
    # Applying the liveness-analysis rules
    def uncover_live_instr(self, i:instr, live_before_succ: Set[location],
                           live_before: Dict[instr, Set[location]],
                           live_after: Dict[instr, Set[location]]):
        live_after[i] = live_before_succ
        live_before[i] = live_after[i].difference(self.write_vars(i)).union(self.read_vars(i))

    def trace_live(self, p: X86Program, live_before: Dict[instr, Set[location]],
                   live_after: Dict[instr, Set[location]]):
        match p:
          case X86Program(body):
            i = 0
            for s in body:
                if i == 0:
                    trace('\t' + str(live_before[s]))
                trace(str(s))
                trace('\t' + str(live_after[s]))
                i = i + 1
            trace("")

# The trace live in blocks
    def trace_live_blocks(self, blocks, live_before: Dict[instr, Set[location]],
                          live_after: Dict[instr, Set[location]]):
        for (l, ss) in blocks.body.items():
            trace(l + ':\n')
            i = 0
            for s in ss:
                if i==0:
                    trace('\t\t{' + ','.join([str(l) for l in live_before[s]]) + '}')
                trace('\t' + str(s))
                trace('\t{' + ','.join([str(l) for l in live_after[s]]) + '}')
                i = i + 1
            trace('')

# When meet with 'Jump' and 'JumpIf', go to the label
    @staticmethod
    def adjacent_instr(s:instr) -> List[str]:
        if isinstance(s, Jump) or isinstance(s, JumpIf):
            return[s.label]
        else: 
            return []
# Create CFG graph
    def blocks_to_graph(self, blocks: Dict[str, List[instr]]) -> DirectedAdjList:
        graph = DirectedAdjList()  
        for u in blocks.keys():
            graph.add_vertex(u)
        for (u, ss) in blocks.items():
            for s in ss:
                for v in self.adjacent_instr(s):
                    graph.add_edge(u, v)
        return graph
        
    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                live_before = {}
                live_after = {}
                cfg = self.blocks_to_graph(body)
                cfg_trans = transpose(cfg) # transpost the CFG graph
                live_before_block = \
                    {label_name('conclusion'):{Reg('rax'),Reg('rsp')}}
                for l in topological_sort(cfg_trans): # Applying the topological sort
                    if l!= label_name('conclusion'):
                        adj_live = [live_before_block[v]\
                                    for v in cfg.adjacent(l)]
                        live_before_succ = set().union(*adj_live)
                        for i in reversed(body[l]): # why not for i in body[l]
                            self.uncover_live_instr(i, live_before_succ, live_before, live_after)
                            live_before_succ = live_before[i]
                        live_before_block[l] = live_before_succ
                trace("uncover live:")
                self.trace_live_blocks(p, live_before, live_after)
                return live_after


    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(body):
                G = UndirectedAdjList()
                for label, block in body.items():
                    for i in block:
                        self.interfere_instr(i, G, live_after)
                return G

    def interfere_instr(self, i: instr, graph: UndirectedAdjList,
                        live_after: Dict[instr, Set[location]]):
        match i:
            case Instr('movq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)

            case Instr('movzbq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
            # how to know the inference of x86_if instruction
            case Instr('cmpq', [s, t]):
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d and s != v:
                            graph.add_edge(d, v)
            
            case _:
                print(f"the i is, {i}")
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d:
                            graph.add_edge(d, v)
    # def build_move(self, p:X86Program) -> UndirectedAdjList:
    #     # THIS IS FOR CHALLANGE, should build a move graph to move bias
    #     # this should be called in `allocate_registers`
    #     # YOUR CODE HERE
    #     move_graph = UndirectedAdjList()
    #     for i in p.body:
    #         if isinstance(i, Instr) and i.instr == 'movq': #Connect all the vertax in movq instruction
    #             move_graph.add_edge(i.source(), i.target())
    #     return move_graph
    
    ############################################################################
    # Allocate Registers
    ############################################################################
    # Returns the coloring and the set of spilled variables.
    def callee_saved_reg(self, variable: location) -> bool:
        callee_saved = {"rbx", "r12", "r13", "r14"}
        if isinstance(variable, Reg) and variable.id in callee_saved:
            return True
        return False    

    def choose_color(self, v, unavail_colors):
        i = 0
        while i in unavail_colors[v]:
            i += 1
        return i

    def color_graph(self, graph: UndirectedAdjList,
                    variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        spills = set()
        unavail_colors = {}
        def compare(u, v):
            return len(unavail_colors[u.key]) < len(unavail_colors[v.key])
        Q = PriorityQueue(compare) # lambda -> 
        color = {}
        for r in registers_for_alloc:
            color[Reg(r)] = register_color[r]
        for x in variables:
            adj_reg = [y for y in graph.adjacent(x) if y.id in registers]
            unavail_colors[x] = \
                set().union([register_color[r.id] for r in adj_reg])
            Q.push(x)
        while not Q.empty():
            v = Q.pop()
            c = self.choose_color(v, unavail_colors)
            color[v] = c
            if c >= len(registers_for_alloc):
                spills = spills.union(set([v]))  # add method instead?
            for u in graph.adjacent(v):
                if u.id not in registers and u.id not in byte_to_full_reg:
                    unavail_colors[u].add(c)
                    Q.increase_key(u)
        return color, spills

    def identify_home(self, c: int, first_location: int) -> arg:
        if c < len(registers_for_alloc):
            return Reg(registers_for_alloc[c])
        else:
            offset = first_location + 8 * (c - len(registers_for_alloc))
            return Deref('rbp', - offset)

    def is_callee_color(self, c: int) -> bool:
        return c < len(registers_for_alloc) \
            and registers_for_alloc[c] in callee_save

    def used_callee_reg(self, variables: Set[location],
                        color: Dict[location, int]) -> Set[str]:
        result = set()
        for x in variables:
            if self.is_callee_color(color[x]):
                result.add(registers_for_alloc[color[x]])
        return list(result)

##  allocate registers
    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(body):
                variables_block = {}
                for label, block in body.items():
                    variables_block[label] = self.collect_locals_instrs(block)
                variables = set()
                for value_set in variables_block.values():
                    variables = variables.union(value_set)                
                (color, spills) = self.color_graph(graph, variables)
                trace("color")
                trace(color)
                trace("")
                
                p.used_callee = set()
                used_callee = p.used_callee
                used_callee = self.used_callee_reg(variables, color)
                num_callee = len(used_callee)
                
                home = {}
                for x in variables:
                    home[x] = self.identify_home(color[x], 8 + 8 * num_callee)
                trace("home")
                trace(home)
                trace("")
                new_body = [self.assign_homes_instr(s, home) for s in body]
                new_p = X86Program(new_body)
                new_p.stack_space = align(8 * (num_callee + len(spills)), 16) \
                    - 8 * num_callee
                new_p.used_callee = used_callee
                return new_p
    
    

    ############################################################################
    # Assign Homes
    ############################################################################

    def collect_locals_arg(self, a: arg) -> Set[location]:
        # Given an argument, return a Set of variable
        match a:
            case Reg(id):
                return set()
            case Variable(id):
                return {Variable(id)}
            case Immediate(value):
                return set()
            case Deref(reg, offset):
                return set()
            case _:
                raise Exception('error in collect_locals_arg, unknown: ' + repr(a))
    
    def collect_locals_instr(self, i: instr) -> Set[location]:
        # Return all locations in one instruction
        match i:
            case Instr(inst, args):
                lss = [self.collect_locals_arg(a) for a in args]
                return set().union(*lss)
            case Callq(func, num_args):
                return set()
            case Jump(label):
                return set()
            case JumpIf(cc, label):
                return set()
            case _:
                raise Exception('error in collect_locals_instr, unknown: ' + repr(i))

    def collect_locals_instrs(self, ss: List[stmt]) -> Set[location]:
        return set().union(*[self.collect_locals_instr(s) for s in ss])

    @staticmethod
    def gen_stack_access(i: int) -> arg:
        return Deref('rbp', -(8 + 8 * i))
    
    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        # Assignment 2. Register Allocation
        # In this assignment, home[a] may be a Reg or Deref?
        # ==> NO, home does not have Reg because they are replaced in the previous function
        # if isinstance(a, Variable):
        #     return home[a]
        # return a
        match a:
            case ByteReg(id):
                return a 
            case Variable(id):
                return home[a]
            case _:
                return super().assign_homes_arg(a, home)
            

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
        # replace all variable
        for s in ss:
            new_instrs.append(self.assign_homes_instr(s, home))
        return new_instrs

    
    
    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        live_after = self.uncover_live(pseudo_x86)
        graph = self.build_interference(pseudo_x86, live_after)
        #trace(graph.show().source)
        #trace("")
        return self.allocate_registers(pseudo_x86, graph) # allocate_registers will help assign_homes to finish the job
    
    
    ###########################################################################
    # Patch Instructions
    ###########################################################################
    def big_constant(self, c:arg) -> bool:
        # To check if an immediate is too big to store in a register
        # The size limit is not for Reg or Deref, it is for immediate
        return isinstance(c, Immediate) and (c.value > (2**32) or c.value < -2**32)
    
    def in_memory(self, a:arg) -> bool:
        # To check if this variable in memory
        return isinstance(a, Deref)
    
    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
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
                    return [mov_instr, op_instr]
                else:
                    return [i]
            case Instr("movq", [source, target]):
                if (target == source): # Not sure if it is comparable
                    return []
                else:
                    return [i]
            # Handle the 'cmpq' instruction
            case Instr('cmpq', [s,t]): # the second argu of cmpq must not be immediate
                if isinstance(t, Immediate): 
                    mov_instr = Instr('movq', [t, Reg('rax')])
                    cmp_instr = Instr('cmpq', [s,Reg('rax')])
                    return [mov_instr, cmp_instr]
                elif isinstance(s, Deref) and isinstance(t, Deref): # Two memory reference in 'cmpq'
                    mov_instr = Instr('movq', [t, Reg('rax')])
                    cmp_instr = Instr('cmpq', [s, Reg('rax')])
                    return [mov_instr, cmp_instr]
                else:
                    return [i]
                
            case Instr('movzbq', [s, t]):
                if isinstance(t, Reg):
                    return [i]
                else:  # Handle the case where the second argument of 'movzbq' is not a register
                    raise Exception("Second argument of 'movzbq must be a register'")

                
            case _:
                # add instration into list
                return [i]
    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        # YOUR CODE HERE
        res = []
        for s in ss:
            instr_res = self.patch_instr(s)
            # print(f"instr is {s}, patched instrs are {instr_res}")
            res += instr_res
        return res

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        # Based on Assignment 1's `patch_instructions`,
        # I need to remove useless movq instructions
        if isinstance(p.body, dict):
            patched_instrs = {}
            for label, instrs in p.body.items():
                patched_instrs[label] = self.patch_instrs(instrs)
        else:
            patched_instrs = self.patch_instrs(p.body)
        new_x86_program = X86Program(patched_instrs)
        # is there possible to remove a register and leave it not use?
        # if so, we may need to change the stack_space?
        new_x86_program.stack_space = p.stack_space
        new_x86_program.used_callee = p.used_callee
        return new_x86_program

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################



    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        # The problem is that how to know the size I need to allocate.
        # iterate on this program and 
        # If we have multiple functions (with labels)
        if isinstance(p.body, dict):
            new_body = {}
            for label, instrs in p.body.items():
                if label == 'main':
                # instructions for stack allocations
                    prelude = [
                        Instr("pushq", [Reg("rbp")]),
                        Instr("movq", [Reg("rsp"), Reg("rbp")]),
                        Instr("subq", [Immediate(p.stack_space), Reg("rsp")])
                    ]
                
                    # Jump to the start block after the prelude in 'main'
                    start_block_label = 'start'
                    jump_to_start = Jump(start_block_label)
                            
                    # instructions for restore stack allocations
                    conclusion = [
                        label_name(generate_name("conclusion")),  # Labeled block for conclusion
                        Instr("addq", Immediate(p.stack_space), Reg("rsp")),
                        # Instr("mov", ["%rbp", "%rsp"]), # is equal to addq if %rbp 's value is not changed
                        Instr("popq", [Reg("rbp")]),
                        Instr("retq", [])
                    ]
                    # Place the prelude, jump to start, and conclusion in main
                    new_body[label] = prelude + [jump_to_start] + instrs + conclusion       
                else:
                    # For other functions, keep the original instructions
                    new_body[label] = instrs   
                    
        else:  
            # If we have a single main function
            starting_offset = 8 * len(p.used_callee) - p.stack_space
            prelude = [
                Instr("pushq", [Reg("rbp")]),
                Instr("movq", [Reg("rsp"), Reg("rbp")]),
                Instr("subq", [Immediate(p.stack_space), Reg("rsp")])
            ]
            
            # Loop through the callee-saved registers to save them
            for reg in p.used_callee:
                prelude.append(Instr("movq", [Reg(reg), Deref("rbp", starting_offset)]))
                starting_offset -= 8

            # Reset starting offset for restoration of callee-saved registers
            starting_offset = 8 * len(p.used_callee) - p.stack_space

            # Loop through the callee-saved registers to restore them
            for reg in p.used_callee:
                conclusion.append(Instr("movq", [Deref("rbp", starting_offset), Reg(reg)]))
                starting_offset -= 8
            
            conclusion.extend(
                [
                label_name(generate_name("conclusion")),  # Labeled block for conclusion
                Instr("addq", [Immediate(p.stack_space), Reg("rsp")]),
                Instr("popq", [Reg("rbp")]),
                Instr("retq", [])
                ]
            )
            
            new_body = prelude + p.body + conclusion

        return X86Program(new_body)