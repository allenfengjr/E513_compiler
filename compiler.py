import ast
from ast import *
from utils import *
from x86_ast import *
from typing import List, Tuple, Set, Dict
from graph import UndirectedAdjList
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
                    temp = Name(generate_name("temp_call"))
                    return (temp, func_temp + arg_temp + [(temp, Call(new_func, new_args, []))])
                else: 
                    return Call(new_func, new_args, []), func_temp + arg_temp
            case IfExp(test, body, orelse):
                # all three does not need atomic
                # print(f"do test rco, test is {test}")
                rco_test, tmp_test = self.rco_exp(test, False)
                # print(f"do body rco, body is {body}")
                rco_body, tmp_body = self.rco_exp(body, False)
                # print(f"do orelse rco, orelse is {orelse}")
                rco_orelse, tmp_orelse = self.rco_exp(orelse, False)
                # make_begin will create stmt^* for IfExp, it will return a Begin
                new_body = make_begin(tmp_body, rco_body)
                # print(f"the new body is {new_body}")
                new_orelse = make_begin(tmp_orelse, rco_orelse)
                if need_atomic:
                    # If need atomic, then I must return an atom
                    tmp = Name(generate_name("temp_if"))
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
                    tmp = Name(generate_name("temp_cmp"))
                    return (tmp, tmp_test + [(tmp, Compare(rco_left, cmp, rco_comparators))] + tmp_comparators)
                else:
                    return Compare(rco_left, cmp, rco_comparators), tmp_test + tmp_comparators
            case Begin(body, result):
                # print("I do have begin")
                new_result, tmp_res = self.rco_exp(result, False)
                return Begin(body, new_result), tmp_res
            case _:
                print(e.__class__)
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
            # print(f"the stmts are, {[i.__class__ for i in rco_statements]}, value is {rco_statements}")
        #Create a new Module with the transformed statements.
        transformed_program = Module(transformed_statements)
        return transformed_program
    

    ############################################################################
    # Explicate Control
    ############################################################################
    def create_block(stmts, basic_blocks):
        match stmts:
            case [Goto(l)]:
                return stmts
            case _:
                label = label_name(generate_name('block'))
                basic_blocks[label] = stmts
                return [Goto(label)]
            
    def explicate_effect(self, e, cont, basic_blocks) -> stmt:
        match e:
            case IfExp(test, body, orelse):
                ...
            case Call(func, args):
                ...
            case Begin(body, result):
                ...
            case _:
                ...
    
    def explicate_assign(self, rhs, lhs, cont, basic_blocks):
        match rhs:
            case IfExp(test, body, orelse):
                ...
            case Begin(body, result):
                ...
            case _:
                return [Assign([lhs], rhs)] + cont
    
    def explicate_pred(self, cnd, thn, els, basic_blocks):
        match cnd:
            case Compare(left, [op], [right]):
                goto_thn = self.create_block(thn, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                return [If(cnd, goto_thn, goto_els)]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                ...
            case IfExp(test, body, orelse):
                ...
            case Begin(body, result):
                ...
            case _:
                return [If(Compare(cnd, [Eq()], [Constant(False)]),
                        self.create_block(els, basic_blocks),
                        self.create_block(thn, basic_blocks))]
    
    def explicate_stmt(self, s, cont, basic_blocks):
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                return self.explicate_pred(test, body, orelse)
            case _:
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
            case _:
                raise Exception('error in write_vars, unexpected: ' + repr(i))
    
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

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        match p:
            case X86Program(body):
                live_before = {}
                live_after = {}
                live_before_succ = set([])
                for i in reversed(body):
                    self.uncover_live_instr(i, live_before_succ, live_before,
                                            live_after)
                    live_before_succ = live_before[i]

                trace("uncover live:")
                self.trace_live(p, live_before, live_after)
                return live_after

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        match p:
            case X86Program(body):
                G = UndirectedAdjList()
                for i in body:
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
            case _:
                for v in live_after[i]:
                    for d in self.write_vars(i):
                        if v != d:
                            graph.add_edge(d, v)
    
    def build_move(self, p:X86Program) -> UndirectedAdjList:
        # THIS IS FOR CHALLANGE, should build a move graph to move bias
        # this should be called in `allocate_registers`
        # YOUR CODE HERE
        move_graph = UndirectedAdjList()
        for i in p.body:
            if isinstance(i, Instr) and i.instr == 'movq': #Connect all the vertax in movq instruction
                move_graph.add_edge(i.source(), i.target())
        return move_graph
        pass
    
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
        Q = PriorityQueue(compare)
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
                if u.id not in registers:
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

    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        match p:
            case X86Program(body):
                variables = self.collect_locals_instrs(body)
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
    
    # def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
    #     # YOUR CODE HERE
    #     # Use color_graph to obtain variable-to-color mapping
    #     variables = set()
    #     for instr in p.body:
    #         variables.update(self.read_vars(instr) | self.write_vars(instr))
    #     color_assignment = self.color_graph(graph, variables)

    #     # Define the correspondence between the colors and Registers
    #     register_mapping = {
    #         0: 'rcx', 1: 'rdx', 2: 'rsi', 3: 'rdi',
    #         4: 'r8', 5: 'r9', 6: 'r10', 7: 'rbx',
    #         8: 'r12', 9: 'r13', 10: 'r14'
    #     }
    #     # Record callee-saved register
    #     p.callee_saved_register = set()
        
    #     for instr in p.body:
    #         match instr:
    #             case Callq("print_int", 1):
    #                 pass
    #             case Callq("input_int", 0):
    #                 pass
    #             case Instr(ins, args):
    #                 # For other instructions, replace variables with registers
    #                 '''
                    
                    
    #                 for arg in [arg for arg in [source, target] if arg is not None]:
    #                     if isinstance(arg, Variable):
    #                         color_set = color_assignment.get(arg.id, set())
    #                         if color_set:
    #                             color = min(color_set)  # choose the smallest color
    #                             register_name = register_mapping.get(color)
    #                             if register_name:
    #                                 arg.id = register_name  # Replace the variable with the corresponding register
    #                                 if self.callee_saved_reg(register_name):
    #                                     p.callee_saved_register.add(register_name)
    #                 '''
    #                 for i, a in enumerate(args):
    #                     print("i is", i, "a is ", a)
    #                     if isinstance(a, Variable):
    #                         color_set = color_assignment.get(a.id, set())
    #                         print("color set is, ", color_set)
    #                         color = min(color_set)
    #                         print("color is, ", color)

    #                         register_name = register_mapping.get(color)
    #                         print("register name is, ", register_name)

    #                         print(f"here we replace {args[i]} into {register_name}")
    #                         args[i] = register_name
    #                         print(f"now args[i] is {args[i]}")
    #                         if self.callee_saved_reg(register_name):
    #                             p.callee_saved_register.add(register_name)

    #     print(f"Program instructions are {p.body}")
    #     return p

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
        # replace all variable
        for s in ss:
            new_instrs.append(self.assign_homes_instr(s, home))
        return new_instrs

    # def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
    #     match pseudo_x86:
    #         case X86Program(body):
    #             # first, uncover_live, return Dict[instr, Set[location]]
    #             liveness = self.uncover_live(pseudo_x86)
    #             # second, build_interference, return UndirectedAdjList
    #             interference_graph = self.build_interference(pseudo_x86, liveness)
    #             # allocate_registers, return X86Program(which replace some variable into register)
    #             p = self.allocate_registers(pseudo_x86, interference_graph)
    #             # assign the new home on new body
    #             variables = self.collect_locals_instrs(p.body)
    #             home = {}
    #             for i, x in enumerate(variables):
    #                 home[x] = self.gen_stack_access(i)
    #             new_body = self.assign_homes_instrs(p.body, home)
    #             new_pseudo_x86 = X86Program(new_body)
    #             new_pseudo_x86.stack_space = align(8 * (len(variables) + len(pseudo_x86.used_callee)), 16)
    #             new_pseudo_x86.used_callee = pseudo_x86.used_callee
    #             print(f"CALLEE SAVED REGISTER and VARIABLE SIZE are, {new_pseudo_x86.used_callee}, {variables}")
    #             return new_pseudo_x86
    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        live_after = self.uncover_live(pseudo_x86)
        graph = self.build_interference(pseudo_x86, live_after)
        #trace(graph.show().source)
        #trace("")
        return self.allocate_registers(pseudo_x86, graph)
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
            conclusion = []

            # Reset starting offset for restoration of callee-saved registers
            starting_offset = 8 * len(p.used_callee) - p.stack_space

            # Loop through the callee-saved registers to restore them
            for reg in p.used_callee:
                conclusion.append(Instr("movq", [Deref("rbp", starting_offset), Reg(reg)]))
                starting_offset -= 8
            
            conclusion.extend(
                [
                Instr("addq", [Immediate(p.stack_space), Reg("rsp")]),
                Instr("popq", [Reg("rbp")]),
                Instr("retq", [])
                ]
            )
            
            new_body = prelude + p.body + conclusion

        return X86Program(new_body)