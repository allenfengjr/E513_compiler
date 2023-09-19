import ast
from ast import *
from utils import *
from x86_ast import *
from typing import List, Tuple, Set, Dict
from graph import UndirectedAdjList
from queue import *
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

    def read_vars(self, i: instr) -> Set[location]:
        # YOUR CODE HERE
        # how to include addq, subq, movq?
        if isinstance(i, Instr):
            read_set = set()
            for arg in [Instr.source, Instr.target]:
                if isinstance(arg, Reg):
                    read_set.add(arg.id)
                elif isinstance(arg, Variable):
                    read_set.add(arg.id)
        # what about negq?
        # elif isinstance(i, negq): 
            return read_set

        # Callq should include all the arguments-passing registers in read_set
        elif isinstance(i, Callq):
            read_set = set()
            argument_passing_registers = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
            for arg in i.func:
                if isinstance(arg, Reg) in argument_passing_registers:
                    read_set.add(arg.id)
                elif isinstance(arg, Variable):
                    read_set.add(arg.id)    
            return read_set
        pass

    def write_vars(self, i: instr) -> Set[location]:
        # YOUR CODE HERE
        #Only focus on writeen variables
        if isinstance(i, Instr):
            write_set = set()
            for arg in [Instr.source, Instr.target]:
                if isinstance(arg, Reg):
                    write_set.add(arg.id)
            return write_set

        elif isinstance(i, Callq):
        # Handle write set for callq instruction (caller-saved registers)
            caller_saved_registers = ['rax', 'rcx', 'rdx', 'rsi', 'rdi', 'r8', 'r9', 'r10', 'r11']
            return set(caller_saved_registers)
        pass

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        # YOUR CODE HERE
        live_after_sets = {}  # Dictionary to store live-after sets for each instruction
        for i in p.body:
            live_after_sets[i] = set()

        # Iterate through the instructions in reverse order   
        for i in reversed(p.body):
            read_set = self.read_vars(i)
            write_set = self.write_vars(i)

        # calculate live-after sets
        live_after_i = (live_after_sets[i]-write_set) | read_set

        live_after_sets[i] = live_after_i
        return live_after_sets
        pass

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        # YOUR CODE HERE
        interference_graph = UndirectedAdjList()

        for i in p.body:
            write_set = self.write_vars(i)
            
            if isinstance(i, Instr) and i.instr == 'movq':
                #rule1: movq instruction
                for d in write_set:
                    for v in live_after[i]:
                        if v!=d and v!=i.source() and d!=i.target():
                            interference_graph.add_edge(d, v)
            else:
                #rule2: other instructions
                for d in write_set:
                    for v in live_after[i]:
                        if v!=d:
                            interference_graph.add_edge(d, v)

        return interference_graph
        pass
    
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
    def callee_saved_reg(self, variable: location) -> bool:
        callee_saved = {"rbx", "r12", "r13", "r14"}
        if isinstance(variable, Reg) and variable.id in callee_saved:
            return True
        return False
    
    # Returns the coloring and the set of spilled variables.
    def color_graph(self, graph: UndirectedAdjList,
                    variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        # YOUR CODE HERE
        color_assignment = {} # Mapping of variables to colors
        saturation_degree = {} # Saturation degree of each vertex
        vertex_queue = PriorityQueue() # Priority queue of vertices

        # Initialize the saturation degree of each vertex and add them to the queue
        for v in graph.vertices():
            saturation_degree[v] = 0
            vertex_queue.put((saturation_degree[v], v))

        while not vertex_queue.empty():
            _, u = vertex_queue.get()
            available_colors = set(range(0, 11)) # Set of available colors, other 5 are not used for register allocation
            # check the neiborhood of u, and remove the color from available colors
            for v in graph.adjacent(u):
                if v in color_assignment:
                    available_colors.discard(color_assignment[v])
                else:
                    saturation_degree[v] += 1
            if available_colors:
                color = min(available_colors) # choose the smallest color
                color_assignment[u] = color

        return color_assignment
        pass

    def allocate_registers(self, p: X86Program, graph: UndirectedAdjList) -> X86Program:
        # YOUR CODE HERE
        # Use color_graph to obtain variable-to-color mapping
        variables = set()
        for instr in p.body:
            variables.update(self.read_vars(instr) | self.write_vars(instr))
        color_assignment = self.color_graph(graph, variables)

        # Define the correspondence between the colors and Registers
        register_mapping = {
            0: 'rcx', 1: 'rdx', 2: 'rsi', 3: 'rdi',
            4: 'r8', 5: 'r9', 6: 'r10', 7: 'rbx',
            8: 'r12', 9: 'r13', 10: 'r14'
        }
        # Record callee-saved register
        p.callee_saved_register = set()
        
        for instr in p.body:
            if isinstance(instr, Callq):
                # Handle Callq instruction separately
                for i, arg in enumerate(instr.func.args):
                    if isinstance(arg, Variable):
                        color_set = color_assignment.get(arg.id, set())
                        if color_set:
                            color = min(color_set)  # choose the smallest color
                            register_name = register_mapping.get(color)
                            if register_name:
                                instr.func.args[i] = Reg(register_name)  # Replace the variable with the corresponding register
                                if self.callee_saved_reg(register_name):
                                    p.callee_saved_register.add(register_name)
            else:
                # For other instructions, replace variables with registers
                for arg in [arg for arg in [instr.source(), instr.target()] if arg is not None]:
                    if isinstance(arg, Variable):
                        color_set = color_assignment.get(arg.id, set())
                        if color_set:
                            color = min(color_set)  # choose the smallest color
                            register_name = register_mapping.get(color)
                            if register_name:
                                arg.id = register_name  # Replace the variable with the corresponding register
                                if self.callee_saved_reg(register_name):
                                    p.callee_saved_register.add(register_name)
        return p

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

    def assign_homes(self, pseudo_x86: X86Program) -> X86Program:
        match pseudo_x86:
            case X86Program(body):
                # first, uncover_live, return Dict[instr, Set[location]]
                liveness = self.uncover_live(pseudo_x86)
                # second, build_interference, return UndirectedAdjList
                interference_graph = self.build_interference(pseudo_x86, liveness)
                # allocate_registers, return X86Program(which replace some variable into register)
                pseudo_x86 = self.allocate_registers(pseudo_x86, interference_graph)
                # assign the new home on new body
                body = pseudo_x86.body
                variables = self.collect_locals_instrs(body)
                home = {}
                for i, x in enumerate(variables):
                    home[x] = self.gen_stack_access(i)
                body = self.assign_homes_instrs(body, home)
                pseudo_x86 = X86Program(body)
                pseudo_x86.stack_space = align(8 * (len(variables) + len(pseudo_x86.callee_saved_register)), 16)
                return pseudo_x86

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
            print(f"instr is {s}, patched instrs are {instr_res}")
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
        new_x86_program.callee_saved_register = p.callee_saved_register
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
            starting_offset = 8 * len(p.callee_saved_register) - p.stack_space
            prelude = [
                Instr("pushq", [Reg("rbp")]),
                Instr("movq", [Reg("rsp"), Reg("rbp")]),
                Instr("subq", [Immediate(p.stack_space), Reg("rsp")])
            ]
            # Loop through the callee-saved registers to save them
            for reg in p.callee_saved_register:
                prelude.append(Instr("movq", [Reg(reg), Deref("rbp", starting_offset)]))
                starting_offset -= 8
            conclusion = []

            # Reset starting offset for restoration of callee-saved registers
            starting_offset = 8 * len(p.callee_saved_register) - p.stack_space

            # Loop through the callee-saved registers to restore them
            for reg in p.callee_saved_register:
                conclusion.append(Instr("movq", [Deref("rbp", starting_offset), Reg(reg)]))
                starting_offset -= 8
            
            conclusion.extend[
                Instr("addq", [Immediate(p.stack_space), Reg("rsp")]),
                Instr("popq", [Reg("rbp")]),
                Instr("retq", [])
            ]
            
            new_body = prelude + p.body + conclusion

        return X86Program(new_body)
