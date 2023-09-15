import compiler
from graph import UndirectedAdjList
from typing import List, Tuple, Set, Dict
from ast import *
from x86_ast import *
from typing import Set, Dict, Tuple

# Skeleton code for the chapter on Register Allocation

class Compiler(compiler.Compiler):

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def read_vars(self, i: instr) -> Set[location]:
        # YOUR CODE HERE
        pass

    def write_vars(self, i: instr) -> Set[location]:
        # YOUR CODE HERE
        pass

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        # YOUR CODE HERE
        pass
    
    def build_move(self, p:X86Program) -> UndirectedAdjList:
        # THIS IS FOR CHALLANGE, should build a move graph to move bias
        # this should be called in `allocate_registers`
        pass
    
    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(self, graph: UndirectedAdjList,
                    variables: Set[location]) -> Tuple[Dict[location, int], Set[location]]:
        # YOUR CODE HERE
        pass

    def allocate_registers(self, p: X86Program,
                           graph: UndirectedAdjList) -> X86Program:
        # YOUR CODE HERE
        pass

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
                liveness = self.uncover_live()
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
                pseudo_x86.stack_space = align(8 * len(variables), 16)
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
        new_x86_program.stack_space = p.stack_space
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
            # I do not think we need to consider callee-register now
            # even if we do need to handle this, this should be at `patch_instructions` func
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
