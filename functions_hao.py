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

class Functions(tuples.Tuples):
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
            case FunctionDef(name, args, body, _, returns, _):
                self.function_arity_map[name] = len(args.args)
                new_body = [self.reveal_function_stmt(stmt) for stmt in body]
                return FunctionDef(name, args, new_body, None, returns, None)
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
            case FunctionDef(name, args, body, _, returns, _):
                if len(args.args) > 6:
                    # Update arguments
                    new_args = args.args[:5]
                    rest_args = args.args[5:]
                    tuple_arg = arg('tup', TupleType([a.annotation for a in rest_args]))
                    new_args.append(tuple_arg)

                    # Update body
                    new_body = [self.limit_function_stmt_in_body(stmt, rest_args) for stmt in body]
                    return FunctionDef(name, arguments(new_args, args.vararg, args.kwonlyargs, args.kw_defaults, args.kwarg, args.defaults), new_body, None, returns, None)
                else:
                    new_body = [self.limit_function_stmt(stmt) for stmt in body]
                    return FunctionDef(name, args, new_body, None, returns, None)
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
    # Limit Functions
    ###########################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> tuple[expr, Temporaries]:
        match e:
            case FunRef(name, arity):
                if need_atomic:
                    tmp = Name(self.generate_name('tmp'))
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
                    tmp = Name(self.generate_name('tmp'))
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