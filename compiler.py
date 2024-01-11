import ast
from ast import *
from utils import *
from x86_ast import *
import functions
import typing
from typing import List, Dict
from var import Temporaries
from register_allocator import arg_registers, caller_save_for_alloc, \
    registers, callee_save_for_alloc
from graph import UndirectedAdjList
import type_check_Lfun
import type_check_Cfun
import interp_Lfun
import interp_Cfun

name_map = {}
class Compiler(functions.Functions):

    '''
    The first two resolve Array, not Tuple
    '''

    ###########################################################################
    # Type-based Resolution
    ###########################################################################

    def resolve_exp(self, e: expr) -> expr:
      match e:
        case ast.Lambda(params, body):
            return ast.Lambda(params, self.resolve_exp(body))
        case Call(Name('arity'), [func]):
            return Call(Name('arity', [self.resolve_exp(func)]))
        case _:
          return super().resolve_exp(e)

    
    def resolve_stmt(self, s: stmt) -> stmt:
        match s:
            case AnnAssign(target, annotation, value, simple):
                return AnnAssign(self.resolve_exp(target),
                                 annotation,
                                 self.resolve_exp(value),
                                 simple)
            case _:
                return super().resolve_stmt(s)
    
    ###########################################################################
    # Bounds Checking
    ###########################################################################

    def check_bounds_exp(self, e: expr) -> expr:
      match e:
        case ast.Lambda(params, body):
            return ast.Lambda(params, self.check_bounds_exp(body))
        case Call(Name('arity'), [func]):
            return Call(Name('arity'), [self.check_bounds_exp(func)])
        case _:
          return super().check_bounds_exp(e)
    
    def check_bounds_stmt(self, s: stmt) -> stmt:
        match s:
          case AnnAssign(target, annotation, value, simple):
              return [AnnAssign(self.check_bounds_exp(target),
                               annotation,
                               self.check_bounds_exp(value),
                               simple)]
          case _:
              return super().check_bounds_stmt(s)
            
    ############################################################################
    # Shrink
    ############################################################################
    def shrink_exp(self, e: expr) -> expr:
       match e:
            case ast.Lambda(params, body):
                return ast.Lambda(params, self.shrink_exp(body))
            case Call(Name('arity'), [func]):
                return Call(Name('arity'), [self.shrink_exp(func)])
            case _:
                return super().shrink_exp(e)
    
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case AnnAssign(target, annotation, value, simple): # AnnAssign(var, type, exp, 0)
                return AnnAssign(
                   self.shrink_exp(target),
                   annotation,
                   self.shrink_exp(value),
                   simple)
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
    # uniquify
    ############################################################################
    no_uniquify_functions = builtin_functions.copy()
    def uniquify_exp(self, e: expr, env: dict) -> expr:
        print(f"e is {e}, etype is {type(e)}")
        match e:
            case Name(id):
                # Replace the name with its unique version if it's in the map
                if id in env.keys():
                    # if variable already appears
                    new_id = env.get(id, id)
                elif id in self.no_uniquify_functions:
                    # some functions that do not need uniquify
                    env[id] = id
                    new_id = env.get(id, id)
                else:
                    # if it is a new variable
                    new_id = generate_name(id)
                    env[id] = new_id
                return Name(new_id, e.ctx)
            case FunRef(name, arity):
                # I think 'arity' already includes the id
                # How to update the arity?
                env[name] = generate_name(name)
                return FunRef(name, name_id)
            case Constant(value):
                return Constant(value)
            case Lambda(param, body):
                # Process lambda parameters and body
                new_param, new_env = self.uniquify_params(param, env, "lambda")
                new_body = self.uniquify_exp(body, new_env)
                return Lambda(new_param, new_body)
            case Call(func, args):
                # Process function call
                new_func = self.uniquify_exp(func, env)
                new_args = [self.uniquify_exp(arg, env) for arg in args]
                return Call(new_func, new_args)
            case UnaryOp(op, operand):
                return UnaryOp(op, self.uniquify_exp(operand, env))
            case BinOp(left, op, right):
                return BinOp(self.uniquify_exp(left, env),
                             op,
                             self.uniquify_exp(right, env))
            case Compare(left, ops, comparators):
                return Compare(self.uniquify_exp(left, env),
                               ops,
                               [self.uniquify_exp(s, env) for s in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.uniquify_exp(test, env),
                             self.uniquify_exp(body, env),
                             self.uniquify_exp(orelse, env))
            case ast.Tuple(elts, ctx):
                return ast.Tuple([self.uniquify_exp(s, env) for s in elts],
                                 ctx)
            case Subscript(value, slices, ctx):
                return Subscript(self.uniquify_exp(value, env),
                                 slices,
                                 ctx)
            case _:
                # Add more cases as needed for other expression types
                raise Exception(f"unhandle expr {e}")

    def uniquify_params(self, params, env: dict, func_type: str) -> tuple:
        # lambda and function defination has different params
        new_env = env.copy()
        if func_type == 'lambda':
            new_params = []
            for name in params:
                new_name = generate_name(name)
                new_env[name] = new_name
                new_params.append(new_name)
        if func_type == 'function_def':
            # Tuple-based parameters
            new_params = []
            for name, type_ in params:
                new_name = generate_name(name)
                new_env[name] = new_name
                new_params.append((new_name, type_))
        return new_params, new_env
        
    # Do we need to check if the parameters are free or not?
    def uniquify_arg(self, arg: ast.arg, env: dict) -> ast.arg:
        if arg is None:
            return None
        new_name = generate_name(arg.arg)
        env[arg.arg] = new_name
        return ast.arg(new_name, arg.annotation)

    def uniquify_def(self, d: FunctionDef, env) -> ast.FunctionDef:
        match d:
            case ast.FunctionDef(name, params, body, decorator_list, returns, type_comment):
                # Process function definition
                new_params, new_env = self.uniquify_params(params, env, "function_def")
                new_body = [self.uniquify_stmt(stmt, new_env) for stmt in body]
                return ast.FunctionDef(name, new_params, new_body, decorator_list, returns, type_comment)
    
    def uniquify_stmt(self, s: ast.stmt, env: dict) -> ast.stmt:
        print(f"stmt is {s}, stmt type is {type(s)}")
        match s:
            case ast.AnnAssign(target, annotation, value, simple):
                # Process annotated assignment
                new_target = self.uniquify_exp(target, env)
                new_value = self.uniquify_exp(value, env)
                return ast.AnnAssign(new_target, annotation, new_value, simple)
            case ast.If(test, body, orelse):
                # Process if statement
                new_test = self.uniquify_exp(test, env)
                new_body = [self.uniquify_stmt(stmt, env) for stmt in body]
                new_orelse = [self.uniquify_stmt(stmt, env) for stmt in orelse]
                return ast.If(new_test, new_body, new_orelse)
            case ast.Return(value):
                # Process return statement
                new_value = self.uniquify_exp(value, env) if value is not None else None
                return ast.Return(new_value)
            case ast.Expr(value):
                # Process expression statement
                new_value = self.uniquify_exp(value, env)
                return ast.Expr(new_value)
            case While(test, body, orelse):
                return While(self.uniquify_exp(test, env),
                             [self.uniquify_stmt(s, env) for s in body],
                             [self.uniquify_stmt(s, env) for s in orelse])
            case Assign(targets, value):
                return Assign([self.uniquify_exp(e, env) for e in targets],
                              self.uniquify_exp(value, env))
            case _:
                # Add more cases as needed for other statement types
                raise Exception(f"Unhandle stmt {s}")
           
    def uniquify(self, p: ast.Module) -> ast.Module:
        res = []
        for d in p.body:
            self.no_uniquify_functions.add(d.name) # first scan: add definations
        for d in p.body:
            env = {}
            res.append(self.uniquify_def(d, env))
        return Module(res)

    
    ############################################################################
    # Reveal Functions
    ############################################################################

    # change all Name('func') to FunRef('func', arity)
    def reveal_funs_exp(self, e: expr, funs) -> expr:
        match e:
            case ast.Lambda(params, body):
                return ast.Lambda(params, self.reveal_funs_exp(body, funs))
            case _:
                return super().reveal_funs_exp(e, funs)
      
    def reveal_funs_stmt(self, s: stmt, funs) -> stmt:
        match s:
            case ast.AnnAssign(target, annotation, value, simple):
                return ast.AnnAssign(self.reveal_funs_exp(target, funs),
                                     annotation,
                                     self.reveal_funs_exp(value, funs),
                                     simple)
            case _:
                return super().reveal_funs_stmt(s, funs)
        
    def reveal_functions(self, p: Module) -> Module:
        match p:
          case Module(body):
            funs = dict()
            for s in body:
              if isinstance(s, FunctionDef):
                funs[s.name] = len(s.args)
            return Module([self.reveal_funs_stmt(s, funs) for s in body])
    
    ############################################################################
    # Convert Assignments
    ############################################################################
    def free_variables(self, e: expr, bound_vars: set) -> set:
        match e:
            case Name(id):
                if id not in bound_vars:
                    return {id}
                else:
                    return set()
            case Constant(Value):
                return set()
            case FunRef(name, arity):
                return set()
            case Call(func, args):
                func_free_vars = self.free_variables(func, bound_vars)
                args_free_vars = set().union(*(self.free_variables(arg, bound_vars) for arg in args))
                return func_free_vars.union(args_free_vars)
            case BinOp(left, op, right):
                left_free_vars = self.free_variables(left, bound_vars)
                right_free_vars = self.free_variables(right, bound_vars)
                return left_free_vars.union(right_free_vars)
            case UnaryOp(op, operand):
                return self.free_variables(operand, bound_vars)
            case ast.Tuple(elts, ctx):
                return set().union()(*(self.free_variables(el, bound_vars) for el in elts))
            case ast.Subscript(value, slice, ctx):
                return self.free_variables(value)
            case Lambda(args, body):
                new_bound_vars = bound_vars.union({arg.arg for arg in args.args})
                return self.free_variables(body, new_bound_vars)
            case _:
                # Recursively handle other expression types (e.g., Call, BinOp, etc.)
                # Collect free variables from subexpressions and return their union
                pass

    def free_in_lambda(self, l: ast.Lambda) -> set:
        return self.free_variables(l)

    def assigned_vars_stmt(self, s: stmt) -> set:
        match s:
            case Assign(targets, _):
                return {t.id for t in targets if isinstance(t, Name)}
            case _:
                # Recursively handle other statement types
                # For compound statements (e.g., If, For), collect assigned vars from substatements
                return set()
    
    def transform_exp(self, e: expr, boxed_vars: set) -> expr:
        match e:
            case Name(id) if id in boxed_vars:
                # Replace read from boxed variable with tuple read
                return Subscript(Name(id), Constant(0), Load())
            case Name(id):
                return Name(id)
            case Lambda(args, body):
                # Transform lambda body
                return Lambda(args, self.transform_exp(body, boxed_vars))
            case Constant(value):
                return Constant(value)
            case FunRef(name, arity):
                return FunRef(name, arity)
            case BinOp(left, op, right):
                return BinOp(self.transform_exp(left, boxed_vars),
                             op,
                             self.transform_exp(right, boxed_vars))
            case UnaryOp(op, operand):
                return UnaryOp(op, self.transform_exp(operand, boxed_vars))
            case Call(func, args):
                return Call(self.transform_exp(func, boxed_vars), [self.transform_exp(a, boxed_vars) for a in args])
            case Compare(left, ops, comparators):
                return Compare(self.transform_exp(left, boxed_vars),
                               ops,
                               [self.transform_exp(s, boxed_vars) for s in comparators])
            case IfExp(test, body, orelse):
                return IfExp(self.transform_exp(test, boxed_vars),
                             self.transform_exp(body, boxed_vars),
                             self.transform_exp(orelse, boxed_vars))
            case Tuple(elts, ctx):
                return Tuple([self.transform_exp(el, boxed_vars) for el in elts], ctx)
            case Subscript(value, slice, ctx):
                return Subscript(self.transform_exp(value, boxed_vars), slice, ctx)
            case _:
                raise Exception("Unhandle transform, ",e)
    def transform_stmt(self, s: stmt, boxed_vars: set) -> stmt:
        match s:
            case AnnAssign(target, annotations, value, simple):
                return AnnAssign(self.transform_exp(target, boxed_vars),
                                 annotations,
                                 self.transform_exp(value, boxed_vars),
                                 simple)
            case Assign(targets, value):
                # Transform the right-hand side of the assignment
                new_value = self.transform_exp(value, boxed_vars)
                new_targets = [self.transform_exp(t, boxed_vars) for t in targets]
                return Assign(new_targets, new_value)
            case Return(value):
                # Transform the return value
                return Return(self.transform_exp(value, boxed_vars))
            case Expr(value):
                # Transform the expression
                return Expr(self.transform_exp(value, boxed_vars))
            case If(test, body, orelse):
                # Transform the test expression and the bodies of the if and else branches
                new_test = self.transform_exp(test, boxed_vars)
                new_body = [self.transform_stmt(stmt, boxed_vars) for stmt in body]
                new_orelse = [self.transform_stmt(stmt, boxed_vars) for stmt in orelse]
                return If(new_test, new_body, new_orelse)
            case While(test, body, orelse):
                new_test = self.transform_exp(test, boxed_vars)
                new_body = [self.transform_stmt(stmt, boxed_vars) for stmt in body]
                new_orelse = [self.transform_stmt(stmt, boxed_vars) for stmt in orelse]
                return While(new_test, new_body, new_orelse)
            case _:
                # Recursively handle other statement types
                # For compound statements (e.g., For, While), transform substatements
                raise Exception("Unhandle transform, ", s)


    def convert_assignments_def(self, d: FunctionDef) -> FunctionDef:
        # Step 1: Identify variables to box
        free_vars = set()  # Collect free variables in lambdas
        assigned_vars = set()  # Collect assigned variables in the function
        for s in d.body:
            if isinstance(s, ast.Lambda):
                free_vars.update(self.free_in_lambda(s))
            elif isinstance(s, ast.Assign):
                assigned_vars.update(self.assigned_vars_stmt(s))
        vars_to_box = free_vars.intersection(assigned_vars)

        # Step 2: Transform the FunctionDef
        new_body = []
        if vars_to_box:
            # Initialize the tuple for boxed variables
            tuple_init = Assign([Name("env")], Tuple([Name("uninitialized(var)") for _ in vars_to_box], Load()))
            new_body.append(tuple_init)

        for stmt in d.body:
            new_body.append(self.transform_stmt(stmt, vars_to_box))

        return FunctionDef(d.name, d.args, new_body, d.decorator_list, d.returns, d.type_comment)
    
    def convert_assignments(self, p: Module) -> Module:
        res = []
        match p:
            case Module(body):
                for s in body:
                    if isinstance(s, FunctionDef):
                        res.append(self.convert_assignments_def(s))
        return Module(res)

    ############################################################################
    # Convert to closures
    ############################################################################
    function_return_type = {}
    # 1. transform lambda
    def create_top_level_function(self, name: str, lambda_expr: Lambda, free_vars: List[str]) -> FunctionDef:
        # Create parameters for the new function
        # The first parameter is the closure ('clos') with a generic type (e.g., Bottom)
        closure_param = ("clos", Bottom())

        # The new function parameters include the closure and the original lambda parameters
        func_params = [closure_param] + lambda_expr.args

        # Create the function body, extracting free variables from the closure
        new_body = []
        for i, fv in enumerate(free_vars):
            new_body.append(Assign([Name(fv)], Subscript(Name("clos"), Constant(i + 1), Load())))

        # Add the body of the lambda
        new_body.append(lambda_expr.body)

        # Create the new function definition
        return FunctionDef(name, func_params, new_body, [], lambda_expr.body, None)

    def transform_lambda_to_closure(self, lambda_expr: Lambda, free_vars: List[str]) -> Closure:
        # Generate a unique name for the new top-level function
        func_name = generate_name("lambda")

        # Create a new top-level function corresponding to the lambda
        new_func_def = self.create_top_level_function(func_name, lambda_expr, free_vars)

        # Add the new function to the module's body
        self.module_body.append(new_func_def)

        # Return a Closure node
        Clos = Closure(len(lambda_expr.args), [FunRef(func_name, len(lambda_expr.args))] + free_vars)
        Clos.has_type = TupleType([FunctionType([TupleType([])]+[e.has_type for e in lambda_expr.args]), lambda_expr.body])
        return Clos

    # 2. transform function call
    def transform_function_call(self, call_expr: Call) -> Expr:
        # Extract the function from the closure
        func = Subscript(call_expr.func, Constant(0), Load())

        # Pass the closure as the first argument
        new_args = [call_expr.func] + call_expr.args

        return Call(func, new_args)
    
    # 3. transform function reference
    def transform_fun_ref(self, fun_ref: FunRef) -> Closure:
        Clos = Closure(fun_ref.arity, [FunRef(fun_ref.name, fun_ref.arity)])
        print("The closure is, ", Clos, Clos.args)
        Clos.has_type = TupleType([FunctionType([TupleType([])], self.function_return_type[fun_ref.name])])
        return Clos
    def is_closure(self, func_name: str) -> bool:
        # Check if the function name corresponds to a closure
        # This method should check if func_name is in the list of functions that have been converted to closures
        if func_name in self.no_uniquify_functions:
            return False
        return True
    
    # closure conversion
    def convert_exp(self, e: expr, free_vars: List[str] = None) -> expr:
        match e:
            case Constant(Value):
                return Constant(Value)
            case Lambda(args, body):
                # Transform Lambda into Closure
                lambda_free_vars = self.free_variables(body, set(arg for arg in args))
                return self.transform_lambda_to_closure(e, list(lambda_free_vars))
            case Call(func, args):
                # Transform function call
                # Check if the function is a closure
                if isinstance(func, Name) and self.is_closure(func.id):
                    new_func = self.convert_exp(func, free_vars)
                    new_args = [Name("clos")] + [self.convert_exp(arg, free_vars) for arg in args]
                    return Call(Subscript(new_func, Constant(0), Load()), new_args)
                else:
                    new_func = self.convert_exp(func, free_vars)
                    new_args = [self.convert_exp(arg, free_vars) for arg in args]
                    return Call(new_func, new_args)
            case FunRef(name, arity):
                # Convert FunRef to Closure
                return self.transform_fun_ref(e)
            case Name(id):
                if free_vars and id in free_vars:
                    # Access free variable from closure
                    return Subscript(Name("clos"), Constant(free_vars.index(id) + 1), Load())
                else:
                    return e
            case BinOp(left, op, right):
                # Transform binary operations
                new_left = self.convert_exp(left, free_vars)
                new_right = self.convert_exp(right, free_vars)
                return BinOp(new_left, op, new_right)
            case UnaryOp(op, opreand):
                return UnaryOp(op, self.convert_exp(opreand, free_vars))
            case Compare(left, ops, comparators):
                return Compare(self.convert_exp(left, free_vars),
                               ops,
                               [self.convert_exp(c, free_vars) for c in comparators])
            case IfExp(test, body, orelse):
                # Transform conditional expressions
                new_test = self.convert_exp(test, free_vars)
                new_body = self.convert_exp(body, free_vars)
                new_orelse = self.convert_exp(orelse, free_vars)
                return IfExp(new_test, new_body, new_orelse)
            case Tuple(elts, ctx):
                return Tuple([self.convert_exp(el, free_vars) for el in elts], ctx)
            case Subscript(value, slice, ctx):
                return Subscript(self.convert_exp(value, free_vars), slice, ctx)
            case _:
                # Recursively handle other expression types
                # For compound expressions (e.g., ListComp, UnaryOp), transform subexpressions
                raise Exception("Unhandled expression type:", e)

    
    def convert_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(value):
                return Expr(self.convert_exp(value))
            case Assign(targets, value):
                new_value = self.convert_exp(value)
                return Assign(targets, new_value)
            case AnnAssign(target, annotation, value, simple):
                # Translate AnnAssign to a regular Assign, discarding the annotation
                new_value = self.convert_exp(value) if value is not None else None
                return Assign([target], new_value)
            case Return(value):
                new_value = self.convert_exp(value) if value is not None else None
                return Return(new_value)
            case If(test, body, orelse):
                new_test = self.convert_exp(test)
                new_body = [self.convert_stmt(stmt) for stmt in body]
                new_orelse = [self.convert_stmt(stmt) for stmt in orelse]
                return If(new_test, new_body, new_orelse)
            case While(test, body, orelse):
                new_test = self.convert_exp(test)
                new_body = [self.convert_stmt(stmt) for stmt in body]
                new_orelse = [self.convert_stmt(stmt) for stmt in orelse]
                return While(new_test, new_body, new_orelse)
            case _:
                raise Exception("Unhandled statement type:", s)


    def convert_function_def(self, d: FunctionDef) -> FunctionDef:
        new_body = [self.convert_stmt(stmt) for stmt in d.body]
        return FunctionDef(d.name, d.args, new_body, d.decorator_list, d.returns, d.type_comment)
    
    def convert_to_closures(self, p: Module) -> Module:
        self.module_body = []
        # first iteration
        for s in p.body:
            self.function_return_type[s.name] = s.returns
        for s in p.body:
            if isinstance(s, FunctionDef):
                new_func_def = self.convert_function_def(s)
                self.module_body.append(new_func_def)
            else:
                self.module_body.append(s)
        for p in self.module_body:
            print("p is, ", p)
        return Module(self.module_body)

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

    def vars_arg(self, a: arg) -> set[location]:
        match a:
            case FunRef(id, arity): # todo: delete? changed to Global
                return {}
            case _:
                return super().vars_arg(a)
            
    def read_vars(self, i: instr) -> set[location]:
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

    def write_vars(self, i: instr) -> set[location]:
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
                        live_after: Dict[instr, set[location]]):
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

    def collect_locals_arg(self, a: arg) -> set[location]:
        match a:
            case FunRef(id, arity):
                return set()
            case _:
                return super().collect_locals_arg(a)
            
    def collect_locals_instr(self, i: instr) -> set[location]:
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