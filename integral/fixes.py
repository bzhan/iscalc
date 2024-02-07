"""Symbol table"""

from copy import deepcopy
from typing import List

from integral import expr, latex
from integral.expr import Type, Expr, Integral, Fun, Summation, Product, Matrix, Symbol, SkolemFunc, FunType, Deriv, \
    IndefiniteIntegral, EvalAt, Unknown, BoolType, IntType, RealType, Limit

VAR_INFO, OP_INFO, FUN_INFO, BINDING_VAR_INFO, SYMBOL_INFO = range(5)


def mapping_symbol_type_2_str(symbol_type):
    if symbol_type == VAR_INFO:
        return 'var'
    elif symbol_type == FUN_INFO:
        return 'fun'
    elif symbol_type == BINDING_VAR_INFO:
        return 'binding'
    elif symbol_type == SYMBOL_INFO:
        return 'symbol'
    elif symbol_type == OP_INFO:
        return 'op'
    else:
        raise NotImplementedError


class Info:
    def __init__(self):
        self.type = None

    def is_var(self):
        return self.symbol_type == VAR_INFO

    def is_func(self):
        return self.symbol_type == FUN_INFO

    def is_op(self):
        return self.symbol_type == OP_INFO

    def is_binding_var(self):
        return self.symbol_type == BINDING_VAR_INFO

    def is_symbol(self):
        return self.symbol_type == SYMBOL_INFO

    def get_type(self) -> expr.Type:
        return self.type

    def set_type(self, t: type):
        self.type = t

    def get_args_name(self):
        assert self.is_func() or self.is_op()
        return self.args_name

    def get_args_type(self):
        assert self.is_func() or self.is_op()
        return self.get_type().get_args_type()

    def get_return_type(self):
        assert self.is_func() or self.is_op()
        return self.get_type().get_return_type()

    @staticmethod
    def get_instance(symbol_type, type, args_name: List[str] = None):
        if symbol_type in ('var', VAR_INFO):
            return VarInfo(type)
        elif symbol_type in ('binding', BINDING_VAR_INFO):
            return BindingVarInfo(type)
        elif symbol_type in ('op', OP_INFO):
            return OpInfo(args_name, type)
        elif symbol_type in ('fun', FUN_INFO):
            return FuncInfo(args_name, type)
        elif symbol_type in ('symbol', SYMBOL_INFO):
            return SymbolInfo(type)
        else:
            print(symbol_type)
            raise NotImplementedError

    def export(self):
        res = dict()
        if hasattr(self, 'type') and self.type is not None:
            res['type'] = str(self.type) 
        if hasattr(self, 'symbol_type') and self.symbol_type is not None:
            res['symbol_type'] = mapping_symbol_type_2_str(self.symbol_type)
        if hasattr(self, 'args_name') and self.args_name is not None:
            res['args_name'] = self.args_name
        return res


class VarInfo(Info):
    def __init__(self, type):
        self.symbol_type = VAR_INFO  # is_var or is_func or is_operator
        self.type = type

    def __hash__(self):
        return hash((self.symbol_type, self.type))

    def __str__(self):
        return "var_info: " + str(self.get_type())

    def __eq__(self, other):
        return isinstance(other, VarInfo) and other.type == self.type


class SymbolInfo(Info):
    def __init__(self, type):
        self.symbol_type = SYMBOL_INFO  # is_var or is_func or is_operator
        self.type = type

    def __hash__(self):
        return hash((self.symbol_type, self.type))

    def __str__(self):
        return "symbol_info: " + str(self.get_type())

    def __eq__(self, other):
        return isinstance(other, SymbolInfo) and other.type == self.type


class FuncInfo(Info):
    def __init__(self, args_name, type):
        self.symbol_type = FUN_INFO
        self.type = type
        self.args_name = args_name  # term infomation

    def __eq__(self, other):
        return isinstance(other, FuncInfo) and \
               other.type == self.type and \
               self.args_name == other.args_name

    def __hash__(self):
        return hash((self.symbol_type, *self.args_name, self.type))


class OpInfo(Info):
    def __init__(self, args_name, type):
        self.symbol_type = OP_INFO
        self.type = type
        self.args_name = args_name

    def __hash__(self):
        return hash((self.symbol_type, self.type, *self.args_name))

    def __eq__(self, other):
        return isinstance(other, OpInfo) and \
               other.type == self.type and \
               self.args_name == other.args_name


class BindingVarInfo(Info):
    def __init__(self, type):
        self.symbol_type = BINDING_VAR_INFO
        self.type = type

    def __hash__(self):
        return hash((self.symbol_type, self.type))

    def __eq__(self, other):
        return isinstance(other, BindingVarInfo) and \
               other.type == self.type

    def __str__(self):
        return "binding_info: " + str(self.get_type())


class Fixes(dict):
    """
    Symbol table:
      one name could have multiple types
    """

    def __str__(self):
        res = "Fixes:\n"
        for key in self:
            res = res + key + "\n"
            for info in self[key]:
                res = res + "    " + str(info) + "\n"
        return res

    def __setitem__(self, key, value):
        if key not in self:
            dict.__setitem__(self, key, set())
        if isinstance(value, Info):
            self[key].add(value)
        elif isinstance(value, set):
            dict.__setitem__(self, key, value)
        else:
            raise NotImplementedError

    def empty(self):
        return len(self.items()) == 0

    def export(self):
        res = list()
        for name in self:
            if len(self[name]) == 1:
                info = list(self[name])[0]
                type = info.get_type()
                if type in (IntType, RealType) or expr.is_matrix_type(type):
                    tmp = info.export()
                    tmp['latex_type'] = latex.convert_type(name, type)
                    res.append([name, tmp])
            else:
                raise ValueError("one variable has multiple types")
        return res

    def update(self, other: 'Fixes'):
        """
        extend into a bigger one based on other fixes.
        """
        res = deepcopy(self)
        for name in other:
            if name not in self:
                res[name] = other[name]
            else:
                res[name] = res[name].union(other[name])
        return res

    def change(self, old_expr, new_expr):
        """
        remove or add new symbol according the change of symbols.
        """
        f1 = fixes_from_expr(old_expr)
        f2 = fixes_from_expr(new_expr)
        sym1 = set(f1.keys())
        sym2 = set(f2.keys())
        remove = sym1.difference(sym2)
        add = sym2.difference(sym1)
        for name in remove:
            if name in self:
                self[name] = self[name].difference(f1[name])
                if self[name] == set():
                    del self[name]
        for name in add:
            if name in self:
                self[name] = self[name].union(f2[name])
            else:
                self[name] = f2[name]

    def subst(self, var: str, e: Expr):
        res = Fixes()

        def rec(t: Type, s: Expr):
            if t.name == 'tensor':
                args = [t.args[0]]
                for arg in t.args[1:]:
                    args.append(arg.subst(var, s))
                return expr.TensorType(*args)
            elif t.name == 'fun':
                args = []
                for arg in t.args:
                    args.append(rec(arg, s))
                return expr.FunType(*args)
            else:
                return t

        for key in self:
            for info in self[key]:
                tmp = deepcopy(info)
                tmp.set_type(rec(info.get_type(), e))
                res[key] = tmp
        return res


def fixes_from_type(t: Type) -> 'Fixes':
    res = Fixes()
    if t in (RealType, IntType, BoolType, Unknown):
        pass
    elif expr.is_fun_type(t):
        for arg in t.args:
            try:
                res = res.update(fixes_from_type(arg))
            except:
                print(t)
                raise NotImplementedError
    elif expr.is_matrix_type(t):
        res = res.update(fixes_from_type(t.eleType))
        res = res.update(fixes_from_expr(t.row))
        res = res.update(fixes_from_expr(t.col))
    else:
        print(str(t))
        raise NotImplementedError

    return res


def fixes_from_expr(e: Expr) -> 'Fixes':
    bd = Fixes()

    def rec(e: Expr, bd: Fixes):
        res = Fixes()
        if expr.is_inf(e) or expr.is_const(e):
            pass
        elif expr.is_var(e):
            res = res.update(fixes_from_type(e.type))
            if e.name in bd:
                res[e.name] = Info.get_instance(BINDING_VAR_INFO, e.type)
            else:
                res[e.name] = Info.get_instance(VAR_INFO, e.type)
        elif expr.is_symbol(e):
            e: Symbol
            res = res.update(fixes_from_type(e.type))
            res[e.name] = Info.get_instance(SYMBOL_INFO, e.type)
        elif expr.is_skolem_func(e):
            e: SkolemFunc
            func_type = FunType(*[arg.type for arg in e.dependent_vars], RealType)
            args_name = [str(arg) for arg in e.dependent_vars]
            res = res.update(fixes_from_type(func_type))
            res[e.name] = Info.get_instance(FUN_INFO, func_type, args_name)
            for arg in e.dependent_vars:
                res = res.update(rec(arg, bd))
        elif expr.is_op(e):
            # # TODO: OP_INFO
            for arg in e.args:
                res = res.update(rec(arg, bd))
        elif expr.is_fun(e):
            # e : Fun
            # res[e.func_name] = Info.get_instance(FUN_INFO, e.func_type, [str(arg) for arg in e.args])
            for arg in e.args:
                res = res.update(rec(arg, bd))
        elif expr.is_matrix(e):
            e: Matrix
            for row in e.data:
                for ele in row:
                    res = res.update(rec(ele, bd))
        elif expr.is_deriv(e):
            e: Deriv
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.var_type)
            res[e.var] = bd_info
            bd[e.var] = bd_info
            res = res.update(rec(e.body, bd))
        elif expr.is_indefinite_integral(e):
            e: IndefiniteIntegral
            res = res.update(fixes_from_type(e.var_type))
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.var_type)
            res[e.var] = bd_info
            bd[e.var] = bd_info
            # TODO : skolem args
            res.update(rec(e.body, bd))
        elif expr.is_evalat(e):
            e: EvalAt
            res = res.update(fixes_from_type(e.var_type))
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.var_type)
            res[e.var] = bd_info
            bd[e.var] = bd_info
            res = res.update(rec(e.lower, bd))
            res = res.update(rec(e.upper, bd))
            res = res.update(rec(e.body, bd))
        elif expr.is_integral(e):
            e: Integral
            res = res.update(fixes_from_type(e.var_type))
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.var_type)
            res[e.var] = bd_info
            bd[e.var] = bd_info
            res = res.update(rec(e.lower, bd))
            res = res.update(rec(e.upper, bd))
            res = res.update(rec(e.body, bd))
        elif expr.is_limit(e):
            e: Limit
            res = res.update(fixes_from_type(e.var_type))
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.var_type)
            res[e.var] = bd_info
            bd[e.var] = bd_info
            res = res.update(rec(e.lim, bd))
            res = res.update(rec(e.body, bd))
        elif expr.is_summation(e):
            e: Summation
            res = res.update(fixes_from_type(e.index_var_type))
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.index_var_type)
            res[e.index_var] = bd_info
            res[e.index_var] = bd_info
            res = res.update(rec(e.lower, bd))
            res = res.update(rec(e.upper, bd))
            res = res.update(rec(e.body, bd))
        elif expr.is_product(e):
            e: Product
            res = res.update(fixes_from_type(e.index_var_type))
            bd_info = Info.get_instance(BINDING_VAR_INFO, e.index_var_type)
            res[e.index_var] = bd_info
            res[e.index_var] = bd_info
            res = res.update(rec(e.lower, bd))
            res = res.update(rec(e.upper, bd))
            res = res.update(rec(e.body, bd))
        else:
            print(e)
            raise NotImplementedError
        return res

    return rec(e, bd)
