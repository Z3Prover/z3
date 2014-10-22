import ctypes, z3core

class Z3Exception(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return str(self.value)

class ContextObj(ctypes.c_void_p):
  def __init__(self, context): self._as_parameter_ = context
  def from_param(obj): return obj

class Config(ctypes.c_void_p):
  def __init__(self, config): self._as_parameter_ = config
  def from_param(obj): return obj

class Symbol(ctypes.c_void_p):
  def __init__(self, symbol): self._as_parameter_ = symbol
  def from_param(obj): return obj

class Sort(ctypes.c_void_p):
  def __init__(self, sort): self._as_parameter_ = sort
  def from_param(obj): return obj

class FuncDecl(ctypes.c_void_p):
  def __init__(self, decl): self._as_parameter_ = decl
  def from_param(obj): return obj

class Ast(ctypes.c_void_p):
  def __init__(self, ast): self._as_parameter_ = ast
  def from_param(obj): return obj

class Pattern(ctypes.c_void_p):
  def __init__(self, pattern): self._as_parameter_ = pattern
  def from_param(obj): return obj

class Model(ctypes.c_void_p):
  def __init__(self, model): self._as_parameter_ = model
  def from_param(obj): return obj

class Literals(ctypes.c_void_p):
  def __init__(self, literals): self._as_parameter_ = literals
  def from_param(obj): return obj

class Constructor(ctypes.c_void_p):
  def __init__(self, constructor): self._as_parameter_ = constructor
  def from_param(obj): return obj

class ConstructorList(ctypes.c_void_p):
  def __init__(self, constructor_list): self._as_parameter_ = constructor_list
  def from_param(obj): return obj

class GoalObj(ctypes.c_void_p):
  def __init__(self, goal): self._as_parameter_ = goal
  def from_param(obj): return obj

class TacticObj(ctypes.c_void_p):
  def __init__(self, tactic): self._as_parameter_ = tactic
  def from_param(obj): return obj

class ProbeObj(ctypes.c_void_p):
  def __init__(self, probe): self._as_parameter_ = probe
  def from_param(obj): return obj

class ApplyResultObj(ctypes.c_void_p):
  def __init__(self, obj): self._as_parameter_ = obj
  def from_param(obj): return obj

class StatsObj(ctypes.c_void_p):
  def __init__(self, statistics): self._as_parameter_ = statistics
  def from_param(obj): return obj

class SolverObj(ctypes.c_void_p):
  def __init__(self, solver): self._as_parameter_ = solver
  def from_param(obj): return obj

class FixedpointObj(ctypes.c_void_p):
  def __init__(self, fixedpoint): self._as_parameter_ = fixedpoint
  def from_param(obj): return obj

class ModelObj(ctypes.c_void_p):
  def __init__(self, model): self._as_parameter_ = model
  def from_param(obj): return obj

class AstVectorObj(ctypes.c_void_p):
  def __init__(self, vector): self._as_parameter_ = vector
  def from_param(obj): return obj

class AstMapObj(ctypes.c_void_p):
  def __init__(self, ast_map): self._as_parameter_ = ast_map
  def from_param(obj): return obj

class Params(ctypes.c_void_p):
  def __init__(self, params): self._as_parameter_ = params
  def from_param(obj): return obj

class ParamDescrs(ctypes.c_void_p):
  def __init__(self, paramdescrs): self._as_parameter_ = paramdescrs
  def from_param(obj): return obj

class FuncInterpObj(ctypes.c_void_p):
  def __init__(self, f): self._as_parameter_ = f
  def from_param(obj): return obj

class FuncEntryObj(ctypes.c_void_p):
  def __init__(self, e): self._as_parameter_ = e
  def from_param(obj): return obj

class RCFNumObj(ctypes.c_void_p):
  def __init__(self, e): self._as_parameter_ = e
  def from_param(obj): return obj

