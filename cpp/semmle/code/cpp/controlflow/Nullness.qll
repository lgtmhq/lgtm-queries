// Copyright 2017 Semmle Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under
// the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

import default
import DefinitionsAndUses
import Options

/**
 * A C/C++ literal whose value is considered null.
 */
abstract class NullValue extends Expr
{
}

/**
 * A C/C++ literal whose value is zero.
 */
class Zero extends NullValue
{
  Zero() { this.(Literal).getValue() = "0" }
}

cached
predicate nullCheckExpr(Expr checkExpr, Variable var)
{
  exists(LocalScopeVariable v, AnalysedExpr expr | var = v and checkExpr = expr and (
    exists(NotExpr notexpr, AnalysedExpr child |
      expr = notexpr and notexpr.getOperand() = child and validCheckExpr(child, v))
    or
    exists(EQExpr eq, AnalysedExpr child, NullValue zero, int i |
      expr = eq and eq.getChild(i) = child and
      validCheckExpr(child, v) and eq.getChild(1-i) = zero)
    or
    exists(NEExpr neq, AnalysedExpr child, NullValue zero, int i |
      expr = neq and neq.getChild(i) = child and
      nullCheckExpr(child, v) and neq.getChild(1-i) = zero)
    or
    exists(LogicalAndExpr op, AnalysedExpr child |
      expr = op and op.getRightOperand() = child and
      nullCheckExpr(child, v))
    or
    exists(AssignExpr assign, AnalysedExpr child |
      expr = assign and assign.getRValue() = child and
      nullCheckExpr(child, v) and not expr.isDef(v))
    or
    exists(FunctionCall fc, AnalysedExpr child |
      expr = fc and
      fc.getTarget().hasQualifiedName("__builtin_expect") and
      fc.getArgument(0) = child and nullCheckExpr(child, v))
  ))
}

cached
predicate validCheckExpr(Expr checkExpr, Variable var)
{
  exists(AnalysedExpr expr, LocalScopeVariable v | expr = checkExpr and v = var and (
    expr.isUse(v)
    or
    expr.isDef(v)
    or
    exists(NotExpr notexpr, AnalysedExpr child |
      expr = notexpr and notexpr.getOperand() = child and nullCheckExpr(child, v))
    or
    exists(EQExpr eq, AnalysedExpr child, NullValue zero, int i |
      expr = eq and eq.getChild(i) = child and
      nullCheckExpr(child, v) and eq.getChild(1-i) = zero)
    or
    exists(NEExpr neq, AnalysedExpr child, NullValue zero, int i |
      expr = neq and neq.getChild(i) = child and
      validCheckExpr(child, v) and neq.getChild(1-i) = zero)
    or
    exists(LogicalAndExpr op, AnalysedExpr child |
      expr = op and op.getRightOperand() = child and
      validCheckExpr(child, v))
    or
    exists(AssignExpr assign, AnalysedExpr child |
      expr = assign and assign.getRValue() = child and
      validCheckExpr(child, v) and not expr.isDef(v))
    or
    exists(FunctionCall fc, AnalysedExpr child |
      expr = fc and
      fc.getTarget().hasQualifiedName("__builtin_expect") and
      fc.getArgument(0) = child and validCheckExpr(child, v))
  ))
}

class AnalysedExpr extends Expr {

  predicate isNullCheck(LocalScopeVariable v) {
    nullCheckExpr(this, v)
  }

  predicate isValidCheck(LocalScopeVariable v) {
    validCheckExpr(this, v)
  }

  ControlFlowNode getNullSuccessor(LocalScopeVariable v)
  {
    (this.isNullCheck(v) and result = this.getATrueSuccessor())
    or
    (this.isValidCheck(v) and result = this.getAFalseSuccessor())
  }

  ControlFlowNode getNonNullSuccessor(LocalScopeVariable v)
  {
    (this.isNullCheck(v) and result = this.getAFalseSuccessor())
    or
    (this.isValidCheck(v) and result = this.getATrueSuccessor())
  }

  ControlFlowNode getValidSuccessor(LocalScopeVariable v)
  {
    (this.isValidCheck(v) and result = this.getATrueSuccessor())
    or
    (this.isNullCheck(v) and result = this.getAFalseSuccessor())
  }

  predicate isUse(LocalScopeVariable v)
  {
    this.inCondition() and
    this = v.getAnAccess()
  }

  predicate isDef(LocalScopeVariable v)
  {
    this.inCondition() and
    ((Assignment) this).getLValue() = v.getAnAccess()
  }

  predicate inCondition()
  {
    this.isCondition() or
    ((AnalysedExpr) this.getParent()).inCondition()
  }
}

cached
predicate checkedNull(Variable var, ControlFlowNode node)
{
  exists(LocalScopeVariable v, ControlFlowNode n | v = var and n = node and (
    exists(AnalysedExpr e |
      e.getNullSuccessor(v) = n)
    or
    exists(ControlFlowNode pred |
      pred = n.getAPredecessor() and
      not(((AnalysedExpr) pred).isDef(v)) and
      checkedNull(v, pred))))
}

cached
predicate checkedValid(Variable var, ControlFlowNode node)
{
  exists(LocalScopeVariable v, ControlFlowNode n | v = var and n = node and (
    exists(AnalysedExpr e |
      e.getValidSuccessor(v) = n)
    or
    exists(ControlFlowNode pred |
      pred = n.getAPredecessor() and
      not(((AnalysedExpr) pred).isDef(v)) and
      checkedValid(v, pred))))
}

predicate nullValue(Expr val)
{
  val instanceof NullValue
  or
  callMayReturnNull(val)
  or
  nullValue(val.(Assignment).getRValue())
}

predicate nullInit(Variable v, ControlFlowNode n)
{
  exists(Initializer init |
    init = n and nullValue(init.getExpr()) and
    v.getInitializer() = init)
  or
  exists(AssignExpr assign |
    assign = n and nullValue(assign.getRValue()) and
    assign.getLValue() = v.getAnAccess())
}

predicate callMayReturnNull(Call c)
{
  if overrideReturnsNull(c) then
    returnsNull(c)
  else
    mayReturnNull(((FunctionCall) c).getTarget())
}

predicate mayReturnNull(Function f)
{
  f.getQualifiedName() = "malloc"
  or
  f.getQualifiedName() = "calloc"
  or
//  f.getQualifiedName() = "strchr"
//  or
//  f.getQualifiedName() = "strstr"
//  or
  exists(ReturnStmt ret |
    nullValue(ret.getExpr()) and
    ret.getEnclosingFunction() = f)
  or
  exists(ReturnStmt ret, Expr returned, ControlFlowNode init, LocalScopeVariable v |
    ret.getExpr() = returned and
    nullInit(v, init) and
    definitionUsePair(v, init, returned) and
    not(checkedValid(v, returned)) and
    ret.getEnclosingFunction() = f)
}
